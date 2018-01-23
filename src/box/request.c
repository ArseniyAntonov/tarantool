/*
 * Copyright 2010-2018, Tarantool AUTHORS, please see AUTHORS file.
 *
 * Redistribution and use in source and binary forms, with or
 * without modification, are permitted provided that the following
 * conditions are met:
 *
 * 1. Redistributions of source code must retain the above
 *    copyright notice, this list of conditions and the
 *    following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials
 *    provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY <COPYRIGHT HOLDER> ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
 * <COPYRIGHT HOLDER> OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
 * BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */
#include "request.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <msgpuck.h>
#include <small/region.h>

#include "fiber.h"
#include "space.h"
#include "index.h"
#include "sequence.h"
#include "key_def.h"
#include "tuple.h"
#include "tuple_compare.h"
#include "tuple_update.h"
#include "txn.h"
#include "xrow.h"
#include "iproto_constants.h"

void
request_rebind_to_primary_key(struct request *request, struct space *space,
			      struct tuple *found_tuple)
{
	struct index *pk = space_index(space, 0);
	assert(pk != NULL);
	uint32_t key_len;
	char *key = tuple_extract_key(found_tuple, pk->def->key_def, &key_len);
	assert(key != NULL);
	request->key = key;
	request->key_end = key + key_len;
	request->index_id = 0;
	/* Clear the *body* to ensure it's rebuilt at commit. */
	request->header = NULL;
}

int
request_handle_sequence(struct request *request, struct space *space)
{
	struct sequence *seq = space->sequence;

	assert(seq != NULL);
	assert(request->type == IPROTO_INSERT ||
	       request->type == IPROTO_REPLACE);

	/*
	 * An automatically generated sequence inherits
	 * privileges of the space it is used with.
	 */
	if (!seq->is_generated &&
	    access_check_sequence(seq) != 0)
		return -1;

	struct index *pk = space_index(space, 0);
	if (unlikely(pk == NULL))
		return 0;

	/*
	 * Look up the first field of the primary key.
	 */
	const char *data = request->tuple;
	const char *data_end = request->tuple_end;
	int len = mp_decode_array(&data);
	int fieldno = pk->def->key_def->parts[0].fieldno;
	if (unlikely(len < fieldno + 1))
		return 0;

	const char *key = data;
	if (unlikely(fieldno > 0)) {
		do {
			mp_next(&key);
		} while (--fieldno > 0);
	}

	int64_t value;
	if (mp_typeof(*key) == MP_NIL) {
		/*
		 * If the first field of the primary key is nil,
		 * this is an auto increment request and we need
		 * to replace the nil with the next value generated
		 * by the space sequence.
		 */
		if (unlikely(sequence_next(seq, &value) != 0))
			return -1;

		const char *key_end = key;
		mp_decode_nil(&key_end);

		size_t buf_size = (request->tuple_end - request->tuple) +
						mp_sizeof_uint(UINT64_MAX);
		char *tuple = region_alloc(&fiber()->gc, buf_size);
		if (tuple == NULL)
			return -1;
		char *tuple_end = mp_encode_array(tuple, len);

		if (unlikely(key != data)) {
			memcpy(tuple_end, data, key - data);
			tuple_end += key - data;
		}

		if (value >= 0)
			tuple_end = mp_encode_uint(tuple_end, value);
		else
			tuple_end = mp_encode_int(tuple_end, value);

		memcpy(tuple_end, key_end, data_end - key_end);
		tuple_end += data_end - key_end;

		assert(tuple_end <= tuple + buf_size);

		request->tuple = tuple;
		request->tuple_end = tuple_end;
	} else {
		/*
		 * If the first field is not nil, update the space
		 * sequence with its value, to make sure that an
		 * auto increment request never tries to insert a
		 * value that is already in the space. Note, this
		 * code is also invoked on final recovery to restore
		 * the sequence value from WAL.
		 */
		if (likely(mp_read_int64(&key, &value) == 0))
			return sequence_update(seq, value);
	}
	return 0;
}

/**
 * Given old and new tuples, initialize the corresponding
 * request to be written to WAL.
 */
static int
request_create_from_tuple(struct request *request, struct space *space,
			  struct tuple *old_tuple, struct tuple *new_tuple)
{
	memset(request, 0, sizeof(*request));
	request->space_id = space->def->id;
	if (old_tuple == new_tuple) {
		/*
		 * Old and new tuples are the same,
		 * turn this request into no-op.
		 */
		request->type = IPROTO_NOP;
		return 0;
	}
	if (new_tuple == NULL) {
		uint32_t size, key_size;
		const char *data = tuple_data_range(old_tuple, &size);
		request->key = tuple_extract_key_raw(data, data + size,
				space->index[0]->def->key_def, &key_size);
		if (request->key == NULL)
			return -1;
		request->key_end = request->key + key_size;
		request->type = IPROTO_DELETE;
	} else {
		uint32_t size;
		const char *data = tuple_data_range(new_tuple, &size);
		char *buf = region_alloc(&fiber()->gc, size);
		if (buf == NULL)
			return -1;
		memcpy(buf, data, size);
		request->tuple = buf;
		request->tuple_end = buf + size;
		request->type = IPROTO_REPLACE;
	}
	return 0;
}

int
request_before_replace(struct request *request, struct space *space,
		       struct txn *txn)
{
	if (space->index_count == 0) {
		/* Empty space, nothing to do. */
		return 0;
	}

	struct region *gc = &fiber()->gc;
	enum iproto_type type = request->type;
	struct index *pk = space->index[0];

	const char *key;
	uint32_t part_count;
	struct index *index;

	/*
	 * Lookup the old tuple.
	 */
	if (type == IPROTO_UPDATE || type == IPROTO_DELETE) {
		index = index_find_unique(space, request->index_id);
		if (index == NULL)
			return -1;
		key = request->key;
		part_count = mp_decode_array(&key);
		if (exact_key_validate(index->def->key_def,
				       key, part_count) != 0)
			return -1;
	} else if (type == IPROTO_INSERT || type == IPROTO_REPLACE ||
		   type == IPROTO_UPSERT) {
		index = pk;
		key = tuple_extract_key_raw(request->tuple, request->tuple_end,
					    index->def->key_def, NULL);
		if (key == NULL)
			return -1;
		part_count = mp_decode_array(&key);
	} else {
		/* Unknown request type, nothing to do. */
		return 0;
	}

	struct tuple *old_tuple;
	if (index_get(index, key, part_count, &old_tuple) != 0)
		return -1;

	/*
	 * Create the new tuple.
	 */
	uint32_t new_size, old_size;
	const char *new_data, *new_data_end;
	const char *old_data, *old_data_end;

	switch (request->type) {
	case IPROTO_INSERT:
	case IPROTO_REPLACE:
		new_data = request->tuple;
		new_data_end = request->tuple_end;
		break;
	case IPROTO_UPDATE:
		if (old_tuple == NULL) {
			/* Nothing to update. */
			return 0;
		}
		old_data = tuple_data_range(old_tuple, &old_size);
		old_data_end = old_data + old_size;
		new_data = tuple_update_execute(region_aligned_alloc_cb, gc,
					request->tuple, request->tuple_end,
					old_data, old_data_end, &new_size,
					request->index_base, NULL);
		if (new_data == NULL)
			return -1;
		new_data_end = new_data + new_size;
		break;
	case IPROTO_DELETE:
		if (old_tuple == NULL) {
			/* Nothing to delete. */
			return 0;
		}
		new_data = new_data_end = NULL;
		break;
	case IPROTO_UPSERT:
		if (old_tuple == NULL) {
			/*
			 * Turn UPSERT into INSERT, but still check
			 * provided operations.
			 */
			new_data = request->tuple;
			new_data_end = request->tuple_end;
			if (tuple_update_check_ops(region_aligned_alloc_cb, gc,
					request->ops, request->ops_end,
					request->index_base) != 0)
				return -1;
			break;
		}
		old_data = tuple_data_range(old_tuple, &old_size);
		old_data_end = old_data + old_size;
		new_data = tuple_upsert_execute(region_aligned_alloc_cb, gc,
					request->ops, request->ops_end,
					old_data, old_data_end, &new_size,
					request->index_base, false, NULL);
		new_data_end = new_data + new_size;
		break;
	default:
		unreachable();
	}

	struct tuple *new_tuple = NULL;
	if (new_data != NULL) {
		new_tuple = tuple_new(tuple_format_runtime,
				      new_data, new_data_end);
		if (new_tuple == NULL)
			return -1;
		tuple_ref(new_tuple);
	}

	assert(old_tuple != NULL || new_tuple != NULL);

	/*
	 * Execute all registered BEFORE triggers.
	 */
	struct txn_stmt *stmt = txn_current_stmt(txn);
	assert(stmt->old_tuple == NULL && stmt->new_tuple == NULL);
	stmt->old_tuple = old_tuple;
	stmt->new_tuple = new_tuple;

	int rc = trigger_run(&space->before_replace, txn);

	/*
	 * The trigger can't change the old tuple,
	 * but it may replace the new tuple.
	 */
	bool request_changed = (stmt->new_tuple != new_tuple);
	new_tuple = stmt->new_tuple;
	assert(stmt->old_tuple == old_tuple);
	stmt->old_tuple = NULL;
	stmt->new_tuple = NULL;

	if (rc != 0)
		goto out;

	/*
	 * We don't allow to change the value of the primary key
	 * in the same statement.
	 */
	if (request_changed && old_tuple != NULL && new_tuple != NULL &&
	    tuple_compare(old_tuple, new_tuple, pk->def->key_def) != 0) {
		diag_set(ClientError, ER_CANT_UPDATE_PRIMARY_KEY,
			 pk->def->name, space->def->name);
		rc = -1;
		goto out;
	}

	/*
	 * The trigger changed the resulting tuple.
	 * Fix the request to conform.
	 */
	if (request_changed) {
		rc = request_create_from_tuple(request, space,
					       old_tuple, new_tuple);
	}
out:
	if (new_tuple != NULL)
		tuple_unref(new_tuple);
	return rc;
}
