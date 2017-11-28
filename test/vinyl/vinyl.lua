#!/usr/bin/env tarantool

box.cfg {
    listen            = os.getenv("LISTEN"),
    memtx_memory      = 512 * 1024 * 1024,
    memtx_max_tuple_size = 4 * 1024 * 1024,
    rows_per_wal      = 1000000,
    vinyl_read_threads = 2,
    vinyl_write_threads = 3,
    vinyl_memory = 512 * 1024 * 1024,
    vinyl_range_size = 1024 * 64,
    vinyl_page_size = 1024,
    vinyl_run_count_per_level = 1,
    vinyl_run_size_ratio = 2,
    vinyl_cache = 0, -- 10kB
    vinyl_max_tuple_size = 1024 * 1024 * 6,
}

function box_info_sort(data)
    if type(data)~='table' then
        return data
    end
    local keys = {}
    for k in pairs(data) do
        table.insert(keys, k)
    end
    table.sort(keys)
    local result = {}
    for _,k in pairs(keys) do
        local v = data[k]
        table.insert(result, {[k] = box_info_sort(v) })
    end
    return result
end

require('console').listen(os.getenv('ADMIN'))
