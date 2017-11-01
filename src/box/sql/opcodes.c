/* Automatically generated.  Do not edit */
/* See the tool/mkopcodec.tcl script for details. */
#include "sqliteInt.h"
#if !defined(SQLITE_OMIT_EXPLAIN) \
 || defined(VDBE_PROFILE) \
 || defined(SQLITE_DEBUG)
#if defined(SQLITE_ENABLE_EXPLAIN_COMMENTS) || defined(SQLITE_DEBUG)
# define OpHelp(X) "\0" X
#else
# define OpHelp(X)
#endif
const char *sqlite3OpcodeName(int i){
 static const char *const azName[] = {
    /*   0 */ "Savepoint"        OpHelp(""),
    /*   1 */ "AutoCommit"       OpHelp(""),
    /*   2 */ "Transaction"      OpHelp(""),
    /*   3 */ "SorterNext"       OpHelp(""),
    /*   4 */ "PrevIfOpen"       OpHelp(""),
    /*   5 */ "Or"               OpHelp("r[P3]=(r[P1] || r[P2])"),
    /*   6 */ "And"              OpHelp("r[P3]=(r[P1] && r[P2])"),
    /*   7 */ "Not"              OpHelp("r[P2]= !r[P1]"),
    /*   8 */ "NextIfOpen"       OpHelp(""),
    /*   9 */ "Prev"             OpHelp(""),
    /*  10 */ "Next"             OpHelp(""),
    /*  11 */ "Checkpoint"       OpHelp(""),
    /*  12 */ "JournalMode"      OpHelp(""),
    /*  13 */ "IsNull"           OpHelp("if r[P1]==NULL goto P2"),
    /*  14 */ "NotNull"          OpHelp("if r[P1]!=NULL goto P2"),
    /*  15 */ "Ne"               OpHelp("IF r[P3]!=r[P1]"),
    /*  16 */ "Eq"               OpHelp("IF r[P3]==r[P1]"),
    /*  17 */ "Gt"               OpHelp("IF r[P3]>r[P1]"),
    /*  18 */ "Le"               OpHelp("IF r[P3]<=r[P1]"),
    /*  19 */ "Lt"               OpHelp("IF r[P3]<r[P1]"),
    /*  20 */ "Ge"               OpHelp("IF r[P3]>=r[P1]"),
    /*  21 */ "ElseNotEq"        OpHelp(""),
    /*  22 */ "BitAnd"           OpHelp("r[P3]=r[P1]&r[P2]"),
    /*  23 */ "BitOr"            OpHelp("r[P3]=r[P1]|r[P2]"),
    /*  24 */ "ShiftLeft"        OpHelp("r[P3]=r[P2]<<r[P1]"),
    /*  25 */ "ShiftRight"       OpHelp("r[P3]=r[P2]>>r[P1]"),
    /*  26 */ "Add"              OpHelp("r[P3]=r[P1]+r[P2]"),
    /*  27 */ "Subtract"         OpHelp("r[P3]=r[P2]-r[P1]"),
    /*  28 */ "Multiply"         OpHelp("r[P3]=r[P1]*r[P2]"),
    /*  29 */ "Divide"           OpHelp("r[P3]=r[P2]/r[P1]"),
    /*  30 */ "Remainder"        OpHelp("r[P3]=r[P2]%r[P1]"),
    /*  31 */ "Concat"           OpHelp("r[P3]=r[P2]+r[P1]"),
    /*  32 */ "Goto"             OpHelp(""),
    /*  33 */ "BitNot"           OpHelp("r[P1]= ~r[P1]"),
    /*  34 */ "Gosub"            OpHelp(""),
    /*  35 */ "InitCoroutine"    OpHelp(""),
    /*  36 */ "Yield"            OpHelp(""),
    /*  37 */ "MustBeInt"        OpHelp(""),
    /*  38 */ "Jump"             OpHelp(""),
    /*  39 */ "Once"             OpHelp(""),
    /*  40 */ "If"               OpHelp(""),
    /*  41 */ "IfNot"            OpHelp(""),
    /*  42 */ "SeekLT"           OpHelp("key=r[P3@P4]"),
    /*  43 */ "SeekLE"           OpHelp("key=r[P3@P4]"),
    /*  44 */ "SeekGE"           OpHelp("key=r[P3@P4]"),
    /*  45 */ "SeekGT"           OpHelp("key=r[P3@P4]"),
    /*  46 */ "NoConflict"       OpHelp("key=r[P3@P4]"),
    /*  47 */ "NotFound"         OpHelp("key=r[P3@P4]"),
    /*  48 */ "Found"            OpHelp("key=r[P3@P4]"),
    /*  49 */ "SeekRowid"        OpHelp("intkey=r[P3]"),
    /*  50 */ "NotExists"        OpHelp("intkey=r[P3]"),
    /*  51 */ "Last"             OpHelp(""),
    /*  52 */ "SorterSort"       OpHelp(""),
    /*  53 */ "Sort"             OpHelp(""),
    /*  54 */ "Rewind"           OpHelp(""),
    /*  55 */ "IdxLE"            OpHelp("key=r[P3@P4]"),
    /*  56 */ "IdxGT"            OpHelp("key=r[P3@P4]"),
    /*  57 */ "IdxLT"            OpHelp("key=r[P3@P4]"),
    /*  58 */ "IdxGE"            OpHelp("key=r[P3@P4]"),
    /*  59 */ "RowSetRead"       OpHelp("r[P3]=rowset(P1)"),
    /*  60 */ "RowSetTest"       OpHelp("if r[P3] in rowset(P1) goto P2"),
    /*  61 */ "Program"          OpHelp(""),
    /*  62 */ "FkIfZero"         OpHelp("if fkctr[P1]==0 goto P2"),
    /*  63 */ "IfPos"            OpHelp("if r[P1]>0 then r[P1]-=P3, goto P2"),
    /*  64 */ "IfNotZero"        OpHelp("if r[P1]!=0 then r[P1]--, goto P2"),
    /*  65 */ "DecrJumpZero"     OpHelp("if (--r[P1])==0 goto P2"),
    /*  66 */ "Init"             OpHelp("Start at P2"),
    /*  67 */ "Return"           OpHelp(""),
    /*  68 */ "EndCoroutine"     OpHelp(""),
    /*  69 */ "HaltIfNull"       OpHelp("if r[P3]=null halt"),
    /*  70 */ "Halt"             OpHelp(""),
    /*  71 */ "Integer"          OpHelp("r[P2]=P1"),
    /*  72 */ "Bool"             OpHelp("r[P2]=P1"),
    /*  73 */ "Int64"            OpHelp("r[P2]=P4"),
    /*  74 */ "String"           OpHelp("r[P2]='P4' (len=P1)"),
    /*  75 */ "Null"             OpHelp("r[P2..P3]=NULL"),
    /*  76 */ "String8"          OpHelp("r[P2]='P4'"),
    /*  77 */ "SoftNull"         OpHelp("r[P1]=NULL"),
    /*  78 */ "Blob"             OpHelp("r[P2]=P4 (len=P1, subtype=P3)"),
    /*  79 */ "Variable"         OpHelp("r[P2]=parameter(P1,P4)"),
    /*  80 */ "Move"             OpHelp("r[P2@P3]=r[P1@P3]"),
    /*  81 */ "Copy"             OpHelp("r[P2@P3+1]=r[P1@P3+1]"),
    /*  82 */ "SCopy"            OpHelp("r[P2]=r[P1]"),
    /*  83 */ "IntCopy"          OpHelp("r[P2]=r[P1]"),
    /*  84 */ "ResultRow"        OpHelp("output=r[P1@P2]"),
    /*  85 */ "CollSeq"          OpHelp(""),
    /*  86 */ "Function0"        OpHelp("r[P3]=func(r[P2@P5])"),
    /*  87 */ "Function"         OpHelp("r[P3]=func(r[P2@P5])"),
    /*  88 */ "AddImm"           OpHelp("r[P1]=r[P1]+P2"),
    /*  89 */ "RealAffinity"     OpHelp(""),
    /*  90 */ "Cast"             OpHelp("affinity(r[P1])"),
    /*  91 */ "Permutation"      OpHelp(""),
    /*  92 */ "Compare"          OpHelp("r[P1@P3] <-> r[P2@P3]"),
    /*  93 */ "Column"           OpHelp("r[P3]=PX"),
    /*  94 */ "Affinity"         OpHelp("affinity(r[P1@P2])"),
    /*  95 */ "MakeRecord"       OpHelp("r[P3]=mkrec(r[P1@P2])"),
    /*  96 */ "Count"            OpHelp("r[P2]=count()"),
    /*  97 */ "TTransaction"     OpHelp(""),
    /*  98 */ "ReadCookie"       OpHelp(""),
    /*  99 */ "SetCookie"        OpHelp(""),
    /* 100 */ "ReopenIdx"        OpHelp("root=P2 iDb=P3"),
    /* 101 */ "OpenRead"         OpHelp("root=P2 iDb=P3"),
    /* 102 */ "OpenWrite"        OpHelp("root=P2 iDb=P3"),
    /* 103 */ "OpenAutoindex"    OpHelp("nColumn=P2"),
    /* 104 */ "OpenEphemeral"    OpHelp("nColumn=P2"),
    /* 105 */ "SorterOpen"       OpHelp(""),
    /* 106 */ "SequenceTest"     OpHelp("if (cursor[P1].ctr++) pc = P2"),
    /* 107 */ "OpenPseudo"       OpHelp("P3 columns in r[P2]"),
    /* 108 */ "Close"            OpHelp(""),
    /* 109 */ "ColumnsUsed"      OpHelp(""),
    /* 110 */ "Sequence"         OpHelp("r[P2]=cursor[P1].ctr++"),
    /* 111 */ "NextId"           OpHelp("r[P3]=get_max(space_index[P1]{Column[P2]})"),
    /* 112 */ "FCopy"            OpHelp("reg[P2@cur_frame]= reg[P1@root_frame(OPFLAG_SAME_FRAME)]"),
    /* 113 */ "NewRowid"         OpHelp("r[P2]=rowid"),
    /* 114 */ "Insert"           OpHelp("intkey=r[P3] data=r[P2]"),
    /* 115 */ "InsertInt"        OpHelp("intkey=P3 data=r[P2]"),
    /* 116 */ "Real"             OpHelp("r[P2]=P4"),
    /* 117 */ "Delete"           OpHelp(""),
    /* 118 */ "ResetCount"       OpHelp(""),
    /* 119 */ "SorterCompare"    OpHelp("if key(P1)!=trim(r[P3],P4) goto P2"),
    /* 120 */ "SorterData"       OpHelp("r[P2]=data"),
    /* 121 */ "RowData"          OpHelp("r[P2]=data"),
    /* 122 */ "Rowid"            OpHelp("r[P2]=rowid"),
    /* 123 */ "NullRow"          OpHelp(""),
    /* 124 */ "SorterInsert"     OpHelp("key=r[P2]"),
    /* 125 */ "IdxReplace"       OpHelp(""),
    /* 126 */ "IdxInsert"        OpHelp("key=r[P2]"),
    /* 127 */ "IdxDelete"        OpHelp("key=r[P2@P3]"),
    /* 128 */ "Seek"             OpHelp("Move P3 to P1.rowid"),
    /* 129 */ "IdxRowid"         OpHelp("r[P2]=rowid"),
    /* 130 */ "Destroy"          OpHelp(""),
    /* 131 */ "Clear"            OpHelp(""),
    /* 132 */ "ResetSorter"      OpHelp(""),
    /* 133 */ "CreateIndex"      OpHelp("r[P2]=root iDb=P1"),
    /* 134 */ "CreateTable"      OpHelp("r[P2]=root iDb=P1"),
    /* 135 */ "ParseSchema"      OpHelp(""),
    /* 136 */ "ParseSchema2"     OpHelp("rows=r[P1@P2] iDb=P3"),
    /* 137 */ "ParseSchema3"     OpHelp("name=r[P1] sql=r[P1+1] iDb=P2"),
    /* 138 */ "LoadAnalysis"     OpHelp(""),
    /* 139 */ "DropTable"        OpHelp(""),
    /* 140 */ "DropIndex"        OpHelp(""),
    /* 141 */ "DropTrigger"      OpHelp(""),
    /* 142 */ "IntegrityCk"      OpHelp(""),
    /* 143 */ "RowSetAdd"        OpHelp("rowset(P1)=r[P2]"),
    /* 144 */ "Param"            OpHelp(""),
    /* 145 */ "FkCounter"        OpHelp("fkctr[P1]+=P2"),
    /* 146 */ "MemMax"           OpHelp("r[P1]=max(r[P1],r[P2])"),
    /* 147 */ "OffsetLimit"      OpHelp("if r[P1]>0 then r[P2]=r[P1]+max(0,r[P3]) else r[P2]=(-1)"),
    /* 148 */ "AggStep0"         OpHelp("accum=r[P3] step(r[P2@P5])"),
    /* 149 */ "AggStep"          OpHelp("accum=r[P3] step(r[P2@P5])"),
    /* 150 */ "AggFinal"         OpHelp("accum=r[P1] N=P2"),
    /* 151 */ "Expire"           OpHelp(""),
    /* 152 */ "TableLock"        OpHelp("iDb=P1 root=P2 write=P3"),
    /* 153 */ "Pagecount"        OpHelp(""),
    /* 154 */ "MaxPgcnt"         OpHelp(""),
    /* 155 */ "CursorHint"       OpHelp(""),
    /* 156 */ "IncMaxid"         OpHelp(""),
    /* 157 */ "Noop"             OpHelp(""),
    /* 158 */ "Explain"          OpHelp(""),
  };
  return azName[i];
}
#endif
