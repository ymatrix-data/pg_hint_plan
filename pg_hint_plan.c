/*-------------------------------------------------------------------------
 *
 * pg_hint_plan.c
 *		  hinting on how to execute a query for PostgreSQL
 *
 * Copyright (c) 2012-2020, NIPPON TELEGRAPH AND TELEPHONE CORPORATION
 *
 *-------------------------------------------------------------------------
 */
#include <string.h>
#include <math.h>

#include "postgres.h"
#include "access/genam.h"
#include "access/heapam.h"
#include "access/relation.h"
#include "catalog/pg_collation.h"
#include "catalog/pg_index.h"
#include "cdb/cdbmutate.h"
#include "cdb/cdbpath.h"
#include "commands/prepare.h"
#include "mb/pg_wchar.h"
#include "miscadmin.h"
#include "nodes/nodeFuncs.h"
#include "nodes/params.h"
#include "optimizer/appendinfo.h"
#include "optimizer/clauses.h"
#include "optimizer/cost.h"
#include "optimizer/joininfo.h"
#include "optimizer/optimizer.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/plancat.h"
#include "optimizer/planner.h"
#include "optimizer/prep.h"
#include "optimizer/restrictinfo.h"
#include "parser/analyze.h"
#include "parser/parser.h"
#include "parser/parsetree.h"
#include "parser/scansup.h"
#include "partitioning/partbounds.h"
#include "tcop/utility.h"
#include "utils/builtins.h"
#include "utils/float.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/rel.h"
#include "utils/snapmgr.h"
#include "utils/syscache.h"
#include "utils/resowner.h"

#include "catalog/pg_class.h"

#include "executor/spi.h"
#include "catalog/pg_type.h"

#include "plpgsql.h"

/* partially copied from pg_stat_statements */
#include "normalize_query.h"

/* PostgreSQL */
#include "access/htup_details.h"


#include "executor/executor.h"
#include "optimizer/planmain.h"
#include "optimizer/tlist.h"
#include "executor/nodeHash.h"                  /* ExecHashRowSize() */

#include "foreign/fdwapi.h"
#include "utils/selfuncs.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_proc.h"
#include "cdb/cdbhash.h"        /* cdb_default_distribution_opfamily_for_type() */
#include "cdb/cdbpathlocus.h"
#include "cdb/cdbutil.h"		/* getgpsegmentCount() */
#include "cdb/cdbvars.h"
#include "utils/guc.h"

#ifdef MATRIXDB_VERSION
#include <float.h>

#include "nodes/print.h"
#endif /* MATRIXDB_VERSION */

#ifdef PG_MODULE_MAGIC
PG_MODULE_MAGIC;
#endif

#define BLOCK_COMMENT_START		"/*"
#define BLOCK_COMMENT_END		"*/"
#define HINT_COMMENT_KEYWORD	"+"
#define HINT_START				BLOCK_COMMENT_START HINT_COMMENT_KEYWORD
#define HINT_END				BLOCK_COMMENT_END

/* hint keywords */
#define HINT_SEQSCAN			"SeqScan"
#define HINT_INDEXSCAN			"IndexScan"
#define HINT_INDEXSCANREGEXP	"IndexScanRegexp"
#define HINT_BITMAPSCAN			"BitmapScan"
#define HINT_BITMAPSCANREGEXP	"BitmapScanRegexp"
#define HINT_TIDSCAN			"TidScan"
#define HINT_NOSEQSCAN			"NoSeqScan"
#define HINT_NOINDEXSCAN		"NoIndexScan"
#define HINT_NOBITMAPSCAN		"NoBitmapScan"
#define HINT_NOTIDSCAN			"NoTidScan"
#define HINT_INDEXONLYSCAN		"IndexOnlyScan"
#define HINT_INDEXONLYSCANREGEXP	"IndexOnlyScanRegexp"
#define HINT_NOINDEXONLYSCAN	"NoIndexOnlyScan"
#define HINT_PARALLEL			"Parallel"
#define HINT_DISPATCH			"DirectDispatch"

#define HINT_NESTLOOP			"NestLoop"
#define HINT_MERGEJOIN			"MergeJoin"
#define HINT_HASHJOIN			"HashJoin"
#define HINT_NONESTLOOP			"NoNestLoop"
#define HINT_NOMERGEJOIN		"NoMergeJoin"
#define HINT_NOHASHJOIN			"NoHashJoin"
#define HINT_LEADING			"Leading"
#define HINT_SET				"Set"
#define HINT_ROWS				"Rows"

#define HINT_DISABLE_BROADCASTMOTION    "DisableBroadcast"
#define HINT_DISABLE_REDISTRIBUTEMOTION "DisableRedistribute"

#define HINT_ARRAY_DEFAULT_INITSIZE 8

#define hint_ereport(str, detail) hint_parse_ereport(str, detail)
#define hint_parse_ereport(str, detail) \
	do { \
		ereport(pg_hint_plan_parse_message_level,		\
			(errmsg("pg_hint_plan: hint syntax error at or near \"%s\"", (str)), \
			 errdetail detail)); \
	} while(0)

#define skip_space(str) \
	while (isspace(*str)) \
		str++;

enum
{
	ENABLE_SEQSCAN = 0x01,
	ENABLE_INDEXSCAN = 0x02,
	ENABLE_BITMAPSCAN = 0x04,
	ENABLE_TIDSCAN = 0x08,
	ENABLE_INDEXONLYSCAN = 0x10
} SCAN_TYPE_BITS;

enum
{
	ENABLE_NESTLOOP = 0x01,
	ENABLE_MERGEJOIN = 0x02,
	ENABLE_HASHJOIN = 0x04
} JOIN_TYPE_BITS;

enum
{
	ENABLE_BROADCASTMOTION = 0x01,
	ENABLE_REDISTRIBUTEMOTION = 0x02
} MOTION_TYPE_BITS;

#define ENABLE_ALL_SCAN (ENABLE_SEQSCAN | ENABLE_INDEXSCAN | \
						 ENABLE_BITMAPSCAN | ENABLE_TIDSCAN | \
						 ENABLE_INDEXONLYSCAN)
#define ENABLE_ALL_JOIN (ENABLE_NESTLOOP | ENABLE_MERGEJOIN | ENABLE_HASHJOIN)
#define ENABLE_ALL_MOTION (ENABLE_BROADCASTMOTION | ENABLE_REDISTRIBUTEMOTION)
#define DISABLE_ALL_SCAN 0
#define DISABLE_ALL_JOIN 0

/* hint keyword of enum type*/
typedef enum HintKeyword
{
	HINT_KEYWORD_SEQSCAN,
	HINT_KEYWORD_INDEXSCAN,
	HINT_KEYWORD_INDEXSCANREGEXP,
	HINT_KEYWORD_BITMAPSCAN,
	HINT_KEYWORD_BITMAPSCANREGEXP,
	HINT_KEYWORD_TIDSCAN,
	HINT_KEYWORD_NOSEQSCAN,
	HINT_KEYWORD_NOINDEXSCAN,
	HINT_KEYWORD_NOBITMAPSCAN,
	HINT_KEYWORD_NOTIDSCAN,
	HINT_KEYWORD_INDEXONLYSCAN,
	HINT_KEYWORD_INDEXONLYSCANREGEXP,
	HINT_KEYWORD_NOINDEXONLYSCAN,

	HINT_KEYWORD_NESTLOOP,
	HINT_KEYWORD_MERGEJOIN,
	HINT_KEYWORD_HASHJOIN,
	HINT_KEYWORD_NONESTLOOP,
	HINT_KEYWORD_NOMERGEJOIN,
	HINT_KEYWORD_NOHASHJOIN,

	HINT_KEYWORD_LEADING,
	HINT_KEYWORD_SET,
	HINT_KEYWORD_ROWS,
	HINT_KEYWORD_PARALLEL,

	HINT_KEYWORD_DISPATCH,

	HINT_KEYWORD_DISABLEBORADCASTMOTION,
	HINT_KEYWORD_DISABLE_REDISTRIBUTEMOTION,

	HINT_KEYWORD_UNRECOGNIZED
} HintKeyword;

#define SCAN_HINT_ACCEPTS_INDEX_NAMES(kw) \
	(kw == HINT_KEYWORD_INDEXSCAN ||			\
	 kw == HINT_KEYWORD_INDEXSCANREGEXP ||		\
	 kw == HINT_KEYWORD_INDEXONLYSCAN ||		\
	 kw == HINT_KEYWORD_INDEXONLYSCANREGEXP ||	\
	 kw == HINT_KEYWORD_BITMAPSCAN ||				\
	 kw == HINT_KEYWORD_BITMAPSCANREGEXP)


typedef struct Hint Hint;
typedef struct HintState HintState;

typedef Hint *(*HintCreateFunction) (const char *hint_str,
									 const char *keyword,
									 HintKeyword hint_keyword);
typedef void (*HintDeleteFunction) (Hint *hint);
typedef void (*HintDescFunction) (Hint *hint, StringInfo buf, bool nolf);
typedef int (*HintCmpFunction) (const Hint *a, const Hint *b);
typedef const char *(*HintParseFunction) (Hint *hint, HintState *hstate,
										  Query *parse, const char *str);

/* hint types */
#define NUM_HINT_TYPE	7
typedef enum HintType
{
	HINT_TYPE_SCAN_METHOD,
	HINT_TYPE_JOIN_METHOD,
	HINT_TYPE_LEADING,
	HINT_TYPE_SET,
	HINT_TYPE_ROWS,
	HINT_TYPE_PARALLEL,
	HINT_TYPE_MOTION
} HintType;

typedef enum HintTypeBitmap
{
	HINT_BM_SCAN_METHOD = 1,
	HINT_BM_PARALLEL = 2
} HintTypeBitmap;

static const char *HintTypeName[] = {
	"scan method",
	"join method",
	"leading",
	"set",
	"rows",
	"parallel",
	"motion"
};

/* hint status */
typedef enum HintStatus
{
	HINT_STATE_NOTUSED = 0,		/* specified relation not used in query */
	HINT_STATE_USED,			/* hint is used */
	HINT_STATE_DUPLICATION,		/* specified hint duplication */
	HINT_STATE_ERROR			/* execute error (parse error does not include
								 * it) */
} HintStatus;

#define hint_state_enabled(hint) ((hint)->base.state == HINT_STATE_NOTUSED || \
								  (hint)->base.state == HINT_STATE_USED)

static unsigned int qno = 0;
static unsigned int msgqno = 0;
static char qnostr[32];
static const char *current_hint_str = NULL;

/*
 * However we usually take a hint stirng in post_parse_analyze_hook, we still
 * need to do so in planner_hook when client starts query execution from the
 * bind message on a prepared query. This variable prevent duplicate and
 * sometimes harmful hint string retrieval.
 */
static bool current_hint_retrieved = false;

/* common data for all hints. */
struct Hint
{
	const char		   *hint_str;		/* must not do pfree */
	const char		   *keyword;		/* must not do pfree */
	HintKeyword			hint_keyword;
	HintType			type;
	HintStatus			state;
	HintDeleteFunction	delete_func;
	HintDescFunction	desc_func;
	HintCmpFunction		cmp_func;
	HintParseFunction	parse_func;
};

/* scan method hints */
typedef struct ScanMethodHint
{
	Hint			base;
	char		   *relname;
	List		   *indexnames;
	bool			regexp;
	unsigned char	enforce_mask;
} ScanMethodHint;

typedef struct ParentIndexInfo
{
	bool		indisunique;
	Oid			method;
	List	   *column_names;
	char	   *expression_str;
	Oid		   *indcollation;
	Oid		   *opclass;
	int16	   *indoption;
	char	   *indpred_str;
} ParentIndexInfo;

/* join method hints */
typedef struct JoinMethodHint
{
	Hint			base;
	int				nrels;
	int				inner_nrels;
	char		  **relnames;
	unsigned char	enforce_mask;
	Relids			joinrelids;
	Relids			inner_joinrelids;
} JoinMethodHint;

/* motion method hints */
typedef struct MotionHint
{
	Hint			base;
	char		   *relname;
	unsigned char	enforce_mask;
} MotionHint;

/* join order hints */
typedef struct OuterInnerRels
{
	char   *relation;
	List   *outer_inner_pair;
} OuterInnerRels;

typedef struct LeadingHint
{
	Hint			base;
	List		   *relations;	/* relation names specified in Leading hint */
	OuterInnerRels *outer_inner;
} LeadingHint;

/* change a run-time parameter hints */
typedef struct SetHint
{
	Hint	base;
	char   *name;				/* name of variable */
	char   *value;
	List   *words;
} SetHint;

/* rows hints */
typedef enum RowsValueType {
	RVT_ABSOLUTE,		/* Rows(... #1000) */
	RVT_ADD,			/* Rows(... +1000) */
	RVT_SUB,			/* Rows(... -1000) */
	RVT_MULTI,			/* Rows(... *1.2) */
} RowsValueType;
typedef struct RowsHint
{
	Hint			base;
	int				nrels;
	int				inner_nrels;
	char		  **relnames;
	Relids			joinrelids;
	Relids			inner_joinrelids;
	char		   *rows_str;
	RowsValueType	value_type;
	double			rows;
} RowsHint;

/* parallel hints */
typedef struct ParallelHint
{
	Hint			base;
	char		   *relname;
	char		   *nworkers_str;	/* original string of nworkers */
	int				nworkers;		/* num of workers specified by Worker */
	bool			force_parallel;	/* force parallel scan */
} ParallelHint;

typedef struct DispatchHint
{
	Hint			base;
} DispatchHint;

/*
 * Describes a context of hint processing.
 */
struct HintState
{
	char		   *hint_str;			/* original hint string */

	/* all hint */
	int				nall_hints;			/* # of valid all hints */
	int				max_all_hints;		/* # of slots for all hints */
	Hint		  **all_hints;			/* parsed all hints */

	/* # of each hints */
	int				num_hints[NUM_HINT_TYPE];

	/* for scan method hints */
	ScanMethodHint **scan_hints;		/* parsed scan hints */

	/* Initial values of parameters  */
	int				init_scan_mask;		/* enable_* mask */
	int				init_nworkers;		/* max_parallel_workers_per_gather */
	/* min_parallel_table_scan_size*/
	int				init_min_para_tablescan_size;
	/* min_parallel_index_scan_size*/
	int				init_min_para_indexscan_size;
	double			init_paratup_cost;	/* parallel_tuple_cost */
	double			init_parasetup_cost;/* parallel_setup_cost */

	PlannerInfo	   *current_root;		/* PlannerInfo for the followings */
	Index			parent_relid;		/* inherit parent of table relid */
	ScanMethodHint *parent_scan_hint;	/* scan hint for the parent */
	ParallelHint   *parent_parallel_hint; /* parallel hint for the parent */
	List		   *parent_index_infos; /* list of parent table's index */

	JoinMethodHint **join_hints;		/* parsed join hints */
	int				init_join_mask;		/* initial value join parameter */
	List		  **join_hint_level;
	LeadingHint	  **leading_hint;		/* parsed Leading hints */
	SetHint		  **set_hints;			/* parsed Set hints */
	GucContext		context;			/* which GUC parameters can we set? */
	RowsHint	  **rows_hints;			/* parsed Rows hints */
	ParallelHint  **parallel_hints;		/* parsed Parallel hints */
	MotionHint    **motion_hints;		/* parsed Motion hints */
};

/*
 * Describes a hint parser module which is bound with particular hint keyword.
 */
typedef struct HintParser
{
	char			   *keyword;
	HintCreateFunction	create_func;
	HintKeyword			hint_keyword;
} HintParser;


/* Module callbacks */
void		_PG_init(void);
void		_PG_fini(void);

static void push_hint(HintState *hstate);
static void pop_hint(void);

static void pg_hint_plan_post_parse(List *parsetrees, const char *str);
static void pg_hint_plan_post_parse_analyze(ParseState *pstate, Query *query);
static void pg_hint_plan_ProcessUtility(PlannedStmt *pstmt,
					const char *queryString,
					ProcessUtilityContext context,
					ParamListInfo params, QueryEnvironment *queryEnv,
					DestReceiver *dest, char *completionTag);
static PlannedStmt *pg_hint_plan_planner(Query *parse, int cursorOptions,
										 ParamListInfo boundParams);
static RelOptInfo *pg_hint_plan_join_search(PlannerInfo *root,
											int levels_needed,
											List *initial_rels);

/* Scan method hint callbacks */
static Hint *ScanMethodHintCreate(const char *hint_str, const char *keyword,
								  HintKeyword hint_keyword);
static void ScanMethodHintDelete(ScanMethodHint *hint);
static void ScanMethodHintDesc(ScanMethodHint *hint, StringInfo buf, bool nolf);
static int ScanMethodHintCmp(const ScanMethodHint *a, const ScanMethodHint *b);
static const char *ScanMethodHintParse(ScanMethodHint *hint, HintState *hstate,
									   Query *parse, const char *str);

/* Join method hint callbacks */
static Hint *JoinMethodHintCreate(const char *hint_str, const char *keyword,
								  HintKeyword hint_keyword);
static void JoinMethodHintDelete(JoinMethodHint *hint);
static void JoinMethodHintDesc(JoinMethodHint *hint, StringInfo buf, bool nolf);
static int JoinMethodHintCmp(const JoinMethodHint *a, const JoinMethodHint *b);
static const char *JoinMethodHintParse(JoinMethodHint *hint, HintState *hstate,
									   Query *parse, const char *str);

/* Leading hint callbacks */
static Hint *LeadingHintCreate(const char *hint_str, const char *keyword,
							   HintKeyword hint_keyword);
static void LeadingHintDelete(LeadingHint *hint);
static void LeadingHintDesc(LeadingHint *hint, StringInfo buf, bool nolf);
static int LeadingHintCmp(const LeadingHint *a, const LeadingHint *b);
static const char *LeadingHintParse(LeadingHint *hint, HintState *hstate,
									Query *parse, const char *str);

/* Set hint callbacks */
static Hint *SetHintCreate(const char *hint_str, const char *keyword,
						   HintKeyword hint_keyword);
static void SetHintDelete(SetHint *hint);
static void SetHintDesc(SetHint *hint, StringInfo buf, bool nolf);
static int SetHintCmp(const SetHint *a, const SetHint *b);
static const char *SetHintParse(SetHint *hint, HintState *hstate, Query *parse,
								const char *str);

/* Rows hint callbacks */
static Hint *RowsHintCreate(const char *hint_str, const char *keyword,
							HintKeyword hint_keyword);
static void RowsHintDelete(RowsHint *hint);
static void RowsHintDesc(RowsHint *hint, StringInfo buf, bool nolf);
static int RowsHintCmp(const RowsHint *a, const RowsHint *b);
static const char *RowsHintParse(RowsHint *hint, HintState *hstate,
								 Query *parse, const char *str);

/* Parallel hint callbacks */
static Hint *ParallelHintCreate(const char *hint_str, const char *keyword,
								HintKeyword hint_keyword);
static void ParallelHintDelete(ParallelHint *hint);
static void ParallelHintDesc(ParallelHint *hint, StringInfo buf, bool nolf);
static int ParallelHintCmp(const ParallelHint *a, const ParallelHint *b);
static const char *ParallelHintParse(ParallelHint *hint, HintState *hstate,
									 Query *parse, const char *str);

/* Dispatch hint callbacks */
static Hint *DispatchHintCreate(const char *hint_str, const char *keyword,
								  HintKeyword hint_keyword);
static void DispatchHintDelete(DispatchHint *hint);
static const char *DispatchHintParse(DispatchHint *hint, HintState *hstate,
									   Query *parse, const char *str);

/* Motion method hint callbacks */
static Hint *MotionHintCreate(const char *hint_str, const char *keyword,
								  HintKeyword hint_keyword);
static void MotionHintDelete(MotionHint *hint);
static void MotionHintDesc(MotionHint *hint, StringInfo buf, bool nolf);
static int MotionHintCmp(const MotionHint *a, const MotionHint *b);
static const char *MotionHintParse(MotionHint *hint, HintState *hstate,
									   Query *parse, const char *str);

static void quote_value(StringInfo buf, const char *value);

static const char *parse_quoted_value(const char *str, char **word,
									  bool truncate);

RelOptInfo *pg_hint_plan_standard_join_search(PlannerInfo *root,
											  int levels_needed,
											  List *initial_rels);
void pg_hint_plan_join_search_one_level(PlannerInfo *root, int level);
void pg_hint_plan_set_rel_pathlist(PlannerInfo * root, RelOptInfo *rel,
								   Index rti, RangeTblEntry *rte);
static void create_plain_partial_paths(PlannerInfo *root,
													RelOptInfo *rel);
static void make_rels_by_clause_joins(PlannerInfo *root, RelOptInfo *old_rel,
									  ListCell *other_rels);
static void make_rels_by_clauseless_joins(PlannerInfo *root,
										  RelOptInfo *old_rel,
										  ListCell *other_rels);
static bool has_join_restriction(PlannerInfo *root, RelOptInfo *rel);
static void set_plain_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
								   RangeTblEntry *rte);
static void set_append_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
									Index rti, RangeTblEntry *rte);
RelOptInfo *pg_hint_plan_make_join_rel(PlannerInfo *root, RelOptInfo *rel1,
									   RelOptInfo *rel2);

static void pg_hint_plan_plpgsql_stmt_beg(PLpgSQL_execstate *estate,
										  PLpgSQL_stmt *stmt);
static void pg_hint_plan_plpgsql_stmt_end(PLpgSQL_execstate *estate,
										  PLpgSQL_stmt *stmt);
static void plpgsql_query_erase_callback(ResourceReleasePhase phase,
										 bool isCommit,
										 bool isTopLevel,
										 void *arg);
static int set_config_option_noerror(const char *name, const char *value,
						  GucContext context, GucSource source,
						  GucAction action, bool changeVal, int elevel);
static void setup_scan_method_enforcement(ScanMethodHint *scanhint,
										  HintState *state);
static int set_config_int32_option(const char *name, int32 value,
									GucContext context);
static int set_config_double_option(const char *name, double value,
									GucContext context);


static MotionHint *
find_motion_hint(PlannerInfo *root, Index relid);

bool enable_boradcast_on_rel(PlannerInfo *root, RelOptInfo *rel);

bool enable_redistribute_on_rel(PlannerInfo *root, RelOptInfo *rel);

Path *
pg_hint_plan_create_mergejoin_path(PlannerInfo *root,
					  RelOptInfo *joinrel,
					  JoinType jointype,
					  JoinType orig_jointype,		/* CDB */
					  JoinCostWorkspace *workspace,
					  JoinPathExtraData *extra,
					  Path *outer_path,
					  Path *inner_path,
					  List *restrict_clauses,
					  List *pathkeys,
					  Relids required_outer,
					  List *mergeclauses,
					  List *redistribution_clauses,	/* CDB */
					  List *outersortkeys,
					  List *innersortkeys);

Path *
pg_hint_plan_create_nestloop_path(PlannerInfo *root,
					 RelOptInfo *joinrel,
					 JoinType jointype,
					 JoinType orig_jointype,		/* CDB */
					 JoinCostWorkspace *workspace,
					 JoinPathExtraData *extra,
					 Path *outer_path,
					 Path *inner_path,
					 List *restrict_clauses,
					 List *redistribution_clauses,	/* CDB */
					 List *pathkeys,
					 Relids required_outer);

static bool
motion_unmaterial(Path *path, void *context);

/* Motion functions*/
static void hash_inner_and_outer(PlannerInfo *root,
					 RelOptInfo *joinrel,
					 RelOptInfo *outerrel,
					 RelOptInfo *innerrel,
					 JoinType jointype,
					 JoinPathExtraData *extra);
static void try_hashjoin_path(PlannerInfo *root,
				  RelOptInfo *joinrel,
				  Path *outer_path,
				  Path *inner_path,
				  List *hashclauses,
				  JoinType jointype,
				  JoinType orig_jointype,
				  JoinPathExtraData *extra);
void add_paths_to_joinrel_motion_wrapper(PlannerInfo *root,
					 RelOptInfo *joinrel,
					 RelOptInfo *outerrel,
					 RelOptInfo *innerrel,
					 JoinType jointype,
					 SpecialJoinInfo *sjinfo,
					 List *restrictlist);
Path * pg_hint_plan_create_hashjoin_path(PlannerInfo *root,
					 RelOptInfo *joinrel,
					 JoinType jointype,
					 JoinType orig_jointype,		/* CDB */
					 JoinCostWorkspace *workspace,
					 JoinPathExtraData *extra,
					 Path *outer_path,
					 Path *inner_path,
					 bool parallel_hash,
#ifdef MATRIXDB_VERSION
					 bool consider_replicate,
#endif
					 List *restrict_clauses,
					 Relids required_outer,
					 List *redistribution_clauses,	/* CDB */
					 List *hashclauses);
static bool try_redistribute(PlannerInfo *root, CdbpathMfjRel *g, CdbpathMfjRel *o,
				 List *redistribution_clauses);
static Path *add_rowid_to_path(PlannerInfo *root, Path *path, int *rowidexpr_id);
static bool cdbpath_match_preds_to_distkey_tail(CdbpathMatchPredsContext *ctx,
									ListCell *distkeycell);
static bool cdbpath_match_preds_to_distkey(PlannerInfo *root,
							   List *mergeclause_list,
							   Path *path,
							   CdbPathLocus locus,
							   CdbPathLocus *colocus);			
static bool cdbpath_distkeys_from_preds(PlannerInfo *root,
							List *mergeclause_list,
							Path *a_path,
							int numsegments,
#ifdef MATRIXDB_VERSION
							int16 *contentids,
							int parallel_workers,
							CdbPathLocus *a_locus,  /* OUT */
							CdbPathLocus *b_locus);  /* OUT */
#else /* MATRIXDB_VERSION */
							CdbPathLocus *a_locus,	/* OUT */
							CdbPathLocus *b_locus);	/* OUT */
#endif /* MATRIXDB_VERSION */

static List *select_cdb_redistribute_clauses(PlannerInfo *root,
								RelOptInfo *joinrel,
								RelOptInfo *outerrel,
								RelOptInfo *innerrel,
								List *restrictlist,
								JoinType jointype);
static List *select_mergejoin_clauses(PlannerInfo *root,
									  RelOptInfo *joinrel,
									  RelOptInfo *outerrel,
									  RelOptInfo *innerrel,
									  List *restrictlist,
									  JoinType jointype,
									  bool *mergejoin_allowed);
static void sort_inner_and_outer(PlannerInfo *root, RelOptInfo *joinrel,
								 RelOptInfo *outerrel, RelOptInfo *innerrel,
								 JoinType jointype, JoinPathExtraData *extra);
static void match_unsorted_outer(PlannerInfo *root, RelOptInfo *joinrel,
								 RelOptInfo *outerrel, RelOptInfo *innerrel,
								 JoinType jointype, JoinPathExtraData *extra);
static inline bool
clause_sides_match_join(RestrictInfo *rinfo, RelOptInfo *outerrel,
						RelOptInfo *innerrel);
static void
try_partial_hashjoin_path(PlannerInfo *root,
						  RelOptInfo *joinrel,
						  Path *outer_path,
						  Path *inner_path,
						  List *hashclauses,
						  JoinType jointype,
						  JoinType orig_jointype,
						  JoinPathExtraData *extra,
						  bool parallel_hash);
static void
try_partial_nestloop_path(PlannerInfo *root,
						  RelOptInfo *joinrel,
						  Path *outer_path,
						  Path *inner_path,
						  List *pathkeys,
						  JoinType jointype,
						  JoinType orig_jointype,
						  JoinPathExtraData *extra);

static bool
cdbpath_eclass_constant_is_hashable(EquivalenceClass *ec, Oid hashOpFamily);
static bool
ECAllMemberContainParam(EquivalenceClass *ec, CdbpathMatchPredsContext *ctx);
static DistributionKey *
makeDistributionKeyForEC(EquivalenceClass *eclass, Oid opfamily);
static void
consider_parallel_mergejoin(PlannerInfo *root,
							RelOptInfo *joinrel,
							RelOptInfo *outerrel,
							RelOptInfo *innerrel,
							JoinType jointype,
							JoinPathExtraData *extra,
							Path *inner_cheapest_total);
static void
try_mergejoin_path(PlannerInfo *root,
				   RelOptInfo *joinrel,
				   Path *outer_path,
				   Path *inner_path,
				   List *pathkeys,
				   List *mergeclauses,
				   List *outersortkeys,
				   List *innersortkeys,
				   JoinType jointype,
				   JoinType orig_jointype,
				   JoinPathExtraData *extra,
				   bool is_partial);
static void
try_nestloop_path(PlannerInfo *root,
				  RelOptInfo *joinrel,
				  Path *outer_path,
				  Path *inner_path,
				  List *pathkeys,
				  JoinType jointype,
				  JoinType orig_jointype,	/* CDB */
				  JoinPathExtraData *extra);
static void
try_partial_mergejoin_path(PlannerInfo *root,
						   RelOptInfo *joinrel,
						   Path *outer_path,
						   Path *inner_path,
						   List *pathkeys,
						   List *mergeclauses,
						   List *outersortkeys,
						   List *innersortkeys,
						   JoinType jointype,
#ifdef MATRIXDB_VERSION
						   JoinType orig_jointype,
#endif
						   JoinPathExtraData *extra);

static void
generate_mergejoin_paths(PlannerInfo *root,
						 RelOptInfo *joinrel,
						 RelOptInfo *innerrel,
						 Path *outerpath,
						 JoinType jointype,
						 JoinPathExtraData *extra,
						 bool useallclauses,
						 Path *inner_cheapest_total,
						 List *merge_pathkeys,
						 bool is_partial);
				
static void
consider_parallel_nestloop(PlannerInfo *root,
						   RelOptInfo *joinrel,
						   RelOptInfo *outerrel,
						   RelOptInfo *innerrel,
						   JoinType jointype,
						   JoinPathExtraData *extra);
static bool
expr_param_walker(Expr *expr, Bitmapset** param_ids);

static inline bool
allow_star_schema_join(PlannerInfo *root,
					   Relids outerrelids,
					   Relids inner_paramrels);

static void
consider_parallel_nestloop(PlannerInfo *root,
						   RelOptInfo *joinrel,
						   RelOptInfo *outerrel,
						   RelOptInfo *innerrel,
						   JoinType jointype,
						   JoinPathExtraData *extra);

/* GUC variables */
static bool	pg_hint_plan_enable_hint = true;
static int debug_level = 0;
static int	pg_hint_plan_parse_message_level = INFO;
static int	pg_hint_plan_debug_message_level = LOG;
/* Default is off, to keep backward compatibility. */
static bool	pg_hint_plan_enable_hint_table = false;
static bool pg_hint_plan_enable_redistribute_motion = true;

static int plpgsql_recurse_level = 0;		/* PLpgSQL recursion level            */
static int recurse_level = 0;		/* recursion level incl. direct SPI calls */
static int hint_inhibit_level = 0;			/* Inhibit hinting if this is above 0 */
											/* (This could not be above 1)        */
static int max_hint_nworkers = -1;		/* Maximum nworkers of Workers hints */

static const struct config_enum_entry parse_messages_level_options[] = {
	{"debug", DEBUG2, true},
	{"debug5", DEBUG5, false},
	{"debug4", DEBUG4, false},
	{"debug3", DEBUG3, false},
	{"debug2", DEBUG2, false},
	{"debug1", DEBUG1, false},
	{"log", LOG, false},
	{"info", INFO, false},
	{"notice", NOTICE, false},
	{"warning", WARNING, false},
	{"error", ERROR, false},
	/*
	 * {"fatal", FATAL, true},
	 * {"panic", PANIC, true},
	 */
	{NULL, 0, false}
};

static const struct config_enum_entry parse_debug_level_options[] = {
	{"off", 0, false},
	{"on", 1, false},
	{"detailed", 2, false},
	{"verbose", 3, false},
	{"0", 0, true},
	{"1", 1, true},
	{"2", 2, true},
	{"3", 3, true},
	{"no", 0, true},
	{"yes", 1, true},
	{"false", 0, true},
	{"true", 1, true},
	{NULL, 0, false}
};

/* Saved hook values in case of unload */
static post_parse_hook_type prev_post_parse_hook = NULL;
static post_parse_analyze_hook_type prev_post_parse_analyze_hook = NULL;
static planner_hook_type prev_planner = NULL;
static join_search_hook_type prev_join_search = NULL;
static set_rel_pathlist_hook_type prev_set_rel_pathlist = NULL;
static ProcessUtility_hook_type prev_ProcessUtility_hook = NULL;

/* Hold reference to currently active hint */
static HintState *current_hint_state = NULL;

/*
 * List of hint contexts.  We treat the head of the list as the Top of the
 * context stack, so current_hint_state always points the first element of this
 * list.
 */
static List *HintStateStack = NIL;

static const HintParser parsers[] = {
	{HINT_SEQSCAN, ScanMethodHintCreate, HINT_KEYWORD_SEQSCAN},
	{HINT_INDEXSCAN, ScanMethodHintCreate, HINT_KEYWORD_INDEXSCAN},
	{HINT_INDEXSCANREGEXP, ScanMethodHintCreate, HINT_KEYWORD_INDEXSCANREGEXP},
	{HINT_BITMAPSCAN, ScanMethodHintCreate, HINT_KEYWORD_BITMAPSCAN},
	{HINT_BITMAPSCANREGEXP, ScanMethodHintCreate,
	 HINT_KEYWORD_BITMAPSCANREGEXP},
	{HINT_TIDSCAN, ScanMethodHintCreate, HINT_KEYWORD_TIDSCAN},
	{HINT_NOSEQSCAN, ScanMethodHintCreate, HINT_KEYWORD_NOSEQSCAN},
	{HINT_NOINDEXSCAN, ScanMethodHintCreate, HINT_KEYWORD_NOINDEXSCAN},
	{HINT_NOBITMAPSCAN, ScanMethodHintCreate, HINT_KEYWORD_NOBITMAPSCAN},
	{HINT_NOTIDSCAN, ScanMethodHintCreate, HINT_KEYWORD_NOTIDSCAN},
	{HINT_INDEXONLYSCAN, ScanMethodHintCreate, HINT_KEYWORD_INDEXONLYSCAN},
	{HINT_INDEXONLYSCANREGEXP, ScanMethodHintCreate,
	 HINT_KEYWORD_INDEXONLYSCANREGEXP},
	{HINT_NOINDEXONLYSCAN, ScanMethodHintCreate, HINT_KEYWORD_NOINDEXONLYSCAN},

	{HINT_NESTLOOP, JoinMethodHintCreate, HINT_KEYWORD_NESTLOOP},
	{HINT_MERGEJOIN, JoinMethodHintCreate, HINT_KEYWORD_MERGEJOIN},
	{HINT_HASHJOIN, JoinMethodHintCreate, HINT_KEYWORD_HASHJOIN},
	{HINT_NONESTLOOP, JoinMethodHintCreate, HINT_KEYWORD_NONESTLOOP},
	{HINT_NOMERGEJOIN, JoinMethodHintCreate, HINT_KEYWORD_NOMERGEJOIN},
	{HINT_NOHASHJOIN, JoinMethodHintCreate, HINT_KEYWORD_NOHASHJOIN},

	{HINT_LEADING, LeadingHintCreate, HINT_KEYWORD_LEADING},
	{HINT_SET, SetHintCreate, HINT_KEYWORD_SET},
	{HINT_ROWS, RowsHintCreate, HINT_KEYWORD_ROWS},
	{HINT_PARALLEL, ParallelHintCreate, HINT_KEYWORD_PARALLEL},
	{HINT_DISABLE_BROADCASTMOTION, MotionHintCreate, HINT_KEYWORD_DISABLEBORADCASTMOTION},
	{HINT_DISABLE_REDISTRIBUTEMOTION, MotionHintCreate, HINT_KEYWORD_DISABLE_REDISTRIBUTEMOTION},

	{HINT_DISPATCH, DispatchHintCreate, HINT_KEYWORD_DISPATCH},

	{NULL, NULL, HINT_KEYWORD_UNRECOGNIZED}
};

PLpgSQL_plugin  plugin_funcs = {
	NULL,
	NULL,
	NULL,
	pg_hint_plan_plpgsql_stmt_beg,
	pg_hint_plan_plpgsql_stmt_end,
	NULL,
	NULL,
};

/*
 * Module load callbacks
 */
void
_PG_init(void)
{
	PLpgSQL_plugin	**var_ptr;

	/* Define custom GUC variables. */
	DefineCustomBoolVariable("pg_hint_plan.enable_hint",
			 "Force planner to use plans specified in the hint comment preceding to the query.",
							 NULL,
							 &pg_hint_plan_enable_hint,
							 true,
							 PGC_USERSET,
							 0,
							 NULL,
							 NULL,
							 NULL);

	DefineCustomEnumVariable("pg_hint_plan.debug_print",
							 "Logs results of hint parsing.",
							 NULL,
							 &debug_level,
							 false,
							 parse_debug_level_options,
							 PGC_USERSET,
							 0,
							 NULL,
							 NULL,
							 NULL);

	DefineCustomEnumVariable("pg_hint_plan.parse_messages",
							 "Message level of parse errors.",
							 NULL,
							 &pg_hint_plan_parse_message_level,
							 INFO,
							 parse_messages_level_options,
							 PGC_USERSET,
							 0,
							 NULL,
							 NULL,
							 NULL);

	DefineCustomEnumVariable("pg_hint_plan.message_level",
							 "Message level of debug messages.",
							 NULL,
							 &pg_hint_plan_debug_message_level,
							 LOG,
							 parse_messages_level_options,
							 PGC_USERSET,
							 0,
							 NULL,
							 NULL,
							 NULL);

	DefineCustomBoolVariable("pg_hint_plan.enable_hint_table",
							 "Let pg_hint_plan look up the hint table.",
							 NULL,
							 &pg_hint_plan_enable_hint_table,
							 false,
							 PGC_USERSET,
							 0,
							 NULL,
							 NULL,
							 NULL);

	DefineCustomBoolVariable("pg_hint_plan.pg_hint_plan_enable_redistribute_motion",
							 "Enable redistribute motion to effect plan",
							 NULL,
							 &pg_hint_plan_enable_redistribute_motion,
							 true,
							 PGC_USERSET,
							 0,
							 NULL,
							 NULL,
							 NULL);

	/* Install hooks. */
	prev_post_parse_hook = post_parse_hook;
	post_parse_hook = pg_hint_plan_post_parse;
	prev_post_parse_analyze_hook = post_parse_analyze_hook;
	post_parse_analyze_hook = pg_hint_plan_post_parse_analyze;
	prev_planner = planner_hook;
	planner_hook = pg_hint_plan_planner;
	prev_join_search = join_search_hook;
	join_search_hook = pg_hint_plan_join_search;
	prev_set_rel_pathlist = set_rel_pathlist_hook;
	set_rel_pathlist_hook = pg_hint_plan_set_rel_pathlist;
	prev_ProcessUtility_hook = ProcessUtility_hook;
	ProcessUtility_hook = pg_hint_plan_ProcessUtility;

	/* setup PL/pgSQL plugin hook */
	var_ptr = (PLpgSQL_plugin **) find_rendezvous_variable("PLpgSQL_plugin");
	*var_ptr = &plugin_funcs;

	RegisterResourceReleaseCallback(plpgsql_query_erase_callback, NULL);
}

/*
 * Module unload callback
 * XXX never called
 */
void
_PG_fini(void)
{
	PLpgSQL_plugin	**var_ptr;

	/* Uninstall hooks. */
	post_parse_hook = prev_post_parse_hook;
	post_parse_analyze_hook = prev_post_parse_analyze_hook;
	planner_hook = prev_planner;
	join_search_hook = prev_join_search;
	set_rel_pathlist_hook = prev_set_rel_pathlist;
	ProcessUtility_hook = prev_ProcessUtility_hook;

	/* uninstall PL/pgSQL plugin hook */
	var_ptr = (PLpgSQL_plugin **) find_rendezvous_variable("PLpgSQL_plugin");
	*var_ptr = NULL;
}

/*
 * create and delete functions the hint object
 */

static Hint *
ScanMethodHintCreate(const char *hint_str, const char *keyword,
					 HintKeyword hint_keyword)
{
	ScanMethodHint *hint;

	hint = palloc(sizeof(ScanMethodHint));
	hint->base.hint_str = hint_str;
	hint->base.keyword = keyword;
	hint->base.hint_keyword = hint_keyword;
	hint->base.type = HINT_TYPE_SCAN_METHOD;
	hint->base.state = HINT_STATE_NOTUSED;
	hint->base.delete_func = (HintDeleteFunction) ScanMethodHintDelete;
	hint->base.desc_func = (HintDescFunction) ScanMethodHintDesc;
	hint->base.cmp_func = (HintCmpFunction) ScanMethodHintCmp;
	hint->base.parse_func = (HintParseFunction) ScanMethodHintParse;
	hint->relname = NULL;
	hint->indexnames = NIL;
	hint->regexp = false;
	hint->enforce_mask = 0;

	return (Hint *) hint;
}

static void
ScanMethodHintDelete(ScanMethodHint *hint)
{
	if (!hint)
		return;

	if (hint->relname)
		pfree(hint->relname);
	list_free_deep(hint->indexnames);
	pfree(hint);
}

static Hint *
JoinMethodHintCreate(const char *hint_str, const char *keyword,
					 HintKeyword hint_keyword)
{
	JoinMethodHint *hint;

	hint = palloc(sizeof(JoinMethodHint));
	hint->base.hint_str = hint_str;
	hint->base.keyword = keyword;
	hint->base.hint_keyword = hint_keyword;
	hint->base.type = HINT_TYPE_JOIN_METHOD;
	hint->base.state = HINT_STATE_NOTUSED;
	hint->base.delete_func = (HintDeleteFunction) JoinMethodHintDelete;
	hint->base.desc_func = (HintDescFunction) JoinMethodHintDesc;
	hint->base.cmp_func = (HintCmpFunction) JoinMethodHintCmp;
	hint->base.parse_func = (HintParseFunction) JoinMethodHintParse;
	hint->nrels = 0;
	hint->inner_nrels = 0;
	hint->relnames = NULL;
	hint->enforce_mask = 0;
	hint->joinrelids = NULL;
	hint->inner_joinrelids = NULL;

	return (Hint *) hint;
}

static void
JoinMethodHintDelete(JoinMethodHint *hint)
{
	if (!hint)
		return;

	if (hint->relnames)
	{
		int	i;

		for (i = 0; i < hint->nrels; i++)
			pfree(hint->relnames[i]);
		pfree(hint->relnames);
	}

	bms_free(hint->joinrelids);
	bms_free(hint->inner_joinrelids);
	pfree(hint);
}

static Hint *
LeadingHintCreate(const char *hint_str, const char *keyword,
				  HintKeyword hint_keyword)
{
	LeadingHint	   *hint;

	hint = palloc(sizeof(LeadingHint));
	hint->base.hint_str = hint_str;
	hint->base.keyword = keyword;
	hint->base.hint_keyword = hint_keyword;
	hint->base.type = HINT_TYPE_LEADING;
	hint->base.state = HINT_STATE_NOTUSED;
	hint->base.delete_func = (HintDeleteFunction)LeadingHintDelete;
	hint->base.desc_func = (HintDescFunction) LeadingHintDesc;
	hint->base.cmp_func = (HintCmpFunction) LeadingHintCmp;
	hint->base.parse_func = (HintParseFunction) LeadingHintParse;
	hint->relations = NIL;
	hint->outer_inner = NULL;

	return (Hint *) hint;
}

static void
LeadingHintDelete(LeadingHint *hint)
{
	if (!hint)
		return;

	list_free_deep(hint->relations);
	if (hint->outer_inner)
		pfree(hint->outer_inner);
	pfree(hint);
}

static Hint *
SetHintCreate(const char *hint_str, const char *keyword,
			  HintKeyword hint_keyword)
{
	SetHint	   *hint;

	hint = palloc(sizeof(SetHint));
	hint->base.hint_str = hint_str;
	hint->base.keyword = keyword;
	hint->base.hint_keyword = hint_keyword;
	hint->base.type = HINT_TYPE_SET;
	hint->base.state = HINT_STATE_NOTUSED;
	hint->base.delete_func = (HintDeleteFunction) SetHintDelete;
	hint->base.desc_func = (HintDescFunction) SetHintDesc;
	hint->base.cmp_func = (HintCmpFunction) SetHintCmp;
	hint->base.parse_func = (HintParseFunction) SetHintParse;
	hint->name = NULL;
	hint->value = NULL;
	hint->words = NIL;

	return (Hint *) hint;
}

static void
SetHintDelete(SetHint *hint)
{
	if (!hint)
		return;

	if (hint->name)
		pfree(hint->name);
	if (hint->value)
		pfree(hint->value);
	if (hint->words)
		list_free(hint->words);
	pfree(hint);
}

static Hint *
RowsHintCreate(const char *hint_str, const char *keyword,
			   HintKeyword hint_keyword)
{
	RowsHint *hint;

	hint = palloc(sizeof(RowsHint));
	hint->base.hint_str = hint_str;
	hint->base.keyword = keyword;
	hint->base.hint_keyword = hint_keyword;
	hint->base.type = HINT_TYPE_ROWS;
	hint->base.state = HINT_STATE_NOTUSED;
	hint->base.delete_func = (HintDeleteFunction) RowsHintDelete;
	hint->base.desc_func = (HintDescFunction) RowsHintDesc;
	hint->base.cmp_func = (HintCmpFunction) RowsHintCmp;
	hint->base.parse_func = (HintParseFunction) RowsHintParse;
	hint->nrels = 0;
	hint->inner_nrels = 0;
	hint->relnames = NULL;
	hint->joinrelids = NULL;
	hint->inner_joinrelids = NULL;
	hint->rows_str = NULL;
	hint->value_type = RVT_ABSOLUTE;
	hint->rows = 0;

	return (Hint *) hint;
}

static void
RowsHintDelete(RowsHint *hint)
{
	if (!hint)
		return;

	if (hint->relnames)
	{
		int	i;

		for (i = 0; i < hint->nrels; i++)
			pfree(hint->relnames[i]);
		pfree(hint->relnames);
	}

	bms_free(hint->joinrelids);
	bms_free(hint->inner_joinrelids);
	pfree(hint);
}

static Hint *
ParallelHintCreate(const char *hint_str, const char *keyword,
				  HintKeyword hint_keyword)
{
	ParallelHint *hint;

	hint = palloc(sizeof(ParallelHint));
	hint->base.hint_str = hint_str;
	hint->base.keyword = keyword;
	hint->base.hint_keyword = hint_keyword;
	hint->base.type = HINT_TYPE_PARALLEL;
	hint->base.state = HINT_STATE_NOTUSED;
	hint->base.delete_func = (HintDeleteFunction) ParallelHintDelete;
	hint->base.desc_func = (HintDescFunction) ParallelHintDesc;
	hint->base.cmp_func = (HintCmpFunction) ParallelHintCmp;
	hint->base.parse_func = (HintParseFunction) ParallelHintParse;
	hint->relname = NULL;
	hint->nworkers = 0;
	hint->nworkers_str = "0";

	return (Hint *) hint;
}

static void
ParallelHintDelete(ParallelHint *hint)
{
	if (!hint)
		return;

	if (hint->relname)
		pfree(hint->relname);
	pfree(hint);
}

static Hint *
DispatchHintCreate(const char *hint_str, const char *keyword,
					 HintKeyword hint_keyword)
{
	DispatchHint *hint;

	hint = palloc(sizeof(DispatchHint));
	hint->base.hint_str = hint_str;
	hint->base.keyword = keyword;
	hint->base.hint_keyword = hint_keyword;
	hint->base.delete_func = (HintDeleteFunction) DispatchHintDelete;
	hint->base.parse_func = (HintParseFunction) DispatchHintParse;

	return (Hint *) hint;
}

static void
DispatchHintDelete(DispatchHint *hint)
{
	if (!hint)
		return;

	pfree(hint);
}

static Hint *
MotionHintCreate(const char *hint_str, const char *keyword,
					 HintKeyword hint_keyword)
{
	MotionHint *hint;

	hint = palloc(sizeof(MotionHint));
	hint->base.hint_str = hint_str;
	hint->base.keyword = keyword;
	hint->base.hint_keyword = hint_keyword;
	hint->base.type = HINT_TYPE_MOTION;
	hint->base.state = HINT_STATE_NOTUSED;
	hint->base.delete_func = (HintDeleteFunction) MotionHintDelete;
	hint->base.desc_func = (HintDescFunction) MotionHintDesc;
	hint->base.cmp_func = (HintCmpFunction) MotionHintCmp;
	hint->base.parse_func = (HintParseFunction) MotionHintParse;
	hint->relname = NULL;
	hint->enforce_mask = 0;

	return (Hint *) hint;
}

static void
MotionHintDelete(MotionHint *hint)
{
	if (!hint)
		return;

	if (hint->relname)
		pfree(hint->relname);
	pfree(hint);
}

static HintState *
HintStateCreate(void)
{
	HintState   *hstate;

	hstate = palloc(sizeof(HintState));
	hstate->hint_str = NULL;
	hstate->nall_hints = 0;
	hstate->max_all_hints = 0;
	hstate->all_hints = NULL;
	memset(hstate->num_hints, 0, sizeof(hstate->num_hints));
	hstate->scan_hints = NULL;
	hstate->init_scan_mask = 0;
	hstate->init_nworkers = 0;
	hstate->init_min_para_tablescan_size = 0;
	hstate->init_min_para_indexscan_size = 0;
	hstate->init_paratup_cost = 0;
	hstate->init_parasetup_cost = 0;
	hstate->current_root = NULL;
	hstate->parent_relid = 0;
	hstate->parent_scan_hint = NULL;
	hstate->parent_parallel_hint = NULL;
	hstate->parent_index_infos = NIL;
	hstate->join_hints = NULL;
	hstate->init_join_mask = 0;
	hstate->join_hint_level = NULL;
	hstate->leading_hint = NULL;
	hstate->context = superuser() ? PGC_SUSET : PGC_USERSET;
	hstate->set_hints = NULL;
	hstate->rows_hints = NULL;
	hstate->parallel_hints = NULL;
	hstate->motion_hints = NULL;

	return hstate;
}

static void
HintStateDelete(HintState *hstate)
{
	int			i;

	if (!hstate)
		return;

	if (hstate->hint_str)
		pfree(hstate->hint_str);

	for (i = 0; i < hstate->num_hints[HINT_TYPE_SCAN_METHOD]; i++)
		hstate->all_hints[i]->delete_func(hstate->all_hints[i]);
	if (hstate->all_hints)
		pfree(hstate->all_hints);
	if (hstate->parent_index_infos)
		list_free(hstate->parent_index_infos);
}

/*
 * Copy given value into buf, with quoting with '"' if necessary.
 */
static void
quote_value(StringInfo buf, const char *value)
{
	bool		need_quote = false;
	const char *str;

	for (str = value; *str != '\0'; str++)
	{
		if (isspace(*str) || *str == '(' || *str == ')' || *str == '"')
		{
			need_quote = true;
			appendStringInfoCharMacro(buf, '"');
			break;
		}
	}

	for (str = value; *str != '\0'; str++)
	{
		if (*str == '"')
			appendStringInfoCharMacro(buf, '"');

		appendStringInfoCharMacro(buf, *str);
	}

	if (need_quote)
		appendStringInfoCharMacro(buf, '"');
}

static void
ScanMethodHintDesc(ScanMethodHint *hint, StringInfo buf, bool nolf)
{
	ListCell   *l;

	appendStringInfo(buf, "%s(", hint->base.keyword);
	if (hint->relname != NULL)
	{
		quote_value(buf, hint->relname);
		foreach(l, hint->indexnames)
		{
			appendStringInfoCharMacro(buf, ' ');
			quote_value(buf, (char *) lfirst(l));
		}
	}
	appendStringInfoString(buf, ")");
	if (!nolf)
		appendStringInfoChar(buf, '\n');
}

static void
JoinMethodHintDesc(JoinMethodHint *hint, StringInfo buf, bool nolf)
{
	int	i;

	appendStringInfo(buf, "%s(", hint->base.keyword);
	if (hint->relnames != NULL)
	{
		quote_value(buf, hint->relnames[0]);
		for (i = 1; i < hint->nrels; i++)
		{
			appendStringInfoCharMacro(buf, ' ');
			quote_value(buf, hint->relnames[i]);
		}
	}
	appendStringInfoString(buf, ")");
	if (!nolf)
		appendStringInfoChar(buf, '\n');
}

static void
OuterInnerDesc(OuterInnerRels *outer_inner, StringInfo buf)
{
	if (outer_inner->relation == NULL)
	{
		bool		is_first;
		ListCell   *l;

		is_first = true;

		appendStringInfoCharMacro(buf, '(');
		foreach(l, outer_inner->outer_inner_pair)
		{
			if (is_first)
				is_first = false;
			else
				appendStringInfoCharMacro(buf, ' ');

			OuterInnerDesc(lfirst(l), buf);
		}

		appendStringInfoCharMacro(buf, ')');
	}
	else
		quote_value(buf, outer_inner->relation);
}

static void
LeadingHintDesc(LeadingHint *hint, StringInfo buf, bool nolf)
{
	appendStringInfo(buf, "%s(", HINT_LEADING);
	if (hint->outer_inner == NULL)
	{
		ListCell   *l;
		bool		is_first;

		is_first = true;

		foreach(l, hint->relations)
		{
			if (is_first)
				is_first = false;
			else
				appendStringInfoCharMacro(buf, ' ');

			quote_value(buf, (char *) lfirst(l));
		}
	}
	else
		OuterInnerDesc(hint->outer_inner, buf);

	appendStringInfoString(buf, ")");
	if (!nolf)
		appendStringInfoChar(buf, '\n');
}

static void
SetHintDesc(SetHint *hint, StringInfo buf, bool nolf)
{
	bool		is_first = true;
	ListCell   *l;

	appendStringInfo(buf, "%s(", HINT_SET);
	foreach(l, hint->words)
	{
		if (is_first)
			is_first = false;
		else
			appendStringInfoCharMacro(buf, ' ');

		quote_value(buf, (char *) lfirst(l));
	}
	appendStringInfo(buf, ")");
	if (!nolf)
		appendStringInfoChar(buf, '\n');
}

static void
RowsHintDesc(RowsHint *hint, StringInfo buf, bool nolf)
{
	int	i;

	appendStringInfo(buf, "%s(", hint->base.keyword);
	if (hint->relnames != NULL)
	{
		quote_value(buf, hint->relnames[0]);
		for (i = 1; i < hint->nrels; i++)
		{
			appendStringInfoCharMacro(buf, ' ');
			quote_value(buf, hint->relnames[i]);
		}
	}
	if (hint->rows_str != NULL)
		appendStringInfo(buf, " %s", hint->rows_str);
	appendStringInfoString(buf, ")");
	if (!nolf)
		appendStringInfoChar(buf, '\n');
}

static void
ParallelHintDesc(ParallelHint *hint, StringInfo buf, bool nolf)
{
	appendStringInfo(buf, "%s(", hint->base.keyword);
	if (hint->relname != NULL)
	{
		quote_value(buf, hint->relname);

		/* number of workers  */
		appendStringInfoCharMacro(buf, ' ');
		quote_value(buf, hint->nworkers_str);
		/* application mode of num of workers */
		appendStringInfoCharMacro(buf, ' ');
		appendStringInfoString(buf,
							   (hint->force_parallel ? "hard" : "soft"));
	}
	appendStringInfoString(buf, ")");
	if (!nolf)
		appendStringInfoChar(buf, '\n');
}

static void
MotionHintDesc(MotionHint *hint, StringInfo buf, bool nolf)
{
	ListCell   *l;

	appendStringInfo(buf, "%s(", hint->base.keyword);
	if (hint->relname != NULL)
	{
		quote_value(buf, hint->relname);
	}
	appendStringInfoString(buf, ")");
	if (!nolf)
		appendStringInfoChar(buf, '\n');
}

/*
 * Append string which represents all hints in a given state to buf, with
 * preceding title with them.
 */
static void
desc_hint_in_state(HintState *hstate, StringInfo buf, const char *title,
				   HintStatus state, bool nolf)
{
	int	i, nshown;

	appendStringInfo(buf, "%s:", title);
	if (!nolf)
		appendStringInfoChar(buf, '\n');

	nshown = 0;
	for (i = 0; i < hstate->nall_hints; i++)
	{
		if (hstate->all_hints[i]->state != state)
			continue;

		hstate->all_hints[i]->desc_func(hstate->all_hints[i], buf, nolf);
		nshown++;
	}

	if (nolf && nshown == 0)
		appendStringInfoString(buf, "(none)");
}

/*
 * Dump contents of given hstate to server log with log level LOG.
 */
static void
HintStateDump(HintState *hstate)
{
	StringInfoData	buf;

	if (!hstate)
	{
		elog(pg_hint_plan_debug_message_level, "pg_hint_plan:\nno hint");
		return;
	}

	initStringInfo(&buf);

	appendStringInfoString(&buf, "pg_hint_plan:\n");
	desc_hint_in_state(hstate, &buf, "used hint", HINT_STATE_USED, false);
	desc_hint_in_state(hstate, &buf, "not used hint", HINT_STATE_NOTUSED, false);
	desc_hint_in_state(hstate, &buf, "duplication hint", HINT_STATE_DUPLICATION, false);
	desc_hint_in_state(hstate, &buf, "error hint", HINT_STATE_ERROR, false);

	ereport(pg_hint_plan_debug_message_level,
			(errmsg ("%s", buf.data)));

	pfree(buf.data);
}

static void
HintStateDump2(HintState *hstate)
{
	StringInfoData	buf;

	if (!hstate)
	{
		elog(pg_hint_plan_debug_message_level,
			 "pg_hint_plan%s: HintStateDump: no hint", qnostr);
		return;
	}

	initStringInfo(&buf);
	appendStringInfo(&buf, "pg_hint_plan%s: HintStateDump: ", qnostr);
	desc_hint_in_state(hstate, &buf, "{used hints", HINT_STATE_USED, true);
	desc_hint_in_state(hstate, &buf, "}, {not used hints", HINT_STATE_NOTUSED, true);
	desc_hint_in_state(hstate, &buf, "}, {duplicate hints", HINT_STATE_DUPLICATION, true);
	desc_hint_in_state(hstate, &buf, "}, {error hints", HINT_STATE_ERROR, true);
	appendStringInfoChar(&buf, '}');

	ereport(pg_hint_plan_debug_message_level,
			(errmsg("%s", buf.data),
			 errhidestmt(true),
			 errhidecontext(true)));

	pfree(buf.data);
}

/*
 * compare functions
 */

static int
RelnameCmp(const void *a, const void *b)
{
	const char *relnamea = *((const char **) a);
	const char *relnameb = *((const char **) b);

	return strcmp(relnamea, relnameb);
}

static int
ScanMethodHintCmp(const ScanMethodHint *a, const ScanMethodHint *b)
{
	return RelnameCmp(&a->relname, &b->relname);
}

static int
JoinMethodHintCmp(const JoinMethodHint *a, const JoinMethodHint *b)
{
	int	i;

	if (a->nrels != b->nrels)
		return a->nrels - b->nrels;

	for (i = 0; i < a->nrels; i++)
	{
		int	result;
		if ((result = RelnameCmp(&a->relnames[i], &b->relnames[i])) != 0)
			return result;
	}

	return 0;
}

static int
LeadingHintCmp(const LeadingHint *a, const LeadingHint *b)
{
	return 0;
}

static int
SetHintCmp(const SetHint *a, const SetHint *b)
{
	return strcmp(a->name, b->name);
}

static int
RowsHintCmp(const RowsHint *a, const RowsHint *b)
{
	int	i;

	if (a->nrels != b->nrels)
		return a->nrels - b->nrels;

	for (i = 0; i < a->nrels; i++)
	{
		int	result;
		if ((result = RelnameCmp(&a->relnames[i], &b->relnames[i])) != 0)
			return result;
	}

	return 0;
}

static int
ParallelHintCmp(const ParallelHint *a, const ParallelHint *b)
{
	return RelnameCmp(&a->relname, &b->relname);
}

static int
MotionHintCmp(const MotionHint *a, const MotionHint *b)
{
	return RelnameCmp(&a->relname, &b->relname);
}

static int
HintCmp(const void *a, const void *b)
{
	const Hint *hinta = *((const Hint **) a);
	const Hint *hintb = *((const Hint **) b);

	if (hinta->type != hintb->type)
		return hinta->type - hintb->type;
	if (hinta->state == HINT_STATE_ERROR)
		return -1;
	if (hintb->state == HINT_STATE_ERROR)
		return 1;
	return hinta->cmp_func(hinta, hintb);
}

/*
 * Returns byte offset of hint b from hint a.  If hint a was specified before
 * b, positive value is returned.
 */
static int
HintCmpWithPos(const void *a, const void *b)
{
	const Hint *hinta = *((const Hint **) a);
	const Hint *hintb = *((const Hint **) b);
	int		result;

	result = HintCmp(a, b);
	if (result == 0)
		result = hinta->hint_str - hintb->hint_str;

	return result;
}

/*
 * parse functions
 */
static const char *
parse_keyword(const char *str, StringInfo buf)
{
	skip_space(str);

	while (!isspace(*str) && *str != '(' && *str != '\0')
		appendStringInfoCharMacro(buf, *str++);

	return str;
}

static const char *
skip_parenthesis(const char *str, char parenthesis)
{
	skip_space(str);

	if (*str != parenthesis)
	{
		if (parenthesis == '(')
			hint_ereport(str, ("Opening parenthesis is necessary."));
		else if (parenthesis == ')')
			hint_ereport(str, ("Closing parenthesis is necessary."));

		return NULL;
	}

	str++;

	return str;
}

/*
 * Parse a token from str, and store malloc'd copy into word.  A token can be
 * quoted with '"'.  Return value is pointer to unparsed portion of original
 * string, or NULL if an error occurred.
 *
 * Parsed token is truncated within NAMEDATALEN-1 bytes, when truncate is true.
 */
static const char *
parse_quoted_value(const char *str, char **word, bool truncate)
{
	StringInfoData	buf;
	bool			in_quote;

	/* Skip leading spaces. */
	skip_space(str);

	initStringInfo(&buf);
	if (*str == '"')
	{
		str++;
		in_quote = true;
	}
	else
		in_quote = false;

	while (true)
	{
		if (in_quote)
		{
			/* Double quotation must be closed. */
			if (*str == '\0')
			{
				pfree(buf.data);
				hint_ereport(str, ("Unterminated quoted string."));
				return NULL;
			}

			/*
			 * Skip escaped double quotation.
			 *
			 * We don't allow slash-asterisk and asterisk-slash (delimiters of
			 * block comments) to be an object name, so users must specify
			 * alias for such object names.
			 *
			 * Those special names can be allowed if we care escaped slashes
			 * and asterisks, but we don't.
			 */
			if (*str == '"')
			{
				str++;
				if (*str != '"')
					break;
			}
		}
		else if (isspace(*str) || *str == '(' || *str == ')' || *str == '"' ||
				 *str == '\0')
			break;

		appendStringInfoCharMacro(&buf, *str++);
	}

	if (buf.len == 0)
	{
		hint_ereport(str, ("Zero-length delimited string."));

		pfree(buf.data);

		return NULL;
	}

	/* Truncate name if it's too long */
	if (truncate)
		truncate_identifier(buf.data, strlen(buf.data), true);

	*word = buf.data;

	return str;
}

static OuterInnerRels *
OuterInnerRelsCreate(char *name, List *outer_inner_list)
{
	OuterInnerRels *outer_inner;

	outer_inner = palloc(sizeof(OuterInnerRels));
	outer_inner->relation = name;
	outer_inner->outer_inner_pair = outer_inner_list;

	return outer_inner;
}

static const char *
parse_parentheses_Leading_in(const char *str, OuterInnerRels **outer_inner)
{
	List   *outer_inner_pair = NIL;

	if ((str = skip_parenthesis(str, '(')) == NULL)
		return NULL;

	skip_space(str);

	/* Store words in parentheses into outer_inner_list. */
	while(*str != ')' && *str != '\0')
	{
		OuterInnerRels *outer_inner_rels;

		if (*str == '(')
		{
			str = parse_parentheses_Leading_in(str, &outer_inner_rels);
			if (str == NULL)
				break;
		}
		else
		{
			char   *name;

			if ((str = parse_quoted_value(str, &name, true)) == NULL)
				break;
			else
				outer_inner_rels = OuterInnerRelsCreate(name, NIL);
		}

		outer_inner_pair = lappend(outer_inner_pair, outer_inner_rels);
		skip_space(str);
	}

	if (str == NULL ||
		(str = skip_parenthesis(str, ')')) == NULL)
	{
		list_free(outer_inner_pair);
		return NULL;
	}

	*outer_inner = OuterInnerRelsCreate(NULL, outer_inner_pair);

	return str;
}

static const char *
parse_parentheses_Leading(const char *str, List **name_list,
	OuterInnerRels **outer_inner)
{
	char   *name;
	bool	truncate = true;

	if ((str = skip_parenthesis(str, '(')) == NULL)
		return NULL;

	skip_space(str);
	if (*str =='(')
	{
		if ((str = parse_parentheses_Leading_in(str, outer_inner)) == NULL)
			return NULL;
	}
	else
	{
		/* Store words in parentheses into name_list. */
		while(*str != ')' && *str != '\0')
		{
			if ((str = parse_quoted_value(str, &name, truncate)) == NULL)
			{
				list_free(*name_list);
				return NULL;
			}

			*name_list = lappend(*name_list, name);
			skip_space(str);
		}
	}

	if ((str = skip_parenthesis(str, ')')) == NULL)
		return NULL;
	return str;
}

static const char *
parse_parentheses(const char *str, List **name_list, HintKeyword keyword)
{
	char   *name;
	bool	truncate = true;

	if ((str = skip_parenthesis(str, '(')) == NULL)
		return NULL;

	skip_space(str);

	/* Store words in parentheses into name_list. */
	while(*str != ')' && *str != '\0')
	{
		if ((str = parse_quoted_value(str, &name, truncate)) == NULL)
		{
			list_free(*name_list);
			return NULL;
		}

		*name_list = lappend(*name_list, name);
		skip_space(str);

		if (keyword == HINT_KEYWORD_INDEXSCANREGEXP ||
			keyword == HINT_KEYWORD_INDEXONLYSCANREGEXP ||
			keyword == HINT_KEYWORD_BITMAPSCANREGEXP ||
			keyword == HINT_KEYWORD_SET)
		{
			truncate = false;
		}
	}

	if ((str = skip_parenthesis(str, ')')) == NULL)
		return NULL;
	return str;
}

static void
parse_dispatch_hint(const char *str)
{
	StringInfoData buf;
	const char *head = NULL;
	const HintParser *parser;
	Hint *hint = NULL;

	head = (const char *) strcasestr(str, HINT_DISPATCH);
	if (head == NULL)
		return;

	initStringInfo(&buf);
	head = parse_keyword(head, &buf);

	for (parser = parsers; parser->keyword != NULL; parser++)
	{
		char *keyword = parser->keyword;

		if (pg_strcasecmp(buf.data, keyword) != 0)
			continue;

		Assert(pg_strcasecmp(keyword, HINT_DISPATCH) == 0);
		hint = parser->create_func(head, keyword, parser->hint_keyword);
		hint->parse_func(hint, NULL, NULL, head);
		/* only handle DirectDispatch hint here */
		break;
	}

	if (parser->keyword == NULL)
	{
		hint_ereport(head,
					 ("Unrecognized hint keyword \"%s\".", buf.data));
		pfree(buf.data);
		return;
	}

	if (hint != NULL)
		hint->delete_func(hint);
	pfree(buf.data);
}

static void
parse_hints(HintState *hstate, Query *parse, const char *str)
{
	StringInfoData	buf;
	char		   *head;

	initStringInfo(&buf);
	while (*str != '\0')
	{
		const HintParser *parser;

		/* in error message, we output the comment including the keyword. */
		head = (char *) str;

		/* parse only the keyword of the hint. */
		resetStringInfo(&buf);
		str = parse_keyword(str, &buf);

		for (parser = parsers; parser->keyword != NULL; parser++)
		{
			char   *keyword = parser->keyword;
			Hint   *hint;

			if (pg_strcasecmp(buf.data, keyword) != 0)
				continue;

			hint = parser->create_func(head, keyword, parser->hint_keyword);

			/* parser of each hint does parse in a parenthesis. */
			if ((str = hint->parse_func(hint, hstate, parse, str)) == NULL)
			{
				hint->delete_func(hint);
				pfree(buf.data);
				return;
			}

			/* Dispatch hint has been processed by parse_dispatch_hint, do not
			 * add it into HintState */
			if (pg_strcasecmp(keyword, HINT_DISPATCH) == 0)
			{
				hint->delete_func(hint);
				skip_space(str);
				break;
			}

			/*
			 * Add hint information into all_hints array.  If we don't have
			 * enough space, double the array.
			 */
			if (hstate->nall_hints == 0)
			{
				hstate->max_all_hints = HINT_ARRAY_DEFAULT_INITSIZE;
				hstate->all_hints = (Hint **)
					palloc(sizeof(Hint *) * hstate->max_all_hints);
			}
			else if (hstate->nall_hints == hstate->max_all_hints)
			{
				hstate->max_all_hints *= 2;
				hstate->all_hints = (Hint **)
					repalloc(hstate->all_hints,
							 sizeof(Hint *) * hstate->max_all_hints);
			}

			hstate->all_hints[hstate->nall_hints] = hint;
			hstate->nall_hints++;

			skip_space(str);

			break;
		}

		if (parser->keyword == NULL)
		{
			hint_ereport(head,
						 ("Unrecognized hint keyword \"%s\".", buf.data));
			pfree(buf.data);
			return;
		}
	}

	pfree(buf.data);
}


/*
 * Get hints from table by client-supplied query string and application name.
 */
static const char *
get_hints_from_table(const char *client_query, const char *client_application)
{
	const char *search_query =
		"SELECT hints "
		"  FROM hint_plan.hints "
		" WHERE norm_query_string = $1 "
		"   AND ( application_name = $2 "
		"    OR application_name = '' ) "
		" ORDER BY application_name DESC";
	static SPIPlanPtr plan = NULL;
	char   *hints = NULL;
	Oid		argtypes[2] = { TEXTOID, TEXTOID };
	Datum	values[2];
	char 	nulls[2] = {' ', ' '};
	text   *qry;
	text   *app;

	PG_TRY();
	{
		bool snapshot_set = false;

		hint_inhibit_level++;

		if (!ActiveSnapshotSet())
		{
			PushActiveSnapshot(GetTransactionSnapshot());
			snapshot_set = true;
		}

		SPI_connect();

		if (plan == NULL)
		{
			SPIPlanPtr	p;
			p = SPI_prepare(search_query, 2, argtypes);
			plan = SPI_saveplan(p);
			SPI_freeplan(p);
		}

		qry = cstring_to_text(client_query);
		app = cstring_to_text(client_application);
		values[0] = PointerGetDatum(qry);
		values[1] = PointerGetDatum(app);

		SPI_execute_plan(plan, values, nulls, true, 1);

		if (SPI_processed > 0)
		{
			char	*buf;

			hints = SPI_getvalue(SPI_tuptable->vals[0],
								 SPI_tuptable->tupdesc, 1);
			/*
			 * Here we use SPI_palloc to ensure that hints string is valid even
			 * after SPI_finish call.  We can't use simple palloc because it
			 * allocates memory in SPI's context and that context is deleted in
			 * SPI_finish.
			 */
			buf = SPI_palloc(strlen(hints) + 1);
			strcpy(buf, hints);
			hints = buf;
		}

		SPI_finish();

		if (snapshot_set)
			PopActiveSnapshot();

		hint_inhibit_level--;
	}
	PG_CATCH();
	{
		hint_inhibit_level--;
		PG_RE_THROW();
	}
	PG_END_TRY();

	return hints;
}

/*
 * Get client-supplied query string. Addtion to that the jumbled query is
 * supplied if the caller requested. From the restriction of JumbleQuery, some
 * kind of query needs special amendments. Reutrns NULL if this query doesn't
 * change the current hint. This function returns NULL also when something
 * wrong has happend and let the caller continue using the current hints.
 */
static const char *
get_query_string(ParseState *pstate, Query *query, Query **jumblequery)
{
	const char *p = debug_query_string;

	/*
	 * If debug_query_string is set, it is the top level statement. But in some
	 * cases we reach here with debug_query_string set NULL for example in the
	 * case of DESCRIBE message handling or EXECUTE command. We may still see a
	 * candidate top-level query in pstate in the case.
	 */
	if (pstate && pstate->p_sourcetext)
		p = pstate->p_sourcetext;

	/* We don't see a query string, return NULL */
	if (!p)
		return NULL;

	if (jumblequery != NULL)
		*jumblequery = query;

	if (query->commandType == CMD_UTILITY)
	{
		Query *target_query = (Query *)query->utilityStmt;

		/*
		 * Some CMD_UTILITY statements have a subquery that we can hint on.
		 * Since EXPLAIN can be placed before other kind of utility statements
		 * and EXECUTE can be contained other kind of utility statements, these
		 * conditions are not mutually exclusive and should be considered in
		 * this order.
		 */
		if (IsA(target_query, ExplainStmt))
		{
			ExplainStmt *stmt = (ExplainStmt *)target_query;

			Assert(IsA(stmt->query, Query));
			target_query = (Query *)stmt->query;

			/* strip out the top-level query for further processing */
			if (target_query->commandType == CMD_UTILITY &&
				target_query->utilityStmt != NULL)
				target_query = (Query *)target_query->utilityStmt;
		}

		if (IsA(target_query, DeclareCursorStmt))
		{
			DeclareCursorStmt *stmt = (DeclareCursorStmt *)target_query;
			Query *query = (Query *)stmt->query;

			/* the target must be CMD_SELECT in this case */
			Assert(IsA(query, Query) && query->commandType == CMD_SELECT);
			target_query = query;
		}

		if (IsA(target_query, CreateTableAsStmt))
		{
			CreateTableAsStmt  *stmt = (CreateTableAsStmt *) target_query;

			Assert(IsA(stmt->query, Query));
			target_query = (Query *) stmt->query;

			/* strip out the top-level query for further processing */
			if (target_query->commandType == CMD_UTILITY &&
				target_query->utilityStmt != NULL)
				target_query = (Query *)target_query->utilityStmt;
		}

		if (IsA(target_query, ExecuteStmt))
		{
			/*
			 * Use the prepared query for EXECUTE. The Query for jumble
			 * also replaced with the corresponding one.
			 */
			ExecuteStmt *stmt = (ExecuteStmt *)target_query;
			PreparedStatement  *entry;

			/*
			 * Silently ignore nonexistent prepared statements. This may happen
			 * for EXECUTE within a function definition.  Otherwise the
			 * execution will fail anyway.
			 */
			entry = FetchPreparedStatement(stmt->name, false);

			if (entry && entry->plansource->is_valid)
			{
				p = entry->plansource->query_string;
				target_query = (Query *) linitial (entry->plansource->query_list);
			}
			else
			{
				/* igonre the hint for EXECUTE if invalidated */
				p = NULL;
				target_query = NULL;
			}
		}

		/* JumbleQuery accespts only a non-utility Query */
		if (target_query &&
			(!IsA(target_query, Query) ||
			 target_query->utilityStmt != NULL))
			target_query = NULL;

		if (jumblequery)
			*jumblequery = target_query;
	}
	/*
	 * Return NULL if pstate is not of top-level query.  We don't need this
	 * when jumble info is not requested or cannot do this when pstate is NULL.
	 */
	else if (!jumblequery && pstate && pstate->p_sourcetext != p &&
			 strcmp(pstate->p_sourcetext, p) != 0)
		p = NULL;

	return p;
}

/*
 * Get hints from the head block comment in client-supplied query string.
 */
static const char *
get_hints_from_comment(const char *p)
{
	const char *hint_head;
	char	   *head;
	char	   *tail;
	int			len;

	if (p == NULL)
		return NULL;

	/* extract query head comment. */
	hint_head = strstr(p, HINT_START);
	if (hint_head == NULL)
		return NULL;
	for (;p < hint_head; p++)
	{
		/*
		 * Allow these characters precedes hint comment:
		 *   - digits
		 *   - alphabets which are in ASCII range
		 *   - space, tabs and new-lines
		 *   - underscores, for identifier
		 *   - commas, for SELECT clause, EXPLAIN and PREPARE
		 *   - parentheses, for EXPLAIN and PREPARE
		 *
		 * Note that we don't use isalpha() nor isalnum() in ctype.h here to
		 * avoid behavior which depends on locale setting.
		 */
		if (!(*p >= '0' && *p <= '9') &&
			!(*p >= 'A' && *p <= 'Z') &&
			!(*p >= 'a' && *p <= 'z') &&
			!isspace(*p) &&
			*p != '_' &&
			*p != ',' &&
			*p != '(' && *p != ')')
			return NULL;
	}

	len = strlen(HINT_START);
	head = (char *) p;
	p += len;
	skip_space(p);

	/* find hint end keyword. */
	if ((tail = strstr(p, HINT_END)) == NULL)
	{
		hint_ereport(head, ("Unterminated block comment."));
		return NULL;
	}

	/* We don't support nested block comments. */
	if ((head = strstr(p, BLOCK_COMMENT_START)) != NULL && head < tail)
	{
		hint_ereport(head, ("Nested block comments are not supported."));
		return NULL;
	}

	/* Make a copy of hint. */
	len = tail - p;
	head = palloc(len + 1);
	memcpy(head, p, len);
	head[len] = '\0';
	p = head;

	return p;
}

/*
 * Parse hints that got, create hint struct from parse tree and parse hints.
 */
static HintState *
create_hintstate(Query *parse, const char *hints)
{
	const char *p;
	int			i;
	HintState   *hstate;

	if (hints == NULL)
		return NULL;

	/* -1 means that no Parallel hint is specified. */
	max_hint_nworkers = -1;

	p = hints;
	hstate = HintStateCreate();
	hstate->hint_str = (char *) hints;

	/* parse each hint. */
	parse_hints(hstate, parse, p);

	/* When nothing specified a hint, we free HintState and returns NULL. */
	if (hstate->nall_hints == 0)
	{
		HintStateDelete(hstate);
		return NULL;
	}

	/* Sort hints in order of original position. */
	qsort(hstate->all_hints, hstate->nall_hints, sizeof(Hint *),
		  HintCmpWithPos);

	/* Count number of hints per hint-type. */
	for (i = 0; i < hstate->nall_hints; i++)
	{
		Hint   *cur_hint = hstate->all_hints[i];
		hstate->num_hints[cur_hint->type]++;
	}

	/*
	 * If an object (or a set of objects) has multiple hints of same hint-type,
	 * only the last hint is valid and others are ignored in planning.
	 * Hints except the last are marked as 'duplicated' to remember the order.
	 */
	for (i = 0; i < hstate->nall_hints - 1; i++)
	{
		Hint   *cur_hint = hstate->all_hints[i];
		Hint   *next_hint = hstate->all_hints[i + 1];

		/*
		 * Leading hint is marked as 'duplicated' in transform_join_hints.
		 */
		if (cur_hint->type == HINT_TYPE_LEADING &&
			next_hint->type == HINT_TYPE_LEADING)
			continue;

		/*
		 * Note that we need to pass addresses of hint pointers, because
		 * HintCmp is designed to sort array of Hint* by qsort.
		 */
		if (HintCmp(&cur_hint, &next_hint) == 0)
		{
			hint_ereport(cur_hint->hint_str,
						 ("Conflict %s hint.", HintTypeName[cur_hint->type]));
			cur_hint->state = HINT_STATE_DUPLICATION;
		}
	}

	/*
	 * Make sure that per-type array pointers point proper position in the
	 * array which consists of all hints.
	 */
	hstate->scan_hints = (ScanMethodHint **) hstate->all_hints;
	hstate->join_hints = (JoinMethodHint **) (hstate->scan_hints +
		hstate->num_hints[HINT_TYPE_SCAN_METHOD]);
	hstate->leading_hint = (LeadingHint **) (hstate->join_hints +
		hstate->num_hints[HINT_TYPE_JOIN_METHOD]);
	hstate->set_hints = (SetHint **) (hstate->leading_hint +
		hstate->num_hints[HINT_TYPE_LEADING]);
	hstate->rows_hints = (RowsHint **) (hstate->set_hints +
		hstate->num_hints[HINT_TYPE_SET]);
	hstate->parallel_hints = (ParallelHint **) (hstate->rows_hints +
		hstate->num_hints[HINT_TYPE_ROWS]);
	hstate->motion_hints = (MotionHint **) (hstate->parallel_hints +
		hstate->num_hints[HINT_TYPE_PARALLEL]);

	return hstate;
}

/*
 * Parse inside of parentheses of scan-method hints.
 */
static const char *
ScanMethodHintParse(ScanMethodHint *hint, HintState *hstate, Query *parse,
					const char *str)
{
	const char	   *keyword = hint->base.keyword;
	HintKeyword		hint_keyword = hint->base.hint_keyword;
	List		   *name_list = NIL;
	int				length;

	if ((str = parse_parentheses(str, &name_list, hint_keyword)) == NULL)
		return NULL;

	/* Parse relation name and index name(s) if given hint accepts. */
	length = list_length(name_list);

	/* at least twp parameters required */
	if (length < 1)
	{
		hint_ereport(str,
					 ("%s hint requires a relation.",  hint->base.keyword));
		hint->base.state = HINT_STATE_ERROR;
		return str;
	}

	hint->relname = linitial(name_list);
	hint->indexnames = list_delete_first(name_list);

	/* check whether the hint accepts index name(s) */
	if (length > 1 && !SCAN_HINT_ACCEPTS_INDEX_NAMES(hint_keyword))
	{
		hint_ereport(str,
					 ("%s hint accepts only one relation.",
					  hint->base.keyword));
		hint->base.state = HINT_STATE_ERROR;
		return str;
	}

	/* Set a bit for specified hint. */
	switch (hint_keyword)
	{
		case HINT_KEYWORD_SEQSCAN:
			hint->enforce_mask = ENABLE_SEQSCAN;
			break;
		case HINT_KEYWORD_INDEXSCAN:
			hint->enforce_mask = ENABLE_INDEXSCAN;
			break;
		case HINT_KEYWORD_INDEXSCANREGEXP:
			hint->enforce_mask = ENABLE_INDEXSCAN;
			hint->regexp = true;
			break;
		case HINT_KEYWORD_BITMAPSCAN:
			hint->enforce_mask = ENABLE_BITMAPSCAN;
			break;
		case HINT_KEYWORD_BITMAPSCANREGEXP:
			hint->enforce_mask = ENABLE_BITMAPSCAN;
			hint->regexp = true;
			break;
		case HINT_KEYWORD_TIDSCAN:
			hint->enforce_mask = ENABLE_TIDSCAN;
			break;
		case HINT_KEYWORD_NOSEQSCAN:
			hint->enforce_mask = ENABLE_ALL_SCAN ^ ENABLE_SEQSCAN;
			break;
		case HINT_KEYWORD_NOINDEXSCAN:
			hint->enforce_mask = ENABLE_ALL_SCAN ^ ENABLE_INDEXSCAN;
			break;
		case HINT_KEYWORD_NOBITMAPSCAN:
			hint->enforce_mask = ENABLE_ALL_SCAN ^ ENABLE_BITMAPSCAN;
			break;
		case HINT_KEYWORD_NOTIDSCAN:
			hint->enforce_mask = ENABLE_ALL_SCAN ^ ENABLE_TIDSCAN;
			break;
		case HINT_KEYWORD_INDEXONLYSCAN:
			hint->enforce_mask = ENABLE_INDEXSCAN | ENABLE_INDEXONLYSCAN;
			break;
		case HINT_KEYWORD_INDEXONLYSCANREGEXP:
			hint->enforce_mask = ENABLE_INDEXSCAN | ENABLE_INDEXONLYSCAN;
			hint->regexp = true;
			break;
		case HINT_KEYWORD_NOINDEXONLYSCAN:
			hint->enforce_mask = ENABLE_ALL_SCAN ^ ENABLE_INDEXONLYSCAN;
			break;
		default:
			hint_ereport(str, ("Unrecognized hint keyword \"%s\".", keyword));
			return NULL;
			break;
	}

	return str;
}

static const char *
JoinMethodHintParse(JoinMethodHint *hint, HintState *hstate, Query *parse,
					const char *str)
{
	const char	   *keyword = hint->base.keyword;
	HintKeyword		hint_keyword = hint->base.hint_keyword;
	List		   *name_list = NIL;

	if ((str = parse_parentheses(str, &name_list, hint_keyword)) == NULL)
		return NULL;

	hint->nrels = list_length(name_list);

	if (hint->nrels > 0)
	{
		ListCell   *l;
		int			i = 0;

		/*
		 * Transform relation names from list to array to sort them with qsort
		 * after.
		 */
		hint->relnames = palloc(sizeof(char *) * hint->nrels);
		foreach (l, name_list)
		{
			hint->relnames[i] = lfirst(l);
			i++;
		}
	}

	list_free(name_list);

	/* A join hint requires at least two relations */
	if (hint->nrels < 2)
	{
		hint_ereport(str,
					 ("%s hint requires at least two relations.",
					  hint->base.keyword));
		hint->base.state = HINT_STATE_ERROR;
		return str;
	}

	/* Sort hints in alphabetical order of relation names. */
	qsort(hint->relnames, hint->nrels, sizeof(char *), RelnameCmp);

	switch (hint_keyword)
	{
		case HINT_KEYWORD_NESTLOOP:
			hint->enforce_mask = ENABLE_NESTLOOP;
			break;
		case HINT_KEYWORD_MERGEJOIN:
			hint->enforce_mask = ENABLE_MERGEJOIN;
			break;
		case HINT_KEYWORD_HASHJOIN:
			hint->enforce_mask = ENABLE_HASHJOIN;
			break;
		case HINT_KEYWORD_NONESTLOOP:
			hint->enforce_mask = ENABLE_ALL_JOIN ^ ENABLE_NESTLOOP;
			break;
		case HINT_KEYWORD_NOMERGEJOIN:
			hint->enforce_mask = ENABLE_ALL_JOIN ^ ENABLE_MERGEJOIN;
			break;
		case HINT_KEYWORD_NOHASHJOIN:
			hint->enforce_mask = ENABLE_ALL_JOIN ^ ENABLE_HASHJOIN;
			break;
		default:
			hint_ereport(str, ("Unrecognized hint keyword \"%s\".", keyword));
			return NULL;
			break;
	}

	return str;
}

static bool
OuterInnerPairCheck(OuterInnerRels *outer_inner)
{
	ListCell *l;
	if (outer_inner->outer_inner_pair == NIL)
	{
		if (outer_inner->relation)
			return true;
		else
			return false;
	}

	if (list_length(outer_inner->outer_inner_pair) == 2)
	{
		foreach(l, outer_inner->outer_inner_pair)
		{
			if (!OuterInnerPairCheck(lfirst(l)))
				return false;
		}
	}
	else
		return false;

	return true;
}

static List *
OuterInnerList(OuterInnerRels *outer_inner)
{
	List		   *outer_inner_list = NIL;
	ListCell	   *l;
	OuterInnerRels *outer_inner_rels;

	foreach(l, outer_inner->outer_inner_pair)
	{
		outer_inner_rels = (OuterInnerRels *)(lfirst(l));

		if (outer_inner_rels->relation != NULL)
			outer_inner_list = lappend(outer_inner_list,
									   outer_inner_rels->relation);
		else
			outer_inner_list = list_concat(outer_inner_list,
										   OuterInnerList(outer_inner_rels));
	}
	return outer_inner_list;
}

static const char *
LeadingHintParse(LeadingHint *hint, HintState *hstate, Query *parse,
				 const char *str)
{
	List		   *name_list = NIL;
	OuterInnerRels *outer_inner = NULL;

	if ((str = parse_parentheses_Leading(str, &name_list, &outer_inner)) ==
		NULL)
		return NULL;

	if (outer_inner != NULL)
		name_list = OuterInnerList(outer_inner);

	hint->relations = name_list;
	hint->outer_inner = outer_inner;

	/* A Leading hint requires at least two relations */
	if ( hint->outer_inner == NULL && list_length(hint->relations) < 2)
	{
		hint_ereport(hint->base.hint_str,
					 ("%s hint requires at least two relations.",
					  HINT_LEADING));
		hint->base.state = HINT_STATE_ERROR;
	}
	else if (hint->outer_inner != NULL &&
			 !OuterInnerPairCheck(hint->outer_inner))
	{
		hint_ereport(hint->base.hint_str,
					 ("%s hint requires two sets of relations when parentheses nests.",
					  HINT_LEADING));
		hint->base.state = HINT_STATE_ERROR;
	}

	return str;
}

static const char *
SetHintParse(SetHint *hint, HintState *hstate, Query *parse, const char *str)
{
	List   *name_list = NIL;

	if ((str = parse_parentheses(str, &name_list, hint->base.hint_keyword))
		== NULL)
		return NULL;

	hint->words = name_list;

	/* We need both name and value to set GUC parameter. */
	if (list_length(name_list) == 2)
	{
		hint->name = linitial(name_list);
		hint->value = lsecond(name_list);
	}
	else
	{
		hint_ereport(hint->base.hint_str,
					 ("%s hint requires name and value of GUC parameter.",
					  HINT_SET));
		hint->base.state = HINT_STATE_ERROR;
	}

	return str;
}

static const char *
RowsHintParse(RowsHint *hint, HintState *hstate, Query *parse,
			  const char *str)
{
	HintKeyword		hint_keyword = hint->base.hint_keyword;
	List		   *name_list = NIL;
	char		   *rows_str;
	char		   *end_ptr;
	ListCell   *l;
	int			i = 0;

	if ((str = parse_parentheses(str, &name_list, hint_keyword)) == NULL)
		return NULL;

	/* Last element must be rows specification */
	hint->nrels = list_length(name_list) - 1;

	if (hint->nrels < 1)
	{
		hint_ereport(str,
					 ("%s hint needs at least one relation followed by one correction term.",
					  hint->base.keyword));
		hint->base.state = HINT_STATE_ERROR;

		return str;
	}

	/*
	 * Transform relation names from list to array to sort them with qsort
	 * after.
	 */
	hint->relnames = palloc(sizeof(char *) * hint->nrels);
	foreach (l, name_list)
	{
		if (hint->nrels <= i)
			break;
		hint->relnames[i] = lfirst(l);
		i++;
	}

	/* Retieve rows estimation */
	rows_str = list_nth(name_list, hint->nrels);
	hint->rows_str = rows_str;		/* store as-is for error logging */
	if (rows_str[0] == '#')
	{
		hint->value_type = RVT_ABSOLUTE;
		rows_str++;
	}
	else if (rows_str[0] == '+')
	{
		hint->value_type = RVT_ADD;
		rows_str++;
	}
	else if (rows_str[0] == '-')
	{
		hint->value_type = RVT_SUB;
		rows_str++;
	}
	else if (rows_str[0] == '*')
	{
		hint->value_type = RVT_MULTI;
		rows_str++;
	}
	else
	{
		hint_ereport(rows_str, ("Unrecognized rows value type notation."));
		hint->base.state = HINT_STATE_ERROR;
		return str;
	}
	hint->rows = strtod(rows_str, &end_ptr);
	if (*end_ptr)
	{
		hint_ereport(rows_str,
					 ("%s hint requires valid number as rows estimation.",
					  hint->base.keyword));
		hint->base.state = HINT_STATE_ERROR;
		return str;
	}

	/* A join hint requires at least two relations */
	if (hint->nrels < 2)
	{
		hint_ereport(str,
					 ("%s hint requires at least two relations.",
					  hint->base.keyword));
		hint->base.state = HINT_STATE_ERROR;
		return str;
	}

	list_free(name_list);

	/* Sort relnames in alphabetical order. */
	qsort(hint->relnames, hint->nrels, sizeof(char *), RelnameCmp);

	return str;
}

static const char *
ParallelHintParse(ParallelHint *hint, HintState *hstate, Query *parse,
				  const char *str)
{
	HintKeyword		hint_keyword = hint->base.hint_keyword;
	List		   *name_list = NIL;
	int				length;
	char   *end_ptr;
	int		nworkers;
	bool	force_parallel = false;

	if ((str = parse_parentheses(str, &name_list, hint_keyword)) == NULL)
		return NULL;

	/* Parse relation name and index name(s) if given hint accepts. */
	length = list_length(name_list);

	if (length < 2 || length > 3)
	{
		hint_ereport(")",
					 ("wrong number of arguments (%d): %s",
					  length,  hint->base.keyword));
		hint->base.state = HINT_STATE_ERROR;
		return str;
	}

	hint->relname = linitial(name_list);

	/* The second parameter is number of workers */
	hint->nworkers_str = list_nth(name_list, 1);
	nworkers = strtod(hint->nworkers_str, &end_ptr);
	if (*end_ptr || nworkers < 0 || nworkers > max_worker_processes)
	{
		if (*end_ptr)
			hint_ereport(hint->nworkers_str,
						 ("number of workers must be a number: %s",
						  hint->base.keyword));
		else if (nworkers < 0)
			hint_ereport(hint->nworkers_str,
						 ("number of workers must be positive: %s",
						  hint->base.keyword));
		else if (nworkers > max_worker_processes)
			hint_ereport(hint->nworkers_str,
						 ("number of workers = %d is larger than max_worker_processes(%d): %s",
						  nworkers, max_worker_processes, hint->base.keyword));

		hint->base.state = HINT_STATE_ERROR;
	}

	hint->nworkers = nworkers;

	/* optional third parameter is specified */
	if (length == 3)
	{
		const char *modeparam = (const char *)list_nth(name_list, 2);
		if (pg_strcasecmp(modeparam, "hard") == 0)
			force_parallel = true;
		else if (pg_strcasecmp(modeparam, "soft") != 0)
		{
			hint_ereport(modeparam,
						 ("enforcement must be soft or hard: %s",
							 hint->base.keyword));
			hint->base.state = HINT_STATE_ERROR;
		}
	}

	hint->force_parallel = force_parallel;

	if (hint->base.state != HINT_STATE_ERROR &&
		nworkers > max_hint_nworkers)
		max_hint_nworkers = nworkers;

	return str;
}

static const char *
DispatchHintParse(DispatchHint *hint, HintState *hstate, Query *parse,
					const char *str)
{
	List *words = NIL;

	if ((str = parse_parentheses(str, &words, hint->base.hint_keyword)) == NULL)
		return NULL;

	if (list_length(words) <= 1)
	{
		list_free(words);
		return NULL;
	}

	direct_dispatch_hint = words;
	return str;
}

/*
 * Parse inside of parentheses of motion hints.
 */
static const char *
MotionHintParse(MotionHint *hint, HintState *hstate, Query *parse,
					const char *str)
{
	const char  *keyword = hint->base.keyword;
	HintKeyword  hint_keyword = hint->base.hint_keyword;
	List	    *name_list = NIL;
	int		     length;

	if ((str = parse_parentheses(str, &name_list, hint_keyword)) == NULL)
		return NULL;

	/* Parse relation name and index name(s) if given hint accepts. */
	length = list_length(name_list);

	/* at least twp parameters required */
	if (length != 1)
	{
		hint_ereport(str,
					 ("%s hint requires a relation.",  hint->base.keyword));
		hint->base.state = HINT_STATE_ERROR;
		return str;
	}

	hint->relname = linitial(name_list);

	/* Set a bit for specified hint. */
	switch (hint_keyword)
	{
		case HINT_KEYWORD_DISABLEBORADCASTMOTION:
			hint->enforce_mask = ENABLE_REDISTRIBUTEMOTION;
			break;
		case HINT_KEYWORD_DISABLE_REDISTRIBUTEMOTION:
			hint->enforce_mask = ENABLE_BROADCASTMOTION;
			break;
		default:
			hint_ereport(str, ("Unrecognized hint keyword \"%s\".", keyword));
			return NULL;
			break;
	}

	return str;
}

/*
 * set GUC parameter functions
 */

static int
get_current_scan_mask()
{
	int mask = 0;

	if (enable_seqscan)
		mask |= ENABLE_SEQSCAN;
	if (enable_indexscan)
		mask |= ENABLE_INDEXSCAN;
	if (enable_bitmapscan)
		mask |= ENABLE_BITMAPSCAN;
	if (enable_tidscan)
		mask |= ENABLE_TIDSCAN;
	if (enable_indexonlyscan)
		mask |= ENABLE_INDEXONLYSCAN;

	return mask;
}

static int
get_current_join_mask()
{
	int mask = 0;

	if (enable_nestloop)
		mask |= ENABLE_NESTLOOP;
	if (enable_mergejoin)
		mask |= ENABLE_MERGEJOIN;
	if (enable_hashjoin)
		mask |= ENABLE_HASHJOIN;

	return mask;
}

/*
 * Sets GUC prameters without throwing exception. Reutrns false if something
 * wrong.
 */
static int
set_config_option_noerror(const char *name, const char *value,
						  GucContext context, GucSource source,
						  GucAction action, bool changeVal, int elevel)
{
	int				result = 0;
	MemoryContext	ccxt = CurrentMemoryContext;

	PG_TRY();
	{
		result = set_config_option(name, value, context, source,
								   action, changeVal, 0, false);
	}
	PG_CATCH();
	{
		ErrorData	   *errdata;

		/* Save error info */
		MemoryContextSwitchTo(ccxt);
		errdata = CopyErrorData();
		FlushErrorState();

		ereport(elevel,
				(errcode(errdata->sqlerrcode),
				 errmsg("%s", errdata->message),
				 errdata->detail ? errdetail("%s", errdata->detail) : 0,
				 errdata->hint ? errhint("%s", errdata->hint) : 0));
		msgqno = qno;
		FreeErrorData(errdata);
	}
	PG_END_TRY();

	return result;
}

/*
 * Sets GUC parameter of int32 type without throwing exceptions. Returns false
 * if something wrong.
 */
static int
set_config_int32_option(const char *name, int32 value, GucContext context)
{
	char buf[16];	/* enough for int32 */

	if (snprintf(buf, 16, "%d", value) < 0)
	{
		ereport(pg_hint_plan_parse_message_level,
				(errmsg ("Failed to convert integer to string: %d", value)));
		return false;
	}

	return
		set_config_option_noerror(name, buf, context,
								  PGC_S_SESSION, GUC_ACTION_SAVE, true,
								  pg_hint_plan_parse_message_level);
}

/*
 * Sets GUC parameter of double type without throwing exceptions. Returns false
 * if something wrong.
 */
static int
set_config_double_option(const char *name, double value, GucContext context)
{
	char *buf = float8out_internal(value);
	int	  result;

	result = set_config_option_noerror(name, buf, context,
									   PGC_S_SESSION, GUC_ACTION_SAVE, true,
									   pg_hint_plan_parse_message_level);
	pfree(buf);
	return result;
}

/* setup scan method enforcement according to given options */
static void
setup_guc_enforcement(SetHint **options, int noptions, GucContext context)
{
	int	i;

	for (i = 0; i < noptions; i++)
	{
		SetHint	   *hint = options[i];
		int			result;

		if (!hint_state_enabled(hint))
			continue;

		result = set_config_option_noerror(hint->name, hint->value, context,
										   PGC_S_SESSION, GUC_ACTION_SAVE, true,
										   pg_hint_plan_parse_message_level);
		if (result != 0)
			hint->base.state = HINT_STATE_USED;
		else
			hint->base.state = HINT_STATE_ERROR;
	}

	return;
}

/*
 * Setup parallel execution environment.
 *
 * If hint is not NULL, set up using it, elsewise reset to initial environment.
 */
static void
setup_parallel_plan_enforcement(ParallelHint *hint, HintState *state)
{
	if (hint)
	{
		hint->base.state = HINT_STATE_USED;
		set_config_int32_option("max_parallel_workers_per_gather",
								hint->nworkers, state->context);
	}
	else
		set_config_int32_option("max_parallel_workers_per_gather",
								state->init_nworkers, state->context);

	/* force means that enforce parallel as far as possible */
	if (hint && hint->force_parallel && hint->nworkers > 0)
	{
		set_config_double_option("parallel_tuple_cost", 0.0, state->context);
		set_config_double_option("parallel_setup_cost", 0.0, state->context);
		set_config_int32_option("min_parallel_table_scan_size", 0,
								state->context);
		set_config_int32_option("min_parallel_index_scan_size", 0,
								state->context);
	}
	else
	{
		set_config_double_option("parallel_tuple_cost",
								state->init_paratup_cost, state->context);
		set_config_double_option("parallel_setup_cost",
								state->init_parasetup_cost, state->context);
		set_config_int32_option("min_parallel_table_scan_size",
								state->init_min_para_tablescan_size,
								state->context);
		set_config_int32_option("min_parallel_index_scan_size",
								state->init_min_para_indexscan_size,
								state->context);
	}
}

#define SET_CONFIG_OPTION(name, type_bits) \
	set_config_option_noerror((name), \
		(mask & (type_bits)) ? "true" : "false", \
		context, PGC_S_SESSION, GUC_ACTION_SAVE, true, ERROR)


/*
 * Setup GUC environment to enforce scan methods. If scanhint is NULL, reset
 * GUCs to the saved state in state.
 */
static void
setup_scan_method_enforcement(ScanMethodHint *scanhint, HintState *state)
{
	unsigned char	enforce_mask = state->init_scan_mask;
	GucContext		context = state->context;
	unsigned char	mask;

	if (scanhint)
	{
		enforce_mask = scanhint->enforce_mask;
		scanhint->base.state = HINT_STATE_USED;
	}

	if (enforce_mask == ENABLE_SEQSCAN || enforce_mask == ENABLE_INDEXSCAN ||
		enforce_mask == ENABLE_BITMAPSCAN || enforce_mask == ENABLE_TIDSCAN
		|| enforce_mask == (ENABLE_INDEXSCAN | ENABLE_INDEXONLYSCAN)
		)
		mask = enforce_mask;
	else
		mask = enforce_mask & current_hint_state->init_scan_mask;

	SET_CONFIG_OPTION("enable_seqscan", ENABLE_SEQSCAN);
	SET_CONFIG_OPTION("enable_indexscan", ENABLE_INDEXSCAN);
	SET_CONFIG_OPTION("enable_bitmapscan", ENABLE_BITMAPSCAN);
	SET_CONFIG_OPTION("enable_tidscan", ENABLE_TIDSCAN);
	SET_CONFIG_OPTION("enable_indexonlyscan", ENABLE_INDEXONLYSCAN);
}

static void
set_motion_config_options(unsigned char enforce_mask, GucContext context)
{
	unsigned char	mask;

	if (enforce_mask == ENABLE_BROADCASTMOTION ||
		enforce_mask == ENABLE_REDISTRIBUTEMOTION)
		mask = enforce_mask;
	else
		mask = ENABLE_ALL_MOTION;

	SET_CONFIG_OPTION("enable_broadcast_motion", ENABLE_BROADCASTMOTION);
	pg_hint_plan_enable_redistribute_motion = (mask & (ENABLE_REDISTRIBUTEMOTION));
}

static void
set_motion_config_options_for_rel(PlannerInfo *root, RelOptInfo *rel)
{
	if (rel->reloptkind != RELOPT_BASEREL)
		return;

	MotionHint *hint = NULL;
    hint = find_motion_hint(root, rel->relid);
	if (hint)
		set_motion_config_options(hint->enforce_mask, current_hint_state->context);
}

static void
set_join_config_options(unsigned char enforce_mask, GucContext context)
{
	unsigned char	mask;

	if (enforce_mask == ENABLE_NESTLOOP || enforce_mask == ENABLE_MERGEJOIN ||
		enforce_mask == ENABLE_HASHJOIN)
		mask = enforce_mask;
	else
		mask = enforce_mask & current_hint_state->init_join_mask;

	SET_CONFIG_OPTION("enable_nestloop", ENABLE_NESTLOOP);
	SET_CONFIG_OPTION("enable_mergejoin", ENABLE_MERGEJOIN);
	SET_CONFIG_OPTION("enable_hashjoin", ENABLE_HASHJOIN);

	/*
	 * Hash join may be rejected for the reason of estimated memory usage. Try
	 * getting rid of that limitation. This change on work_mem is reverted just
	 * after searching join path so no suginificant side-effects are expected.
	 */
	if (enforce_mask == ENABLE_HASHJOIN)
	{
		char			buf[32];

		/* See final_cost_hashjoin(). */
		if (work_mem < MAX_KILOBYTES)
		{
			snprintf(buf, sizeof(buf), UINT64_FORMAT, (uint64)MAX_KILOBYTES);
			ignore_deprecated_guc_warning = true;
			set_config_option_noerror("work_mem", buf,
									  context, PGC_S_SESSION, GUC_ACTION_SAVE,
									  true, ERROR);
			ignore_deprecated_guc_warning = false;
		}
	}
}

/*
 * Push a hint into hint stack which is implemented with List struct.  Head of
 * list is top of stack.
 */
static void
push_hint(HintState *hstate)
{
	/* Prepend new hint to the list means pushing to stack. */
	HintStateStack = lcons(hstate, HintStateStack);

	/* Pushed hint is the one which should be used hereafter. */
	current_hint_state = hstate;
}

/* Pop a hint from hint stack.  Popped hint is automatically discarded. */
static void
pop_hint(void)
{
	/* Hint stack must not be empty. */
	if(HintStateStack == NIL)
		elog(ERROR, "hint stack is empty");

	/*
	 * Take a hint at the head from the list, and free it.  Switch
	 * current_hint_state to point new head (NULL if the list is empty).
	 */
	HintStateStack = list_delete_first(HintStateStack);
	HintStateDelete(current_hint_state);
	if(HintStateStack == NIL)
		current_hint_state = NULL;
	else
		current_hint_state = (HintState *) lfirst(list_head(HintStateStack));
}

/*
 * Retrieve and store hint string from given query or from the hint table.
 */
static void
get_current_hint_string(ParseState *pstate, Query *query)
{
	const char *query_str;
	MemoryContext	oldcontext;

	/* do nothing under hint table search */
	if (hint_inhibit_level > 0)
		return;

	/* We alredy have one, don't parse it again. */
	if (current_hint_retrieved)
		return;

	/* Don't parse the current query hereafter */
	current_hint_retrieved = true;

	if (!pg_hint_plan_enable_hint)
	{
		if (current_hint_str)
		{
			pfree((void *)current_hint_str);
			current_hint_str = NULL;
		}
		return;
	}

	/* increment the query number */
	qnostr[0] = 0;
	if (debug_level > 1)
		snprintf(qnostr, sizeof(qnostr), "[qno=0x%x]", qno++);
	qno++;

	/* search the hint table for a hint if requested */
	if (pg_hint_plan_enable_hint_table)
	{
		int				query_len;
		pgssJumbleState	jstate;
		Query		   *jumblequery;
		char		   *normalized_query = NULL;

		query_str = get_query_string(pstate, query, &jumblequery);

		/* If this query is not for hint, just return */
		if (!query_str)
			return;

		/* clear the previous hint string */
		if (current_hint_str)
		{
			pfree((void *)current_hint_str);
			current_hint_str = NULL;
		}

		if (jumblequery)
		{
			/*
			 * XXX: normalization code is copied from pg_stat_statements.c.
			 * Make sure to keep up-to-date with it.
			 */
			jstate.jumble = (unsigned char *) palloc(JUMBLE_SIZE);
			jstate.jumble_len = 0;
			jstate.clocations_buf_size = 32;
			jstate.clocations = (pgssLocationLen *)
				palloc(jstate.clocations_buf_size * sizeof(pgssLocationLen));
			jstate.clocations_count = 0;

			JumbleQuery(&jstate, jumblequery);

			/*
			 * Normalize the query string by replacing constants with '?'
			 */
			/*
			 * Search hint string which is stored keyed by query string
			 * and application name.  The query string is normalized to allow
			 * fuzzy matching.
			 *
			 * Adding 1 byte to query_len ensures that the returned string has
			 * a terminating NULL.
			 */
			query_len = strlen(query_str) + 1;
			normalized_query =
				generate_normalized_query(&jstate, query_str, 0, &query_len,
										  GetDatabaseEncoding());

			/*
			 * find a hint for the normalized query. the result should be in
			 * TopMemoryContext
			 */
			oldcontext = MemoryContextSwitchTo(TopMemoryContext);
			current_hint_str =
				get_hints_from_table(normalized_query, application_name);
			MemoryContextSwitchTo(oldcontext);

			if (debug_level > 1)
			{
				if (current_hint_str)
					ereport(pg_hint_plan_debug_message_level,
							(errmsg("pg_hint_plan[qno=0x%x]: "
									"post_parse_analyze_hook: "
									"hints from table: \"%s\": "
									"normalized_query=\"%s\", "
									"application name =\"%s\"",
									qno, current_hint_str,
									normalized_query, application_name),
							 errhidestmt(msgqno != qno),
							 errhidecontext(msgqno != qno)));
				else
					ereport(pg_hint_plan_debug_message_level,
							(errmsg("pg_hint_plan[qno=0x%x]: "
									"no match found in table:  "
									"application name = \"%s\", "
									"normalized_query=\"%s\"",
									qno, application_name,
									normalized_query),
							 errhidestmt(msgqno != qno),
							 errhidecontext(msgqno != qno)));

				msgqno = qno;
			}
		}

		/* retrun if we have hint here */
		if (current_hint_str)
			return;
	}
	else
		query_str = get_query_string(pstate, query, NULL);

	if (query_str)
	{
		/*
		 * get hints from the comment. However we may have the same query
		 * string with the previous call, but the extra comparison seems no
		 * use..
		 */
		if (current_hint_str)
			pfree((void *)current_hint_str);

		oldcontext = MemoryContextSwitchTo(TopMemoryContext);
		current_hint_str = get_hints_from_comment(query_str);
		MemoryContextSwitchTo(oldcontext);
	}
	else
	{
		/*
		 * Failed to get query. We would be in fetching invalidated
		 * plancache. Try the next chance.
		 */
		current_hint_retrieved = false;
	}

	if (debug_level > 1)
	{
		if (debug_level == 1 && query_str && debug_query_string &&
			strcmp(query_str, debug_query_string))
			ereport(pg_hint_plan_debug_message_level,
					(errmsg("hints in comment=\"%s\"",
							current_hint_str ? current_hint_str : "(none)"),
					 errhidestmt(msgqno != qno),
					 errhidecontext(msgqno != qno)));
		else
			ereport(pg_hint_plan_debug_message_level,
					(errmsg("hints in comment=\"%s\", query=\"%s\", debug_query_string=\"%s\"",
							current_hint_str ? current_hint_str : "(none)",
							query_str ? query_str : "(none)",
							debug_query_string ? debug_query_string : "(none)"),
					 errhidestmt(msgqno != qno),
					 errhidecontext(msgqno != qno)));
		msgqno = qno;
	}
}

static void
pg_hint_plan_post_parse(List *parsetrees, const char *str)
{
	const char *hint_str = NULL;

	if (prev_post_parse_hook)
		prev_post_parse_hook(parsetrees, str);

	if (!pg_hint_plan_enable_hint)
		return;

	if (list_length(parsetrees) != 1)
		return;

	if (direct_dispatch_hint != NIL)
		return;

	/* get hints from the comment */
	hint_str = get_hints_from_comment(str);
	if (hint_str == NULL)
		return;

	parse_dispatch_hint(hint_str);
}

/*
 * Retrieve hint string from the current query.
 */
static void
pg_hint_plan_post_parse_analyze(ParseState *pstate, Query *query)
{
	if (prev_post_parse_analyze_hook)
		prev_post_parse_analyze_hook(pstate, query);

	/* always retrieve hint from the top-level query string */
	if (plpgsql_recurse_level == 0)
		current_hint_retrieved = false;

	get_current_hint_string(pstate, query);
}

/*
 * We need to reset current_hint_retrieved flag always when a command execution
 * is finished. This is true even for a pure utility command that doesn't
 * involve planning phase.
 */
static void
pg_hint_plan_ProcessUtility(PlannedStmt *pstmt, const char *queryString,
					ProcessUtilityContext context,
					ParamListInfo params, QueryEnvironment *queryEnv,
					DestReceiver *dest, char *completionTag)
{
	if (prev_ProcessUtility_hook)
		prev_ProcessUtility_hook(pstmt, queryString, context, params, queryEnv,
								 dest, completionTag);
	else
		standard_ProcessUtility(pstmt, queryString, context, params, queryEnv,
								 dest, completionTag);

	if (plpgsql_recurse_level == 0)
		current_hint_retrieved = false;
}

/*
 * Read and set up hint information
 */
static PlannedStmt *
pg_hint_plan_planner(Query *parse, int cursorOptions, ParamListInfo boundParams)
{
	int				save_nestlevel;
	PlannedStmt	   *result;
	HintState	   *hstate;
	const char 	   *prev_hint_str = NULL;

	/*
	 * Use standard planner if pg_hint_plan is disabled or current nesting
	 * depth is nesting depth of SPI calls. Other hook functions try to change
	 * plan with current_hint_state if any, so set it to NULL.
	 */
	if (!pg_hint_plan_enable_hint || hint_inhibit_level > 0)
	{
		if (debug_level > 1)
			ereport(pg_hint_plan_debug_message_level,
					(errmsg ("pg_hint_plan%s: planner: enable_hint=%d,"
							 " hint_inhibit_level=%d",
							 qnostr, pg_hint_plan_enable_hint,
							 hint_inhibit_level),
					 errhidestmt(msgqno != qno)));
		msgqno = qno;

		goto standard_planner_proc;
	}

	/*
	 * Support for nested plpgsql functions. This is quite ugly but this is the
	 * only point I could find where I can get the query string.
	 */
	if (plpgsql_recurse_level > 0 &&
		error_context_stack && error_context_stack->arg)
	{
		MemoryContext oldcontext;

		oldcontext = MemoryContextSwitchTo(TopMemoryContext);
		current_hint_str =
			get_hints_from_comment((char *)error_context_stack->arg);
		MemoryContextSwitchTo(oldcontext);
	}

	/*
	 * Query execution in extended protocol can be started without the analyze
	 * phase. In the case retrieve hint string here.
	 */
	if (!current_hint_str)
		get_current_hint_string(NULL, parse);

	/* No hint, go the normal way */
	if (!current_hint_str)
		goto standard_planner_proc;

	/* parse the hint into hint state struct */
	hstate = create_hintstate(parse, pstrdup(current_hint_str));

	/* run standard planner if the statement has not valid hint */
	if (!hstate)
		goto standard_planner_proc;

	/*
	 * Push new hint struct to the hint stack to disable previous hint context.
	 */
	push_hint(hstate);

	/*  Set scan enforcement here. */
	save_nestlevel = NewGUCNestLevel();

	/* Apply Set hints, then save it as the initial state  */
	setup_guc_enforcement(current_hint_state->set_hints,
						   current_hint_state->num_hints[HINT_TYPE_SET],
						   current_hint_state->context);

	current_hint_state->init_scan_mask = get_current_scan_mask();
	current_hint_state->init_join_mask = get_current_join_mask();
	current_hint_state->init_min_para_tablescan_size =
		min_parallel_table_scan_size;
	current_hint_state->init_min_para_indexscan_size =
		min_parallel_index_scan_size;
	current_hint_state->init_paratup_cost = parallel_tuple_cost;
	current_hint_state->init_parasetup_cost = parallel_setup_cost;

	/*
	 * max_parallel_workers_per_gather should be non-zero here if Workers hint
	 * is specified.
	 */
	if (max_hint_nworkers > 0 && max_parallel_workers_per_gather < 1)
		set_config_int32_option("max_parallel_workers_per_gather",
								1, current_hint_state->context);
	current_hint_state->init_nworkers = max_parallel_workers_per_gather;

	if (debug_level > 1)
	{
		ereport(pg_hint_plan_debug_message_level,
				(errhidestmt(msgqno != qno),
				 errmsg("pg_hint_plan%s: planner", qnostr)));
		msgqno = qno;
	}

	/*
	 * The planner call below may replace current_hint_str. Store and restore
	 * it so that the subsequent planning in the upper level doesn't get
	 * confused.
	 */
	recurse_level++;
	prev_hint_str = current_hint_str;
	current_hint_str = NULL;

	/*
	 * Use PG_TRY mechanism to recover GUC parameters and current_hint_state to
	 * the state when this planner started when error occurred in planner.
	 */
	PG_TRY();
	{
		if (prev_planner)
			result = (*prev_planner) (parse, cursorOptions, boundParams);
		else
			result = standard_planner(parse, cursorOptions, boundParams);

		current_hint_str = prev_hint_str;
		recurse_level--;
	}
	PG_CATCH();
	{
		/*
		 * Rollback changes of GUC parameters, and pop current hint context
		 * from hint stack to rewind the state.
		 */
		current_hint_str = prev_hint_str;
		recurse_level--;
		AtEOXact_GUC(true, save_nestlevel);
		pop_hint();
		PG_RE_THROW();
	}
	PG_END_TRY();


	/*
	 * current_hint_str is useless after planning of the top-level query.
	 */
	if (recurse_level < 1 && current_hint_str)
	{
		pfree((void *)current_hint_str);
		current_hint_str = NULL;
		current_hint_retrieved = false;
	}

	/* Print hint in debug mode. */
	if (debug_level == 1)
		HintStateDump(current_hint_state);
	else if (debug_level > 1)
		HintStateDump2(current_hint_state);

	/*
	 * Rollback changes of GUC parameters, and pop current hint context from
	 * hint stack to rewind the state.
	 */
	AtEOXact_GUC(true, save_nestlevel);
	pop_hint();

	return result;

standard_planner_proc:
	if (debug_level > 1)
	{
		ereport(pg_hint_plan_debug_message_level,
				(errhidestmt(msgqno != qno),
				 errmsg("pg_hint_plan%s: planner: no valid hint",
						qnostr)));
		msgqno = qno;
	}
	current_hint_state = NULL;
	if (prev_planner)
		result =  (*prev_planner) (parse, cursorOptions, boundParams);
	else
		result = standard_planner(parse, cursorOptions, boundParams);

	/* The upper-level planner still needs the current hint state */
	if (HintStateStack != NIL)
		current_hint_state = (HintState *) lfirst(list_head(HintStateStack));

	return result;
}

/*
 * Find scan method hint to be applied to the given relation
 *
 */
static ScanMethodHint *
find_scan_hint(PlannerInfo *root, Index relid)
{
	RelOptInfo	   *rel;
	RangeTblEntry  *rte;
	ScanMethodHint	*real_name_hint = NULL;
	ScanMethodHint	*alias_hint = NULL;
	int				i;

	/* This should not be a join rel */
	Assert(relid > 0);
	rel = root->simple_rel_array[relid];

	/*
	 * This function is called for any RelOptInfo or its inheritance parent if
	 * any. If we are called from inheritance planner, the RelOptInfo for the
	 * parent of target child relation is not set in the planner info.
	 *
	 * Otherwise we should check that the reloptinfo is base relation or
	 * inheritance children.
	 */
	if (rel &&
		rel->reloptkind != RELOPT_BASEREL &&
		rel->reloptkind != RELOPT_OTHER_MEMBER_REL)
		return NULL;

	/*
	 * This is baserel or appendrel children. We can refer to RangeTblEntry.
	 */
	rte = root->simple_rte_array[relid];
	Assert(rte);

	/* We don't hint on other than relation and foreign tables */
	if (rte->rtekind != RTE_RELATION ||
		rte->relkind == RELKIND_FOREIGN_TABLE)
		return NULL;

	/* Find scan method hint, which matches given names, from the list. */
	for (i = 0; i < current_hint_state->num_hints[HINT_TYPE_SCAN_METHOD]; i++)
	{
		ScanMethodHint *hint = current_hint_state->scan_hints[i];

		/* We ignore disabled hints. */
		if (!hint_state_enabled(hint))
			continue;

		if (!alias_hint &&
			RelnameCmp(&rte->eref->aliasname, &hint->relname) == 0)
			alias_hint = hint;

		/* check the real name for appendrel children */
		if (!real_name_hint &&
			rel && rel->reloptkind == RELOPT_OTHER_MEMBER_REL)
		{
			char *realname = get_rel_name(rte->relid);

			if (realname && RelnameCmp(&realname, &hint->relname) == 0)
				real_name_hint = hint;
		}

		/* No more match expected, break  */
		if(alias_hint && real_name_hint)
			break;
	}

	/* real name match precedes alias match */
	if (real_name_hint)
		return real_name_hint;

	return alias_hint;
}

static ParallelHint *
find_parallel_hint(PlannerInfo *root, Index relid)
{
	RelOptInfo	   *rel;
	RangeTblEntry  *rte;
	ParallelHint	*real_name_hint = NULL;
	ParallelHint	*alias_hint = NULL;
	int				i;

	/* This should not be a join rel */
	Assert(relid > 0);
	rel = root->simple_rel_array[relid];

	/*
	 * Parallel planning is appliable only on base relation, which has
	 * RelOptInfo.
	 */
	if (!rel)
		return NULL;

	/*
	 * We have set root->glob->parallelModeOK if needed. What we should do here
	 * is just following the decision of planner.
	 */
	if (!rel->consider_parallel)
		return NULL;

	/*
	 * This is baserel or appendrel children. We can refer to RangeTblEntry.
	 */
	rte = root->simple_rte_array[relid];
	Assert(rte);

	/* Find parallel method hint, which matches given names, from the list. */
	for (i = 0; i < current_hint_state->num_hints[HINT_TYPE_PARALLEL]; i++)
	{
		ParallelHint *hint = current_hint_state->parallel_hints[i];

		/* We ignore disabled hints. */
		if (!hint_state_enabled(hint))
			continue;

		if (!alias_hint &&
			RelnameCmp(&rte->eref->aliasname, &hint->relname) == 0)
			alias_hint = hint;

		/* check the real name for appendrel children */
		if (!real_name_hint &&
			rel && rel->reloptkind == RELOPT_OTHER_MEMBER_REL)
		{
			char *realname = get_rel_name(rte->relid);

			if (realname && RelnameCmp(&realname, &hint->relname) == 0)
				real_name_hint = hint;
		}

		/* No more match expected, break  */
		if(alias_hint && real_name_hint)
			break;
	}

	/* real name match precedes alias match */
	if (real_name_hint)
		return real_name_hint;

	return alias_hint;
}

/*
 * Find motion hint to be applied to the given relation
 *
 */
static MotionHint *
find_motion_hint(PlannerInfo *root, Index relid)
{
	RelOptInfo	   *rel;
	RangeTblEntry  *rte;
	MotionHint	*real_name_hint = NULL;
	MotionHint	*alias_hint = NULL;
	int				i;

	/* This should not be a join rel */
	Assert(relid > 0);
	rel = root->simple_rel_array[relid];

	if (!rel)
		return NULL;

	/*
	 * This function is called for any RelOptInfo or its inheritance parent if
	 * any. If we are called from inheritance planner, the RelOptInfo for the
	 * parent of target child relation is not set in the planner info.
	 *
	 * Otherwise we should check that the reloptinfo is base relation or
	 * inheritance children.
	 */
	if (!IS_SIMPLE_REL(rel))
		return NULL;

	/*
	 * This is baserel or appendrel children. We can refer to RangeTblEntry.
	 */
	rte = root->simple_rte_array[relid];
	Assert(rte);

	/* We don't hint on other than relation and foreign tables */
	if (rte->rtekind != RTE_RELATION ||
		rte->relkind == RELKIND_FOREIGN_TABLE)
		return NULL;

	/* Find scan method hint, which matches given names, from the list. */
	for (i = 0; i < current_hint_state->num_hints[HINT_TYPE_MOTION]; i++)
	{
		MotionHint *hint = current_hint_state->motion_hints[i];

		if (!hint)
			continue;

		/* We ignore disabled hints. */
		if (!hint_state_enabled(hint))
			continue;

		if (!alias_hint &&
			RelnameCmp(&rte->eref->aliasname, &hint->relname) == 0)
			alias_hint = hint;

		/* check the real name for appendrel children */
		if (!real_name_hint &&
			rel && rel->reloptkind == RELOPT_OTHER_MEMBER_REL)
		{
			char *realname = get_rel_name(rte->relid);

			if (realname && RelnameCmp(&realname, &hint->relname) == 0)
				real_name_hint = hint;
		}

		/* No more match expected, break  */
		if(alias_hint && real_name_hint)
			break;
	}

	/* real name match precedes alias match */
	if (real_name_hint)
		return real_name_hint;

	return alias_hint;
}

/*
 * regexeq
 *
 * Returns TRUE on match, FALSE on no match.
 *
 *   s1 --- the data to match against
 *   s2 --- the pattern
 *
 * Because we copy s1 to NameData, make the size of s1 less than NAMEDATALEN.
 */
static bool
regexpeq(const char *s1, const char *s2)
{
	NameData	name;
	text	   *regexp;
	Datum		result;

	strcpy(name.data, s1);
	regexp = cstring_to_text(s2);

	result = DirectFunctionCall2Coll(nameregexeq,
									 DEFAULT_COLLATION_OID,
									 NameGetDatum(&name),
									 PointerGetDatum(regexp));
	return DatumGetBool(result);
}


/* Remove indexes instructed not to use by hint. */
static void
restrict_indexes(PlannerInfo *root, ScanMethodHint *hint, RelOptInfo *rel,
			   bool using_parent_hint)
{
	ListCell	   *cell;
	ListCell	   *prev;
	ListCell	   *next;
	StringInfoData	buf;
	RangeTblEntry  *rte = root->simple_rte_array[rel->relid];
	Oid				relationObjectId = rte->relid;

	/*
	 * We delete all the IndexOptInfo list and prevent you from being usable by
	 * a scan.
	 */
	if (hint->enforce_mask == ENABLE_SEQSCAN ||
		hint->enforce_mask == ENABLE_TIDSCAN)
	{
		list_free_deep(rel->indexlist);
		rel->indexlist = NIL;
		hint->base.state = HINT_STATE_USED;

		return;
	}

	/*
	 * When a list of indexes is not specified, we just use all indexes.
	 */
	if (hint->indexnames == NIL)
		return;

	/*
	 * Leaving only an specified index, we delete it from a IndexOptInfo list
	 * other than it.
	 */
	prev = NULL;
	if (debug_level > 0)
		initStringInfo(&buf);

	for (cell = list_head(rel->indexlist); cell; cell = next)
	{
		IndexOptInfo   *info = (IndexOptInfo *) lfirst(cell);
		char		   *indexname = get_rel_name(info->indexoid);
		ListCell	   *l;
		bool			use_index = false;

		next = lnext(cell);

		foreach(l, hint->indexnames)
		{
			char   *hintname = (char *) lfirst(l);
			bool	result;

			if (hint->regexp)
				result = regexpeq(indexname, hintname);
			else
				result = RelnameCmp(&indexname, &hintname) == 0;

			if (result)
			{
				use_index = true;
				if (debug_level > 0)
				{
					appendStringInfoCharMacro(&buf, ' ');
					quote_value(&buf, indexname);
				}

				break;
			}
		}

		/*
		 * Apply index restriction of parent hint to children. Since index
		 * inheritance is not explicitly described we should search for an
		 * children's index with the same definition to that of the parent.
		 */
		if (using_parent_hint && !use_index)
		{
			foreach(l, current_hint_state->parent_index_infos)
			{
				int					i;
				HeapTuple			ht_idx;
				ParentIndexInfo	   *p_info = (ParentIndexInfo *)lfirst(l);

				/*
				 * we check the 'same' index by comparing uniqueness, access
				 * method and index key columns.
				 */
				if (p_info->indisunique != info->unique ||
					p_info->method != info->relam ||
					list_length(p_info->column_names) != info->ncolumns)
					continue;

				/* Check if index key columns match */
				for (i = 0; i < info->ncolumns; i++)
				{
					char       *c_attname = NULL;
					char       *p_attname = NULL;

					p_attname = list_nth(p_info->column_names, i);

					/*
					 * if both of the key of the same position are expressions,
					 * ignore them for now and check later.
					 */
					if (info->indexkeys[i] == 0 && !p_attname)
						continue;

					/* deny if one is expression while another is not */
					if (info->indexkeys[i] == 0 || !p_attname)
						break;

					c_attname = get_attname(relationObjectId,
											info->indexkeys[i], false);

					/* deny if any of column attributes don't match */
					if (strcmp(p_attname, c_attname) != 0 ||
						p_info->indcollation[i] != info->indexcollations[i] ||
						p_info->opclass[i] != info->opcintype[i]||
						((p_info->indoption[i] & INDOPTION_DESC) != 0)
						!= info->reverse_sort[i] ||
						((p_info->indoption[i] & INDOPTION_NULLS_FIRST) != 0)
						!= info->nulls_first[i])
						break;
				}

				/* deny this if any difference found */
				if (i != info->ncolumns)
					continue;

				/* check on key expressions  */
				if ((p_info->expression_str && (info->indexprs != NIL)) ||
					(p_info->indpred_str && (info->indpred != NIL)))
				{
					/* fetch the index of this child */
					ht_idx = SearchSysCache1(INDEXRELID,
											 ObjectIdGetDatum(info->indexoid));

					/* check expressions if both expressions are available */
					if (p_info->expression_str &&
						!heap_attisnull(ht_idx, Anum_pg_index_indexprs, NULL))
					{
						Datum       exprsDatum;
						bool        isnull;
						Datum       result;

						/*
						 * to change the expression's parameter of child's
						 * index to strings
						 */
						exprsDatum = SysCacheGetAttr(INDEXRELID, ht_idx,
													 Anum_pg_index_indexprs,
													 &isnull);

						result = DirectFunctionCall2(pg_get_expr,
													 exprsDatum,
													 ObjectIdGetDatum(
														 relationObjectId));

						/* deny if expressions don't match */
						if (strcmp(p_info->expression_str,
								   text_to_cstring(DatumGetTextP(result))) != 0)
						{
							/* Clean up */
							ReleaseSysCache(ht_idx);
							continue;
						}
					}

					/* compare index predicates  */
					if (p_info->indpred_str &&
						!heap_attisnull(ht_idx, Anum_pg_index_indpred, NULL))
					{
						Datum       predDatum;
						bool        isnull;
						Datum       result;

						predDatum = SysCacheGetAttr(INDEXRELID, ht_idx,
													 Anum_pg_index_indpred,
													 &isnull);

						result = DirectFunctionCall2(pg_get_expr,
													 predDatum,
													 ObjectIdGetDatum(
														 relationObjectId));

						if (strcmp(p_info->indpred_str,
								   text_to_cstring(DatumGetTextP(result))) != 0)
						{
							/* Clean up */
							ReleaseSysCache(ht_idx);
							continue;
						}
					}

					/* Clean up */
					ReleaseSysCache(ht_idx);
				}
				else if (p_info->expression_str || (info->indexprs != NIL))
					continue;
				else if	(p_info->indpred_str || (info->indpred != NIL))
					continue;

				use_index = true;

				/* to log the candidate of index */
				if (debug_level > 0)
				{
					appendStringInfoCharMacro(&buf, ' ');
					quote_value(&buf, indexname);
				}

				break;
			}
		}

		if (!use_index)
			rel->indexlist = list_delete_cell(rel->indexlist, cell, prev);
		else
			prev = cell;

		pfree(indexname);
	}

	if (debug_level == 1)
	{
		StringInfoData  rel_buf;
		char *disprelname = "";

		/*
		 * If this hint targetted the parent, use the real name of this
		 * child. Otherwise use hint specification.
		 */
		if (using_parent_hint)
			disprelname = get_rel_name(rte->relid);
		else
			disprelname = hint->relname;

		initStringInfo(&rel_buf);
		quote_value(&rel_buf, disprelname);

		ereport(pg_hint_plan_debug_message_level,
				(errmsg("available indexes for %s(%s):%s",
					 hint->base.keyword,
					 rel_buf.data,
					 buf.data)));
		pfree(buf.data);
		pfree(rel_buf.data);
	}
}

/*
 * Return information of index definition.
 */
static ParentIndexInfo *
get_parent_index_info(Oid indexoid, Oid relid)
{
	ParentIndexInfo	*p_info = palloc(sizeof(ParentIndexInfo));
	Relation	    indexRelation;
	Form_pg_index	index;
	char		   *attname;
	int				i;

	indexRelation = index_open(indexoid, RowExclusiveLock);

	index = indexRelation->rd_index;

	p_info->indisunique = index->indisunique;
	p_info->method = indexRelation->rd_rel->relam;

	p_info->column_names = NIL;
	p_info->indcollation = (Oid *) palloc(sizeof(Oid) * index->indnatts);
	p_info->opclass = (Oid *) palloc(sizeof(Oid) * index->indnatts);
	p_info->indoption = (int16 *) palloc(sizeof(Oid) * index->indnatts);

	/*
	 * Collect relation attribute names of index columns for index
	 * identification, not index attribute names. NULL means expression index
	 * columns.
	 */
	for (i = 0; i < index->indnatts; i++)
	{
		attname = get_attname(relid, index->indkey.values[i], true);
		p_info->column_names = lappend(p_info->column_names, attname);

		p_info->indcollation[i] = indexRelation->rd_indcollation[i];
		p_info->opclass[i] = indexRelation->rd_opcintype[i];
		p_info->indoption[i] = indexRelation->rd_indoption[i];
	}

	/*
	 * to check to match the expression's parameter of index with child indexes
	 */
	p_info->expression_str = NULL;
	if(!heap_attisnull(indexRelation->rd_indextuple, Anum_pg_index_indexprs,
					   NULL))
	{
		Datum       exprsDatum;
		bool		isnull;
		Datum		result;

		exprsDatum = SysCacheGetAttr(INDEXRELID, indexRelation->rd_indextuple,
									 Anum_pg_index_indexprs, &isnull);

		result = DirectFunctionCall2(pg_get_expr,
									 exprsDatum,
									 ObjectIdGetDatum(relid));

		p_info->expression_str = text_to_cstring(DatumGetTextP(result));
	}

	/*
	 * to check to match the predicate's parameter of index with child indexes
	 */
	p_info->indpred_str = NULL;
	if(!heap_attisnull(indexRelation->rd_indextuple, Anum_pg_index_indpred,
					   NULL))
	{
		Datum       predDatum;
		bool		isnull;
		Datum		result;

		predDatum = SysCacheGetAttr(INDEXRELID, indexRelation->rd_indextuple,
									 Anum_pg_index_indpred, &isnull);

		result = DirectFunctionCall2(pg_get_expr,
									 predDatum,
									 ObjectIdGetDatum(relid));

		p_info->indpred_str = text_to_cstring(DatumGetTextP(result));
	}

	index_close(indexRelation, NoLock);

	return p_info;
}

/*
 * cancel hint enforcement
 */
static void
reset_hint_enforcement()
{
	setup_scan_method_enforcement(NULL, current_hint_state);
	setup_parallel_plan_enforcement(NULL, current_hint_state);
}

/*
 * Set planner guc parameters according to corresponding scan hints.  Returns
 * bitmap of HintTypeBitmap. If shint or phint is not NULL, set used hint
 * there respectively.
 */
static int
setup_hint_enforcement(PlannerInfo *root, RelOptInfo *rel,
					   ScanMethodHint **rshint, ParallelHint **rphint)
{
	Index	new_parent_relid = 0;
	ListCell *l;
	ScanMethodHint *shint = NULL;
	ParallelHint   *phint = NULL;
	bool			inhparent = root->simple_rte_array[rel->relid]->inh;
	Oid		relationObjectId = root->simple_rte_array[rel->relid]->relid;
	int				ret = 0;

	/* reset returns if requested  */
	if (rshint != NULL) *rshint = NULL;
	if (rphint != NULL) *rphint = NULL;

	/*
	 * We could register the parent relation of the following children here
	 * when inhparent == true but inheritnce planner doesn't call this function
	 * for parents. Since we cannot distinguish who called this function we
	 * cannot do other than always seeking the parent regardless of who called
	 * this function.
	 */
	if (inhparent)
	{
		/* set up only parallel hints for parent relation */
		phint = find_parallel_hint(root, rel->relid);
		if (phint)
		{
			setup_parallel_plan_enforcement(phint, current_hint_state);
			if (rphint) *rphint = phint;
			ret |= HINT_BM_PARALLEL;
			return ret;
		}

		if (debug_level > 1)
			ereport(pg_hint_plan_debug_message_level,
					(errhidestmt(true),
					 errmsg ("pg_hint_plan%s: setup_hint_enforcement"
							 " skipping inh parent: relation=%u(%s), inhparent=%d,"
							 " current_hint_state=%p, hint_inhibit_level=%d",
							 qnostr, relationObjectId,
							 get_rel_name(relationObjectId),
							 inhparent, current_hint_state, hint_inhibit_level)));
		return 0;
	}

	/*
	 * Forget about the parent of another subquery, but don't forget if the
	 * inhTargetkind of the root is not INHKIND_NONE, which signals the root
	 * contains only appendrel members. See inheritance_planner for details.
	 *
	 * (PG12.0) 428b260f87 added one more planning cycle for updates on
	 * partitioned tables and hints set up in the cycle are overriden by the
	 * second cycle. Since I didn't find no apparent distinction between the
	 * PlannerRoot of the cycle and that of ordinary CMD_SELECT, pg_hint_plan
	 * accepts both cycles and the later one wins. In the second cycle root
	 * doesn't have inheritance information at all so use the parent_relid set
	 * in the first cycle.
	 */
	if (root->inhTargetKind == INHKIND_NONE)
	{
		if (root != current_hint_state->current_root)
			current_hint_state->parent_relid = 0;

		/* Find the parent for this relation other than the registered parent */
		foreach (l, root->append_rel_list)
		{
			AppendRelInfo *appinfo = (AppendRelInfo *) lfirst(l);

			if (appinfo->child_relid == rel->relid)
			{
				if (current_hint_state->parent_relid != appinfo->parent_relid)
				{
					new_parent_relid = appinfo->parent_relid;
					current_hint_state->current_root = root;
				}
				break;
			}
		}

		if (!l)
		{
			/*
			 * This relation doesn't have a parent. Cancel
			 * current_hint_state.
			 */
			current_hint_state->parent_relid = 0;
			current_hint_state->parent_scan_hint = NULL;
			current_hint_state->parent_parallel_hint = NULL;
		}
	}

	if (new_parent_relid > 0)
	{
		/*
		 * Here we found a new parent for the current relation. Scan continues
		 * hint to other childrens of this parent so remember it to avoid
		 * redundant setup cost.
		 */
		current_hint_state->parent_relid = new_parent_relid;

		/* Find hints for the parent */
		current_hint_state->parent_scan_hint =
			find_scan_hint(root, current_hint_state->parent_relid);

		current_hint_state->parent_parallel_hint =
			find_parallel_hint(root, current_hint_state->parent_relid);

		/*
		 * If hint is found for the parent, apply it for this child instead
		 * of its own.
		 */
		if (current_hint_state->parent_scan_hint)
		{
			ScanMethodHint * pshint = current_hint_state->parent_scan_hint;

			pshint->base.state = HINT_STATE_USED;

			/* Apply index mask in the same manner to the parent. */
			if (pshint->indexnames)
			{
				Oid			parentrel_oid;
				Relation	parent_rel;

				parentrel_oid =
					root->simple_rte_array[current_hint_state->parent_relid]->relid;
				parent_rel = heap_open(parentrel_oid, NoLock);

				/* Search the parent relation for indexes match the hint spec */
				foreach(l, RelationGetIndexList(parent_rel))
				{
					Oid         indexoid = lfirst_oid(l);
					char       *indexname = get_rel_name(indexoid);
					ListCell   *lc;
					ParentIndexInfo *parent_index_info;

					foreach(lc, pshint->indexnames)
					{
						if (RelnameCmp(&indexname, &lfirst(lc)) == 0)
							break;
					}
					if (!lc)
						continue;

					parent_index_info =
						get_parent_index_info(indexoid, parentrel_oid);
					current_hint_state->parent_index_infos =
						lappend(current_hint_state->parent_index_infos,
								parent_index_info);
				}
				heap_close(parent_rel, NoLock);
			}
		}
	}

	shint = find_scan_hint(root, rel->relid);
	if (!shint)
		shint = current_hint_state->parent_scan_hint;

	if (shint)
	{
		bool using_parent_hint =
			(shint == current_hint_state->parent_scan_hint);

		ret |= HINT_BM_SCAN_METHOD;

		/* Setup scan enforcement environment */
		setup_scan_method_enforcement(shint, current_hint_state);

		/* restrict unwanted inexes */
		restrict_indexes(root, shint, rel, using_parent_hint);

		if (debug_level > 1)
		{
			char *additional_message = "";

			if (shint == current_hint_state->parent_scan_hint)
				additional_message = " by parent hint";

			ereport(pg_hint_plan_debug_message_level,
					(errhidestmt(true),
					 errmsg ("pg_hint_plan%s: setup_hint_enforcement"
							 " index deletion%s:"
							 " relation=%u(%s), inhparent=%d, "
							 "current_hint_state=%p,"
							 " hint_inhibit_level=%d, scanmask=0x%x",
							 qnostr, additional_message,
							 relationObjectId,
							 get_rel_name(relationObjectId),
							 inhparent, current_hint_state,
							 hint_inhibit_level,
							 shint->enforce_mask)));
		}
	}

	/* Do the same for parallel plan enforcement */
	phint = find_parallel_hint(root, rel->relid);
	if (!phint)
		phint = current_hint_state->parent_parallel_hint;

	setup_parallel_plan_enforcement(phint, current_hint_state);

	if (phint)
		ret |= HINT_BM_PARALLEL;

	/* Nothing to apply. Reset the scan mask to intial state */
	if (!shint && ! phint)
	{
		if (debug_level > 1)
			ereport(pg_hint_plan_debug_message_level,
					(errhidestmt (true),
					 errmsg ("pg_hint_plan%s: setup_hint_enforcement"
							 " no hint applied:"
							 " relation=%u(%s), inhparent=%d, current_hint=%p,"
							 " hint_inhibit_level=%d, scanmask=0x%x",
							 qnostr, relationObjectId,
							 get_rel_name(relationObjectId),
							 inhparent, current_hint_state, hint_inhibit_level,
							 current_hint_state->init_scan_mask)));

		setup_scan_method_enforcement(NULL,	current_hint_state);

		return ret;
	}

	if (rshint != NULL) *rshint = shint;
	if (rphint != NULL) *rphint = phint;

	return ret;
}

/*
 * Return index of relation which matches given aliasname, or 0 if not found.
 * If same aliasname was used multiple times in a query, return -1.
 */
static int
find_relid_aliasname(PlannerInfo *root, char *aliasname, List *initial_rels,
					 const char *str)
{
	int		i;
	Index	found = 0;

	for (i = 1; i < root->simple_rel_array_size; i++)
	{
		ListCell   *l;

		if (root->simple_rel_array[i] == NULL)
			continue;

		Assert(i == root->simple_rel_array[i]->relid);

		if (RelnameCmp(&aliasname,
					   &root->simple_rte_array[i]->eref->aliasname) != 0)
			continue;

		foreach(l, initial_rels)
		{
			RelOptInfo *rel = (RelOptInfo *) lfirst(l);

			if (rel->reloptkind == RELOPT_BASEREL)
			{
				if (rel->relid != i)
					continue;
			}
			else
			{
				Assert(rel->reloptkind == RELOPT_JOINREL);

				if (!bms_is_member(i, rel->relids))
					continue;
			}

			if (found != 0)
			{
				hint_ereport(str,
							 ("Relation name \"%s\" is ambiguous.",
							  aliasname));
				return -1;
			}

			found = i;
			break;
		}

	}

	return found;
}

/*
 * Return join hint which matches given joinrelids.
 */
static JoinMethodHint *
find_join_hint(Relids joinrelids)
{
	List	   *join_hint;
	ListCell   *l;

	join_hint = current_hint_state->join_hint_level[bms_num_members(joinrelids)];

	foreach(l, join_hint)
	{
		JoinMethodHint *hint = (JoinMethodHint *) lfirst(l);

		if (bms_equal(joinrelids, hint->joinrelids))
			return hint;
	}

	return NULL;
}

static Relids
OuterInnerJoinCreate(OuterInnerRels *outer_inner, LeadingHint *leading_hint,
	PlannerInfo *root, List *initial_rels, HintState *hstate, int nbaserel)
{
	OuterInnerRels *outer_rels;
	OuterInnerRels *inner_rels;
	Relids			outer_relids;
	Relids			inner_relids;
	Relids			join_relids;
	JoinMethodHint *hint;

	if (outer_inner->relation != NULL)
	{
		return bms_make_singleton(
					find_relid_aliasname(root, outer_inner->relation,
										 initial_rels,
										 leading_hint->base.hint_str));
	}

	outer_rels = lfirst(outer_inner->outer_inner_pair->head);
	inner_rels = lfirst(outer_inner->outer_inner_pair->tail);

	outer_relids = OuterInnerJoinCreate(outer_rels,
										leading_hint,
										root,
										initial_rels,
										hstate,
										nbaserel);
	inner_relids = OuterInnerJoinCreate(inner_rels,
										leading_hint,
										root,
										initial_rels,
										hstate,
										nbaserel);

	join_relids = bms_add_members(outer_relids, inner_relids);

	if (bms_num_members(join_relids) > nbaserel)
		return join_relids;

	/*
	 * If we don't have join method hint, create new one for the
	 * join combination with all join methods are enabled.
	 */
	hint = find_join_hint(join_relids);
	if (hint == NULL)
	{
		/*
		 * Here relnames is not set, since Relids bitmap is sufficient to
		 * control paths of this query afterward.
		 */
		hint = (JoinMethodHint *) JoinMethodHintCreate(
					leading_hint->base.hint_str,
					HINT_LEADING,
					HINT_KEYWORD_LEADING);
		hint->base.state = HINT_STATE_USED;
		hint->nrels = bms_num_members(join_relids);
		hint->enforce_mask = ENABLE_ALL_JOIN;
		hint->joinrelids = bms_copy(join_relids);
		hint->inner_nrels = bms_num_members(inner_relids);
		hint->inner_joinrelids = bms_copy(inner_relids);

		hstate->join_hint_level[hint->nrels] =
			lappend(hstate->join_hint_level[hint->nrels], hint);
	}
	else
	{
		hint->inner_nrels = bms_num_members(inner_relids);
		hint->inner_joinrelids = bms_copy(inner_relids);
	}

	return join_relids;
}

static Relids
create_bms_of_relids(Hint *base, PlannerInfo *root, List *initial_rels,
		int nrels, char **relnames)
{
	int		relid;
	Relids	relids = NULL;
	int		j;
	char   *relname;

	for (j = 0; j < nrels; j++)
	{
		relname = relnames[j];

		relid = find_relid_aliasname(root, relname, initial_rels,
									 base->hint_str);

		if (relid == -1)
			base->state = HINT_STATE_ERROR;

		/*
		 * the aliasname is not found(relid == 0) or same aliasname was used
		 * multiple times in a query(relid == -1)
		 */
		if (relid <= 0)
		{
			relids = NULL;
			break;
		}
		if (bms_is_member(relid, relids))
		{
			hint_ereport(base->hint_str,
						 ("Relation name \"%s\" is duplicated.", relname));
			base->state = HINT_STATE_ERROR;
			break;
		}

		relids = bms_add_member(relids, relid);
	}
	return relids;
}
/*
 * Transform join method hint into handy form.
 *
 *   - create bitmap of relids from alias names, to make it easier to check
 *     whether a join path matches a join method hint.
 *   - add join method hints which are necessary to enforce join order
 *     specified by Leading hint
 */
static bool
transform_join_hints(HintState *hstate, PlannerInfo *root, int nbaserel,
		List *initial_rels, JoinMethodHint **join_method_hints)
{
	int				i;
	int				relid;
	Relids			joinrelids;
	int				njoinrels;
	ListCell	   *l;
	char		   *relname;
	LeadingHint	   *lhint = NULL;

	/*
	 * Create bitmap of relids from alias names for each join method hint.
	 * Bitmaps are more handy than strings in join searching.
	 */
	for (i = 0; i < hstate->num_hints[HINT_TYPE_JOIN_METHOD]; i++)
	{
		JoinMethodHint *hint = hstate->join_hints[i];

		if (!hint_state_enabled(hint) || hint->nrels > nbaserel)
			continue;

		hint->joinrelids = create_bms_of_relids(&(hint->base), root,
									 initial_rels, hint->nrels, hint->relnames);

		if (hint->joinrelids == NULL || hint->base.state == HINT_STATE_ERROR)
			continue;

		hstate->join_hint_level[hint->nrels] =
			lappend(hstate->join_hint_level[hint->nrels], hint);
	}

	/*
	 * Create bitmap of relids from alias names for each rows hint.
	 * Bitmaps are more handy than strings in join searching.
	 */
	for (i = 0; i < hstate->num_hints[HINT_TYPE_ROWS]; i++)
	{
		RowsHint *hint = hstate->rows_hints[i];

		if (!hint_state_enabled(hint) || hint->nrels > nbaserel)
			continue;

		hint->joinrelids = create_bms_of_relids(&(hint->base), root,
									 initial_rels, hint->nrels, hint->relnames);
	}

	/* Do nothing if no Leading hint was supplied. */
	if (hstate->num_hints[HINT_TYPE_LEADING] == 0)
		return false;

	/*
	 * Decide whether to use Leading hint
	 */
	for (i = 0; i < hstate->num_hints[HINT_TYPE_LEADING]; i++)
	{
		LeadingHint	   *leading_hint = (LeadingHint *)hstate->leading_hint[i];
		Relids			relids;

		if (leading_hint->base.state == HINT_STATE_ERROR)
			continue;

		relid = 0;
		relids = NULL;

		foreach(l, leading_hint->relations)
		{
			relname = (char *)lfirst(l);;

			relid = find_relid_aliasname(root, relname, initial_rels,
										 leading_hint->base.hint_str);
			if (relid == -1)
				leading_hint->base.state = HINT_STATE_ERROR;

			if (relid <= 0)
				break;

			if (bms_is_member(relid, relids))
			{
				hint_ereport(leading_hint->base.hint_str,
							 ("Relation name \"%s\" is duplicated.", relname));
				leading_hint->base.state = HINT_STATE_ERROR;
				break;
			}

			relids = bms_add_member(relids, relid);
		}

		if (relid <= 0 || leading_hint->base.state == HINT_STATE_ERROR)
			continue;

		if (lhint != NULL)
		{
			hint_ereport(lhint->base.hint_str,
				 ("Conflict %s hint.", HintTypeName[lhint->base.type]));
			lhint->base.state = HINT_STATE_DUPLICATION;
		}
		leading_hint->base.state = HINT_STATE_USED;
		lhint = leading_hint;
	}

	/* check to exist Leading hint marked with 'used'. */
	if (lhint == NULL)
		return false;

	/*
	 * We need join method hints which fit specified join order in every join
	 * level.  For example, Leading(A B C) virtually requires following join
	 * method hints, if no join method hint supplied:
	 *   - level 1: none
	 *   - level 2: NestLoop(A B), MergeJoin(A B), HashJoin(A B)
	 *   - level 3: NestLoop(A B C), MergeJoin(A B C), HashJoin(A B C)
	 *
	 * If we already have join method hint which fits specified join order in
	 * that join level, we leave it as-is and don't add new hints.
	 */
	joinrelids = NULL;
	njoinrels = 0;
	if (lhint->outer_inner == NULL)
	{
		foreach(l, lhint->relations)
		{
			JoinMethodHint *hint;

			relname = (char *)lfirst(l);

			/*
			 * Find relid of the relation which has given name.  If we have the
			 * name given in Leading hint multiple times in the join, nothing to
			 * do.
			 */
			relid = find_relid_aliasname(root, relname, initial_rels,
										 hstate->hint_str);

			/* Create bitmap of relids for current join level. */
			joinrelids = bms_add_member(joinrelids, relid);
			njoinrels++;

			/* We never have join method hint for single relation. */
			if (njoinrels < 2)
				continue;

			/*
			 * If we don't have join method hint, create new one for the
			 * join combination with all join methods are enabled.
			 */
			hint = find_join_hint(joinrelids);
			if (hint == NULL)
			{
				/*
				 * Here relnames is not set, since Relids bitmap is sufficient
				 * to control paths of this query afterward.
				 */
				hint = (JoinMethodHint *) JoinMethodHintCreate(
											lhint->base.hint_str,
											HINT_LEADING,
											HINT_KEYWORD_LEADING);
				hint->base.state = HINT_STATE_USED;
				hint->nrels = njoinrels;
				hint->enforce_mask = ENABLE_ALL_JOIN;
				hint->joinrelids = bms_copy(joinrelids);
			}

			join_method_hints[njoinrels] = hint;

			if (njoinrels >= nbaserel)
				break;
		}
		bms_free(joinrelids);

		if (njoinrels < 2)
			return false;

		/*
		 * Delete all join hints which have different combination from Leading
		 * hint.
		 */
		for (i = 2; i <= njoinrels; i++)
		{
			list_free(hstate->join_hint_level[i]);

			hstate->join_hint_level[i] = lappend(NIL, join_method_hints[i]);
		}
	}
	else
	{
		joinrelids = OuterInnerJoinCreate(lhint->outer_inner,
										  lhint,
										  root,
										  initial_rels,
										  hstate,
										  nbaserel);

		njoinrels = bms_num_members(joinrelids);
		Assert(njoinrels >= 2);

		/*
		 * Delete all join hints which have different combination from Leading
		 * hint.
		 */
		for (i = 2;i <= njoinrels; i++)
		{
			if (hstate->join_hint_level[i] != NIL)
			{
				ListCell *prev = NULL;
				ListCell *next = NULL;
				for(l = list_head(hstate->join_hint_level[i]); l; l = next)
				{

					JoinMethodHint *hint = (JoinMethodHint *)lfirst(l);

					next = lnext(l);

					if (hint->inner_nrels == 0 &&
						!(bms_intersect(hint->joinrelids, joinrelids) == NULL ||
						  bms_equal(bms_union(hint->joinrelids, joinrelids),
						  hint->joinrelids)))
					{
						hstate->join_hint_level[i] =
							list_delete_cell(hstate->join_hint_level[i], l,
											 prev);
					}
					else
						prev = l;
				}
			}
		}

		bms_free(joinrelids);
	}

	if (hint_state_enabled(lhint))
	{
		set_join_config_options(DISABLE_ALL_JOIN, current_hint_state->context);
		return true;
	}
	return false;
}

/*
 * wrapper of make_join_rel()
 *
 * call make_join_rel() after changing enable_* parameters according to given
 * hints.
 */
static RelOptInfo *
make_join_rel_wrapper(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2)
{
	Relids			joinrelids;
	JoinMethodHint *hint;
	RelOptInfo	   *rel;
	int				save_nestlevel;

	joinrelids = bms_union(rel1->relids, rel2->relids);
	hint = find_join_hint(joinrelids);
	bms_free(joinrelids);

	if (!hint)
		return pg_hint_plan_make_join_rel(root, rel1, rel2);

	if (hint->inner_nrels == 0)
	{
		save_nestlevel = NewGUCNestLevel();

		set_join_config_options(hint->enforce_mask,
								current_hint_state->context);

		rel = pg_hint_plan_make_join_rel(root, rel1, rel2);
		hint->base.state = HINT_STATE_USED;

		/*
		 * Restore the GUC variables we set above.
		 */
		AtEOXact_GUC(true, save_nestlevel);
	}
	else
		rel = pg_hint_plan_make_join_rel(root, rel1, rel2);

	return rel;
}

/*
 * TODO : comment
 */
static void
add_paths_to_joinrel_wrapper(PlannerInfo *root,
							 RelOptInfo *joinrel,
							 RelOptInfo *outerrel,
							 RelOptInfo *innerrel,
							 JoinType jointype,
							 SpecialJoinInfo *sjinfo,
							 List *restrictlist)
{
	Relids			joinrelids;
	JoinMethodHint *join_hint;
	int				save_nestlevel;

	joinrelids = bms_union(outerrel->relids, innerrel->relids);
	join_hint = find_join_hint(joinrelids);
	bms_free(joinrelids);

	if (join_hint && join_hint->inner_nrels != 0)
	{
		save_nestlevel = NewGUCNestLevel();

		if (bms_equal(join_hint->inner_joinrelids, innerrel->relids))
		{

			set_join_config_options(join_hint->enforce_mask,
									current_hint_state->context);

			add_paths_to_joinrel_motion_wrapper(root, joinrel, outerrel, innerrel, jointype,
								 sjinfo, restrictlist);
			join_hint->base.state = HINT_STATE_USED;
		}
		else
		{
			set_join_config_options(DISABLE_ALL_JOIN,
									current_hint_state->context);
			add_paths_to_joinrel_motion_wrapper(root, joinrel, outerrel, innerrel, jointype,
								 sjinfo, restrictlist);
		}

		/*
		 * Restore the GUC variables we set above.
		 */
		AtEOXact_GUC(true, save_nestlevel);
	}
	else
		add_paths_to_joinrel_motion_wrapper(root, joinrel, outerrel, innerrel, jointype,
							 sjinfo, restrictlist);
}

static int
get_num_baserels(List *initial_rels)
{
	int			nbaserel = 0;
	ListCell   *l;

	foreach(l, initial_rels)
	{
		RelOptInfo *rel = (RelOptInfo *) lfirst(l);

		if (rel->reloptkind == RELOPT_BASEREL)
			nbaserel++;
		else if (rel->reloptkind ==RELOPT_JOINREL)
			nbaserel+= bms_num_members(rel->relids);
		else
		{
			/* other values not expected here */
			elog(ERROR, "unrecognized reloptkind type: %d", rel->reloptkind);
		}
	}

	return nbaserel;
}

static RelOptInfo *
pg_hint_plan_join_search(PlannerInfo *root, int levels_needed,
						 List *initial_rels)
{
	JoinMethodHint	  **join_method_hints;
	int					nbaserel;
	RelOptInfo		   *rel;
	int					i;
	bool				leading_hint_enable;

	/*
	 * Use standard planner if pg_hint_plan is disabled or no
	 * valid hint is supplied or current nesting depth is nesting depth of SPI
	 * calls.
	 */
	if (!current_hint_state || hint_inhibit_level > 0)
	{
		if (prev_join_search)
			return (*prev_join_search) (root, levels_needed, initial_rels);
		else
			return standard_join_search(root, levels_needed, initial_rels);
	}

	nbaserel = get_num_baserels(initial_rels);
	current_hint_state->join_hint_level =
		palloc0(sizeof(List *) * (nbaserel + 1));
	join_method_hints = palloc0(sizeof(JoinMethodHint *) * (nbaserel + 1));

	leading_hint_enable = transform_join_hints(current_hint_state,
											   root, nbaserel,
											   initial_rels, join_method_hints);

	rel = pg_hint_plan_standard_join_search(root, levels_needed, initial_rels);

	/*
	 * Adjust number of parallel workers of the result rel to the largest
	 * number of the component paths.
	 */
	if (current_hint_state->num_hints[HINT_TYPE_PARALLEL] > 0)
	{
		ListCell   *lc;
		int 		nworkers = 0;

		foreach (lc, initial_rels)
		{
			ListCell *lcp;
			RelOptInfo *rel = (RelOptInfo *) lfirst(lc);

			foreach (lcp, rel->partial_pathlist)
			{
				Path *path = (Path *) lfirst(lcp);

				if (nworkers < path-> parallel_workers)
					nworkers = path-> parallel_workers;
			}
		}

		foreach (lc, rel->partial_pathlist)
		{
			Path *path = (Path *) lfirst(lc);

			if (path->parallel_safe && path->parallel_workers < nworkers)
				path->parallel_workers = nworkers;
		}
	}

	for (i = 2; i <= nbaserel; i++)
	{
		list_free(current_hint_state->join_hint_level[i]);

		/* free Leading hint only */
		if (join_method_hints[i] != NULL &&
			join_method_hints[i]->enforce_mask == ENABLE_ALL_JOIN)
			JoinMethodHintDelete(join_method_hints[i]);
	}
	pfree(current_hint_state->join_hint_level);
	pfree(join_method_hints);

	if (leading_hint_enable)
		set_join_config_options(current_hint_state->init_join_mask,
								current_hint_state->context);

	return rel;
}

/*
 * Force number of wokers if instructed by hint
 */
void
pg_hint_plan_set_rel_pathlist(PlannerInfo * root, RelOptInfo *rel,
							  Index rti, RangeTblEntry *rte)
{
	ParallelHint   *phint;
	ListCell	   *l;
	int				found_hints;

	/* call the previous hook */
	if (prev_set_rel_pathlist)
		prev_set_rel_pathlist(root, rel, rti, rte);

	/* Nothing to do if no hint available */
	if (current_hint_state == NULL)
		return;

	/* Don't touch dummy rels. */
	if (IS_DUMMY_REL(rel))
		return;

	/*
	 * We can accept only plain relations, foreign tables and table saples are
	 * also unacceptable. See set_rel_pathlist.
	 */
	if ((rel->rtekind != RTE_RELATION &&
		 rel->rtekind != RTE_SUBQUERY)||
		rte->relkind == RELKIND_FOREIGN_TABLE ||
		rte->tablesample != NULL)
		return;

	/*
	 * Even though UNION ALL node doesn't have particular name so usually it is
	 * unhintable, turn on parallel when it contains parallel nodes.
	 */
	if (rel->rtekind == RTE_SUBQUERY)
	{
		ListCell *lc;
		bool	inhibit_nonparallel = false;

		if (rel->partial_pathlist == NIL)
			return;

		foreach(lc, rel->partial_pathlist)
		{
			ListCell *lcp;
			AppendPath *apath = (AppendPath *) lfirst(lc);
			int		parallel_workers = 0;

			if (!IsA(apath, AppendPath))
				continue;

			foreach (lcp, apath->subpaths)
			{
				Path *spath = (Path *) lfirst(lcp);

				if (spath->parallel_aware &&
					parallel_workers < spath->parallel_workers)
					parallel_workers = spath->parallel_workers;
			}

			apath->path.parallel_workers = parallel_workers;
			inhibit_nonparallel = true;
		}

		if (inhibit_nonparallel)
		{
			ListCell *lc;

			foreach(lc, rel->pathlist)
			{
				Path *path = (Path *) lfirst(lc);

				if (path->startup_cost < disable_cost)
				{
					path->startup_cost += disable_cost;
					path->total_cost += disable_cost;
				}
			}
		}

		return;
	}

	/* We cannot handle if this requires an outer */
	if (rel->lateral_relids)
		return;

	/* Return if this relation gets no enfocement */
	if ((found_hints = setup_hint_enforcement(root, rel, NULL, &phint)) == 0)
		return;

	/* Here, we regenerate paths with the current hint restriction */
	if (found_hints & HINT_BM_SCAN_METHOD || found_hints & HINT_BM_PARALLEL)
	{
		/*
		 * When hint is specified on non-parent relations, discard existing
		 * paths and regenerate based on the hint considered. Otherwise we
		 * already have hinted childx paths then just adjust the number of
		 * planned number of workers.
		 */
		if (root->simple_rte_array[rel->relid]->inh)
		{
			/* enforce number of workers if requested */
			if (phint && phint->force_parallel)
			{
				if (phint->nworkers == 0)
				{
					list_free_deep(rel->partial_pathlist);
					rel->partial_pathlist = NIL;
				}
				else
				{
					/* prioritize partial paths */
					foreach (l, rel->partial_pathlist)
					{
						Path *ppath = (Path *) lfirst(l);

						if (ppath->parallel_safe)
						{
							ppath->parallel_workers	= phint->nworkers;
							ppath->startup_cost = 0;
							ppath->total_cost = 0;
						}
					}

					/* disable non-partial paths */
					foreach (l, rel->pathlist)
					{
						Path *ppath = (Path *) lfirst(l);

						if (ppath->startup_cost < disable_cost)
						{
							ppath->startup_cost += disable_cost;
							ppath->total_cost += disable_cost;
						}
					}
				}
			}
		}
		else
		{
			/* Just discard all the paths considered so far */
			list_free_deep(rel->pathlist);
			rel->pathlist = NIL;
			list_free_deep(rel->partial_pathlist);
			rel->partial_pathlist = NIL;

			/* Regenerate paths with the current enforcement */
			set_plain_rel_pathlist(root, rel, rte);

			/* Additional work to enforce parallel query execution */
			if (phint && phint->nworkers > 0)
			{
				/*
				 * For Parallel Append to be planned properly, we shouldn't set
				 * the costs of non-partial paths to disable-value.  Lower the
				 * priority of non-parallel paths by setting partial path costs
				 * to 0 instead.
				 */
				foreach (l, rel->partial_pathlist)
				{
					Path *path = (Path *) lfirst(l);

					path->startup_cost = 0;
					path->total_cost = 0;
				}

				/* enforce number of workers if requested */
				if (phint->force_parallel)
				{
					foreach (l, rel->partial_pathlist)
					{
						Path *ppath = (Path *) lfirst(l);

						if (ppath->parallel_safe)
							ppath->parallel_workers	= phint->nworkers;
					}
				}

				/* Generate gather paths */
				if (rel->reloptkind == RELOPT_BASEREL &&
					bms_membership(root->all_baserels) != BMS_SINGLETON)
					generate_gather_paths(root, rel, false);
			}
		}
	}

	reset_hint_enforcement();
}

/*
 * set_rel_pathlist
 *	  Build access paths for a base relation
 *
 * This function was copied and edited from set_rel_pathlist() in
 * src/backend/optimizer/path/allpaths.c in order not to copy other static
 * functions not required here.
 */
static void
set_rel_pathlist(PlannerInfo *root, RelOptInfo *rel,
				 Index rti, RangeTblEntry *rte)
{
	if (IS_DUMMY_REL(rel))
	{
		/* We already proved the relation empty, so nothing more to do */
	}
	else if (rte->inh)
	{
		/* It's an "append relation", process accordingly */
		set_append_rel_pathlist(root, rel, rti, rte);
	}
	else
	{
		if (rel->rtekind == RTE_RELATION)
		{
			if (rte->relkind == RELKIND_RELATION)
			{
				if(rte->tablesample != NULL)
					elog(ERROR, "sampled relation is not supported");

				/* Plain relation */
				set_plain_rel_pathlist(root, rel, rte);
			}
			else
				elog(ERROR, "unexpected relkind: %c", rte->relkind);
		}
		else
			elog(ERROR, "unexpected rtekind: %d", (int) rel->rtekind);
	}

	/*
	 * Allow a plugin to editorialize on the set of Paths for this base
	 * relation.  It could add new paths (such as CustomPaths) by calling
	 * add_path(), or delete or modify paths added by the core code.
	 */
	if (set_rel_pathlist_hook)
		(*set_rel_pathlist_hook) (root, rel, rti, rte);

	/* Now find the cheapest of the paths for this rel */
	set_cheapest(rel);
}

/*
 * stmt_beg callback is called when each query in PL/pgSQL function is about
 * to be executed.  At that timing, we save query string in the global variable
 * plpgsql_query_string to use it in planner hook.  It's safe to use one global
 * variable for the purpose, because its content is only necessary until
 * planner hook is called for the query, so recursive PL/pgSQL function calls
 * don't harm this mechanism.
 */
static void
pg_hint_plan_plpgsql_stmt_beg(PLpgSQL_execstate *estate, PLpgSQL_stmt *stmt)
{
	plpgsql_recurse_level++;
}

/*
 * stmt_end callback is called then each query in PL/pgSQL function has
 * finished.  At that timing, we clear plpgsql_query_string to tell planner
 * hook that next call is not for a query written in PL/pgSQL block.
 */
static void
pg_hint_plan_plpgsql_stmt_end(PLpgSQL_execstate *estate, PLpgSQL_stmt *stmt)
{
	plpgsql_recurse_level--;
}

void plpgsql_query_erase_callback(ResourceReleasePhase phase,
								  bool isCommit,
								  bool isTopLevel,
								  void *arg)
{
	if (!isTopLevel || phase != RESOURCE_RELEASE_AFTER_LOCKS)
		return;
	/* Cancel plpgsql nest level*/
	plpgsql_recurse_level = 0;
}



/*
 * cdbpath_motion_for_join_wrapper
 *
 * Decides where a join should be done.  Adds Motion operators atop
 * the subpaths if needed to deliver their results to the join locus.
 * Returns the join locus if ok, or a null locus otherwise. If
 * jointype is JOIN_SEMI_DEDUP or JOIN_SEMI_DEDUP_REVERSE, this also
 * tacks a RowIdExpr on one side of the join, and *p_rowidexpr_id is
 * set to the ID of that. The caller is expected to uniquefy
 * the result after the join, passing the rowidexpr_id to
 * create_unique_rowid_path().
 *
 * mergeclause_list is a List of RestrictInfo.  Its members are
 * the equijoin predicates between the outer and inner rel.
 * It comes from select_mergejoin_clauses() in joinpath.c.
 */
CdbPathLocus
cdbpath_motion_for_join_wrapper(PlannerInfo *root,
						JoinType jointype,	/* JOIN_INNER/FULL/LEFT/RIGHT/IN */
						Path **p_outer_path,	/* INOUT */
						Path **p_inner_path,	/* INOUT */
						int *p_rowidexpr_id,	/* OUT */
						List *redistribution_clauses, /* equijoin RestrictInfo list */
						List *restrict_clauses,
						List *outer_pathkeys,
						List *inner_pathkeys,
						bool outer_require_existing_order,
#ifdef MATRIXDB_VERSION
						bool inner_require_existing_order,
						bool consider_replicate,
						bool parallel_hash)
#else /* MATRIXDB_VERSION */
						bool inner_require_existing_order)
#endif /* MATRIXDB_VERSION */
{
	CdbpathMfjRel outer;
	CdbpathMfjRel inner;
	int			numsegments;
	bool		join_quals_contain_outer_references;
	ListCell   *lc;

	*p_rowidexpr_id = 0;

	outer.pathkeys = outer_pathkeys;
	inner.pathkeys = inner_pathkeys;
	outer.path = *p_outer_path;
	inner.path = *p_inner_path;
	outer.locus = outer.path->locus;
	inner.locus = inner.path->locus;
	CdbPathLocus_MakeNull(&outer.move_to);
	CdbPathLocus_MakeNull(&inner.move_to);

	Assert(cdbpathlocus_is_valid(outer.locus));
	Assert(cdbpathlocus_is_valid(inner.locus));

	/*
	 * Does the join quals contain references to outer query? If so, we must
	 * evaluate them in the outer query's locus. That means pulling both
	 * inputs to outer locus, and performing the join there.
	 *
	 * XXX: If there are pseudoconstant quals, they will be executed by a
	 * gating Result with a One-Time Filter. In that case, the join's inputs
	 * wouldn't need to be brought to the outer locus. We could execute the
	 * join normally, and bring the result to the outer locus and put the
	 * gating Result above the Motion, instead. But for now, we're not smart
	 * like that.
	 */
	join_quals_contain_outer_references = false;
	foreach(lc, restrict_clauses)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

		if (rinfo->contain_outer_query_references)
		{
			join_quals_contain_outer_references = true;
			break;
		}
	}

	/*
	 * Locus type Replicated can only be generated by join operation.
	 * And in the function cdbpathlocus_join there is a rule:
	 * <any locus type> join <Replicated> => any locus type
	 * Proof by contradiction, it shows that when code arrives here,
	 * is is impossible that any of the two input paths' locus
	 * is Replicated. So we add two asserts here.
	 */
	Assert(!CdbPathLocus_IsReplicated(outer.locus));
	Assert(!CdbPathLocus_IsReplicated(inner.locus));

	if (CdbPathLocus_IsReplicated(outer.locus) ||
		CdbPathLocus_IsReplicated(inner.locus))
		goto fail;

	outer.has_wts = cdbpath_contains_wts(outer.path);
	inner.has_wts = cdbpath_contains_wts(inner.path);

	/* For now, inner path should not contain WorkTableScan */
	Assert(!inner.has_wts);

	/*
	 * If outer rel contains WorkTableScan and inner rel is hash distributed,
	 * unfortunately we have to pretend that inner is randomly distributed,
	 * otherwise we may end up with redistributing outer rel.
	 */
	if (outer.has_wts && inner.locus.distkey != NIL)
#ifdef MATRIXDB_VERSION
		CdbPathLocus_MakeStrewn(&inner.locus,
								CdbPathLocus_NumSegments(inner.locus),
								inner.locus.contentids,
								inner.path->parallel_workers);
#else /* MATRIXDB_VERSION */
		CdbPathLocus_MakeStrewn(&inner.locus,
								CdbPathLocus_NumSegments(inner.locus));
#endif /* MATRIXDB_VERSION */

#ifdef MATRIXDB_VERSION
	/*
	 * If outer has wts, the outer's locus type always same with recursive
	 * cte's starting conditions. If outer is hash distributed with id, when
	 * join this node to inner node, inner's locus type has been changed to
	 * strewn, and would create a redistributed motion with distributed key
	 * id for inner node, so we also reset outer's locus type to strewn when
	 * the outer's locus type is hash distributed, replace redistributed motion
	 * to broadcast motion.
	 */
	if (outer.has_wts && outer.locus.distkey != NIL)
		CdbPathLocus_MakeStrewn(&outer.locus,
								CdbPathLocus_NumSegments(outer.locus),
								outer.locus.contentids,
								outer.path->parallel_workers);
#endif /* MATRIXDB_VERSION */

	/*
	 * Caller can specify an ordering for each source path that is the same as
	 * or weaker than the path's existing ordering. Caller may insist that we
	 * do not add motion that would lose the specified ordering property;
	 * otherwise the given ordering is preferred but not required. A required
	 * NIL ordering means no motion is allowed for that path.
	 */
	outer.require_existing_order = outer_require_existing_order;
	inner.require_existing_order = inner_require_existing_order;

	/*
	 * Don't consider replicating the preserved rel of an outer join, or the
	 * current-query rel of a join between current query and subquery.
	 *
	 * Path that contains WorkTableScan cannot be replicated.
	 */
	/* ok_to_replicate means broadcast */
#ifdef MATRIXDB_VERSION
	outer.ok_to_replicate = consider_replicate && !outer.has_wts;
	inner.ok_to_replicate = consider_replicate;
#else
	outer.ok_to_replicate = !outer.has_wts;
	inner.ok_to_replicate = true;
#endif
	switch (jointype)
	{
		case JOIN_INNER:
		case JOIN_UNIQUE_OUTER:
		case JOIN_UNIQUE_INNER:
			break;
		case JOIN_SEMI:
		case JOIN_ANTI:
		case JOIN_LEFT:
		case JOIN_LASJ_NOTIN:
			outer.ok_to_replicate = false;
			break;
		case JOIN_RIGHT:
			inner.ok_to_replicate = false;
			break;
		case JOIN_FULL:
			outer.ok_to_replicate = false;
			inner.ok_to_replicate = false;
			break;

		case JOIN_DEDUP_SEMI:

			/*
			 * In this plan type, we generate a unique row ID on the outer
			 * side of the join, perform the join, possibly broadcasting the
			 * outer side, and remove duplicates after the join, so that only
			 * one row for each input outer row remains.
			 *
			 * If the outer input is General or SegmentGeneral, it's available
			 * in all the segments, but we cannot reliably generate a row ID
			 * to distinguish each logical row in that case. So force the
			 * input to a single node first in that case.
			 *
			 * In previous Greenplum versions, we assumed that we can generate
			 * a unique row ID for General paths, by generating the same
			 * sequence of numbers on each segment. That works as long as the
			 * rows are in the same order on each segment, but it seemed like
			 * a risky assumption. And it didn't work on SegmentGeneral paths
			 * (i.e. replicated tables) anyway.
			 */
			if (!CdbPathLocus_IsPartitioned(inner.locus))
				goto fail;

			if (CdbPathLocus_IsPartitioned(outer.locus) ||
				CdbPathLocus_IsBottleneck(outer.locus))
			{
				/* ok */
			}
			else if (CdbPathLocus_IsGeneral(outer.locus))
			{
				CdbPathLocus_MakeSingleQE(&outer.locus,
										  CdbPathLocus_NumSegments(inner.locus));
				outer.path->locus = outer.locus;

			}
			else if (CdbPathLocus_IsSegmentGeneral(outer.locus))
			{
				CdbPathLocus_MakeSingleQE(&outer.locus,
										  CdbPathLocus_CommonSegments(inner.locus,
																	  outer.locus));
				outer.path->locus = outer.locus;
			}
			else
				goto fail;
			inner.ok_to_replicate = false;
			outer.path = add_rowid_to_path(root, outer.path, p_rowidexpr_id);
			*p_outer_path = outer.path;
			break;

		case JOIN_DEDUP_SEMI_REVERSE:
			/* same as JOIN_DEDUP_SEMI, but with inner and outer reversed */
			if (!CdbPathLocus_IsPartitioned(outer.locus))
				goto fail;
			if (CdbPathLocus_IsPartitioned(inner.locus) ||
				CdbPathLocus_IsBottleneck(inner.locus))
			{
				/* ok */
			}
			else if (CdbPathLocus_IsGeneral(inner.locus))
			{
				CdbPathLocus_MakeSingleQE(&inner.locus,
										  CdbPathLocus_NumSegments(outer.locus));
				inner.path->locus = inner.locus;
			}
			else if (CdbPathLocus_IsSegmentGeneral(inner.locus))
			{
				CdbPathLocus_MakeSingleQE(&inner.locus,
										  CdbPathLocus_CommonSegments(outer.locus,
																	  inner.locus));
				inner.path->locus = inner.locus;
			}
			else
				goto fail;
			outer.ok_to_replicate = false;
			inner.path = add_rowid_to_path(root, inner.path, p_rowidexpr_id);
			*p_inner_path = inner.path;
			break;

		default:

			/*
			 * The caller should already have transformed
			 * JOIN_UNIQUE_INNER/OUTER into JOIN_INNER
			 */
			elog(ERROR, "unexpected join type %d", jointype);
	}

	/* Get rel sizes. */
	outer.bytes = outer.path->rows * outer.path->pathtarget->width;
	inner.bytes = inner.path->rows * inner.path->pathtarget->width;

	if (join_quals_contain_outer_references)
	{
		if (CdbPathLocus_IsOuterQuery(outer.locus) &&
			CdbPathLocus_IsOuterQuery(inner.locus))
			return outer.locus;

		if (!CdbPathLocus_IsOuterQuery(outer.locus))
			CdbPathLocus_MakeOuterQuery(&outer.move_to);
		if (!CdbPathLocus_IsOuterQuery(inner.locus))
			CdbPathLocus_MakeOuterQuery(&inner.move_to);
	}
	else if (CdbPathLocus_IsOuterQuery(outer.locus) ||
			 CdbPathLocus_IsOuterQuery(inner.locus))
	{
		/*
		 * If one side of the join has "outer query" locus, must bring the
		 * other side there too.
		 */
		if (CdbPathLocus_IsOuterQuery(outer.locus) &&
			CdbPathLocus_IsOuterQuery(inner.locus))
			return outer.locus;

		if (CdbPathLocus_IsOuterQuery(outer.locus))
			inner.move_to = outer.locus;
		else
			outer.move_to = inner.locus;
	}
	else if (CdbPathLocus_IsGeneral(outer.locus) ||
			 CdbPathLocus_IsGeneral(inner.locus))
	{
		/*
		 * Motion not needed if either source is everywhere (e.g. a constant).
		 *
		 * But if a row is everywhere and is preserved in an outer join, we don't
		 * want to preserve it in every qExec process where it is unmatched,
		 * because that would produce duplicate null-augmented rows. So in that
		 * case, bring all the partitions to a single qExec to be joined. CDB
		 * TODO: Can this case be handled without introducing a bottleneck?
		 */
		/*
		 * The logic for the join result's locus is (outer's locus is general):
		 *   1. if outer is ok to replicated, then result's locus is the same
		 *      as inner's locus
		 *   2. if outer is not ok to replicated (like left join or wts cases)
		 *      2.1 if inner's locus is hashed or hashOJ, we try to redistribute
		 *          outer as the inner, if fails, make inner singleQE
		 *      2.2 if inner's locus is strewn, we try to redistribute
		 *          outer and inner, if fails, make inner singleQE
		 *      2.3 just return the inner's locus, no motion is needed
		 */
		CdbpathMfjRel *general = &outer;
		CdbpathMfjRel *other = &inner;

		/*
		 * both are general, the result is general
		 */
		if (CdbPathLocus_IsGeneral(outer.locus) &&
			CdbPathLocus_IsGeneral(inner.locus))
			return outer.locus;

		if (CdbPathLocus_IsGeneral(inner.locus))
		{
			general = &inner;
			other = &outer;
		}

		/* numsegments of General locus is always -1 */
		Assert(CdbPathLocus_NumSegments(general->locus) == -1);

		/*
		 * If general can happen everywhere (ok_to_replicate)
		 * then it acts like identity: 
		 *     General join other_locus => other_locus
		 */
		if (general->ok_to_replicate)
			return other->locus;

		if (!CdbPathLocus_IsPartitioned(other->locus))
		{
			/*
			 * If general is not ok_to_replicate, for example,
			 * generate_series(1, 10) left join xxxx, only for
			 * some specific locus types general can act as
			 * identity:
			 *    General join other_locus => other_locus, if and only if
			 *    other_locus in (singleQE, Entry).
			 * Here other's locus:
			 *    - cannot be general (it has already handled)
			 *    - cannot be replicated (assert at the beginning of the function)
			 */
			Assert(CdbPathLocus_IsBottleneck(other->locus) ||
				   CdbPathLocus_IsSegmentGeneral(other->locus));
			return other->locus;
		}
		/*
		 * If other's locus is partitioned, we first try to
		 * add redistribute motion, if fails, we gather other
		 * to singleQE.
		 */
		else if (!try_redistribute(root, general, other, redistribution_clauses))
		{
			/*
			 * FIXME: do we need test other's movable?
			 */
			CdbPathLocus_MakeSingleQE(&other->move_to,
									  CdbPathLocus_NumSegments(other->locus));
		}
	}
	else if (CdbPathLocus_IsSegmentGeneral(outer.locus) ||
			 CdbPathLocus_IsSegmentGeneral(inner.locus))
	{
		/*
		 * the whole branch handles the case that at least
		 * one of the two locus is SegmentGeneral. The logic
		 * is:
		 *   - if both are SegmentGeneral:
		 *       1. if both locus are equal, no motion needed, simply return
		 *       2. For update cases. If resultrelation
		 *          is SegmentGeneral, the update must execute
		 *          on each segment of the resultrelation, if resultrelation's
		 *          numsegments is larger, the only solution is to broadcast
		 *          other
		 *       3. no motion is needed, change both numsegments to common
		 *   - if only one of them is SegmentGeneral :
		 *       1. consider update case, if resultrelation is SegmentGeneral,
		 *          the only solution is to broadcast the other
		 *       2. if other's locus is singleQE or entry, make SegmentGeneral
		 *          to other's locus
		 *       3. the remaining possibility of other's locus is partitioned
		 *          3.1 if SegmentGeneral is not ok_to_replicate, try to
		 *              add redistribute motion, if fails gather each to
		 *              singleQE
		 *          3.2 if SegmentGeneral's numsegments is larger, just return
		 *              other's locus
		 *          3.3 try to add redistribute motion, if fails, gather each
		 *              to singleQE
		 */
		CdbpathMfjRel *segGeneral;
		CdbpathMfjRel *other;

		if (CdbPathLocus_IsSegmentGeneral(outer.locus) &&
			CdbPathLocus_IsSegmentGeneral(inner.locus))
		{
			/*
			 * use_common to indicate whether we should
			 * return a segmentgeneral locus with common
			 * numsegments.
			 */
			bool use_common = true;

#ifdef MATRIXDB_VERSION
			int			numcommon;
			int16	   *commoncontentids;

			commoncontentids = find_locus_common_contentids(outer.locus.contentids,
															outer.locus.numsegments,
															inner.locus.contentids,
															inner.locus.numsegments,
															&numcommon);
			/* Handle the case of two same locuses */
			if ((CdbPathLocus_NumSegments(outer.locus) == numcommon) &&
				(CdbPathLocus_NumSegments(inner.locus) == numcommon))
				return inner.locus;
#else /* MATRIXDB_VERSION */
			/*
			 * Handle the case two same locus
			 */
			if (CdbPathLocus_NumSegments(outer.locus) ==
				CdbPathLocus_NumSegments(inner.locus))
				return inner.locus;
#endif /* MATRIXDB_VERSION */

#ifdef MATRIXDB_VERSION
			/*
			 * Now, two locus' segments not equal
			 * We should consider update resultrelation
			 * if update,
			 *   - resultrelation's segments not covered by the other one's, then
			 *     we should broadcast the other
			 *   - otherwise, results is common
			 * else:
			 *   common
			 */
#else /* MATRIXDB_VERSION */
			/*
			 * Now, two locus' numsegments not equal
			 * We should consider update resultrelation
			 * if update,
			 *   - resultrelation's numsegments larger, then
			 *     we should broadcast the other
			 *   - otherwise, results is common
			 * else:
			 *   common
			 */
#endif /* MATRIXDB_VERSION */
			if (root->upd_del_replicated_table > 0)
			{
#ifdef MATRIXDB_VERSION
				;
				if ((CdbPathLocus_NumSegments(outer.locus) > numcommon) &&
					bms_is_member(root->upd_del_replicated_table,
								  outer.path->parent->relids) && enable_boradcast_on_rel(root, outer.path->parent))
#else /* MATRIXDB_VERSION */
				if ((CdbPathLocus_NumSegments(outer.locus) >
					 CdbPathLocus_NumSegments(inner.locus)) &&
					bms_is_member(root->upd_del_replicated_table,
								  outer.path->parent->relids) && enable_boradcast_on_rel(root, outer.path->parent))
#endif /* MATRIXDB_VERSION */
				{
#ifdef MATRIXDB_VERSION
					/*
					 * the updated resultrelation is replicated table
					 * and its segments are not covered, we should broadcast
					 * the other path
					 */
#else /* MATRIXDB_VERSION */
					/*
					 * the updated resultrelation is replicated table
					 * and its numsegments is larger, we should broadcast
					 * the other path
					 */
#endif /* MATRIXDB_VERSION */
					if (!inner.ok_to_replicate)
						goto fail;

					/*
					 * FIXME: do we need to test inner's movable?
					 */
#ifdef MATRIXDB_VERSION
					/* parallel mode is disabled for UPDATE/INSERT/DELETE */
					Assert(outer.path->parallel_workers == 0);
					CdbPathLocus_MakeReplicated(&inner.move_to,
												CdbPathLocus_NumSegments(outer.locus),
												outer.locus.contentids,
												0);
#else /* MATRIXDB_VERSION */
					CdbPathLocus_MakeReplicated(&inner.move_to,
												CdbPathLocus_NumSegments(outer.locus));
#endif /* MATRIXDB_VERSION */

					use_common = false;
				}
#ifdef MATRIXDB_VERSION
				else if ((CdbPathLocus_NumSegments(inner.locus) > numcommon) &&
						 bms_is_member(root->upd_del_replicated_table,
									   inner.path->parent->relids) && enable_boradcast_on_rel(root, inner.path->parent))
#else /* MATRIXDB_VERSION */
				else if ((CdbPathLocus_NumSegments(outer.locus) <
						  CdbPathLocus_NumSegments(inner.locus)) &&
						 bms_is_member(root->upd_del_replicated_table,
									   inner.path->parent->relids) && enable_boradcast_on_rel(root, inner.path->parent))
#endif /* MATRIXDB_VERSION */
				{
#ifdef MATRIXDB_VERSION
					/*
					 * the updated resultrelation is replicated table
					 * and its segments are not covered, we should broadcast
					 * the other path
					 */
#else /* MATRIXDB_VERSION */
					/*
					 * the updated resultrelation is replicated table
					 * and its numsegments is larger, we should broadcast
					 * the other path
					 */
#endif /* MATRIXDB_VERSION */
					if (!outer.ok_to_replicate)
						goto fail;

					/*
					 * FIXME: do we need to test outer's movable?
					 */
#ifdef MATRIXDB_VERSION
					/* parallel mode is disabled for UPDATE/INSERT/DELETE */
					Assert(inner.path->parallel_workers == 0);
					CdbPathLocus_MakeReplicated(&outer.move_to,
												CdbPathLocus_NumSegments(inner.locus),
												inner.locus.contentids,
												0);
#else /* MATRIXDB_VERSION */
					CdbPathLocus_MakeReplicated(&outer.move_to,
												CdbPathLocus_NumSegments(inner.locus));
#endif /* MATRIXDB_VERSION */

					use_common = false;
				}
			}
			
			if (use_common)
			{
#ifdef MATRIXDB_VERSION
				/* The statement is not update a replicated table. */
				if (numcommon == 0)
				{
					/*
					 * No common segments, bring both sides to a same single QE.
					 * Or we can redistribute each side on their join keys respectively,
					 * to a same set of segments. Normally replicated table should
					 * be not large, so we simply move them both to one segment.
					 */
					numcommon = CdbPathLocus_CommonSegments(outer.locus,
															inner.locus);
					CdbPathLocus_MakeSingleQE(&outer.move_to, numcommon);
					CdbPathLocus_MakeSingleQE(&inner.move_to, numcommon);
				}
				else
				{
					/* Just return the segmentgeneral with common segments. */
					outer.locus.numsegments = numcommon;
					outer.locus.contentids = commoncontentids;
					inner.locus.numsegments = numcommon;
					inner.locus.contentids = commoncontentids;
					return inner.locus;
				}
#else /* MATRIXDB_VERSION */
				/*
				 * The statement is not update a replicated table.
				 * Just return the segmentgeneral with a smaller numsegments.
				 */
				numsegments = CdbPathLocus_CommonSegments(inner.locus,
														  outer.locus);
				outer.locus.numsegments = numsegments;
				inner.locus.numsegments = numsegments;

				return inner.locus;
#endif /* MATRIXDB_VERSION */
			}
		}
		else
		{
			if (CdbPathLocus_IsSegmentGeneral(outer.locus))
			{
				segGeneral = &outer;
				other = &inner;
			}
			else
			{
				segGeneral = &inner;
				other = &outer;
			}

			Assert(CdbPathLocus_IsBottleneck(other->locus) ||
				   CdbPathLocus_IsPartitioned(other->locus));
			
			/*
			 * For UPDATE/DELETE, replicated table can't guarantee a logic row has
			 * same ctid or item pointer on each copy. If we broadcast matched tuples
			 * to all segments, the segments may update the wrong tuples or can't
			 * find a valid tuple according to ctid or item pointer.
			 *
			 * So For UPDATE/DELETE on replicated table, we broadcast other path so
			 * all target tuples can be selected on all copys and then be updated
			 * locally.
			 */
			if (root->upd_del_replicated_table > 0 &&
				bms_is_member(root->upd_del_replicated_table,
							  segGeneral->path->parent->relids) && enable_boradcast_on_rel(root, segGeneral->path->parent))
			{
				/*
				 * For UPDATE on a replicated table, we have to do it
				 * everywhere so that for each segment, we have to collect
				 * all the information of other that is we should broadcast it
				 */
				
				/*
				 * FIXME: do we need to test other's movable?
				 */
#ifdef MATRIXDB_VERSION
				/* parallel mode is disabled for UPDATE/INSERT/DELETE */
				Assert(segGeneral->path->parallel_workers == 0);
				CdbPathLocus_MakeReplicated(&other->move_to,
											CdbPathLocus_NumSegments(segGeneral->locus),
											segGeneral->locus.contentids,
											0);
#else /* MATRIXDB_VERSION */
				CdbPathLocus_MakeReplicated(&other->move_to,
											CdbPathLocus_NumSegments(segGeneral->locus));
#endif /* MATRIXDB_VERSION */
			}
			else if (CdbPathLocus_IsBottleneck(other->locus))
			{
#ifdef MATRIXDB_VERSION
				/* Bring the SegmentGeneral locus to the singleton one */
				segGeneral->move_to = other->locus;
#else /* MATRIXDB_VERSION */
				/*
				 * if the locus type is equal and segment count is unequal,
				 * we will dispatch the one on more segments to the other
				 */
				numsegments = CdbPathLocus_CommonSegments(segGeneral->locus,
														  other->locus);
				segGeneral->move_to = other->locus;
				segGeneral->move_to.numsegments = numsegments;
#endif /* MATRIXDB_VERSION */
			}
			else
			{
				/*
				 * This branch handles for partitioned other locus
				 * hashed, hashoj, strewn
				 */
				Assert(CdbPathLocus_IsPartitioned(other->locus));
				
				if (!segGeneral->ok_to_replicate)
				{
					if (!try_redistribute(root, segGeneral,
										  other, redistribution_clauses))
					{
						/*
						 * FIXME: do we need to test movable?
						 */
#ifdef MATRIXDB_VERSION
						/* Bring both sides to a same single QE */
						int numcommon = CdbPathLocus_CommonSegments(segGeneral->locus,
																	other->locus);
						CdbPathLocus_MakeSingleQE(&segGeneral->move_to, numcommon);
						CdbPathLocus_MakeSingleQE(&other->move_to, numcommon);
#else /* MATRIXDB_VERSION */
						CdbPathLocus_MakeSingleQE(&segGeneral->move_to,
												  CdbPathLocus_NumSegments(segGeneral->locus));
						CdbPathLocus_MakeSingleQE(&other->move_to,
												  CdbPathLocus_NumSegments(other->locus));
#endif /* MATRIXDB_VERSION */
					}
				}
				else
				{
					/*
					 * If all other's segments have segGeneral stored, then no motion
					 * is needed.
					 *
					 * A sql to reach here:
					 *     select * from d2 a join r1 b using (c1);
					 * where d2 is a replicated table on 2 segment,
					 *       r1 is a random table on 1 segments.
					 */
#ifdef MATRIXDB_VERSION
					int		numcommon;
					int16	*commoncontentids;
					commoncontentids = find_locus_common_contentids(segGeneral->locus.contentids,
																	segGeneral->locus.numsegments,
																	other->locus.contentids,
																	other->locus.numsegments,
																	&numcommon);
#endif /* MATRIXDB_VERSION */

#ifdef MATRIXDB_VERSION
					if (CdbPathLocus_NumSegments(other->locus) == numcommon)
#else /* MATRIXDB_VERSION */
					if (CdbPathLocus_NumSegments(segGeneral->locus) >=
						CdbPathLocus_NumSegments(other->locus))
#endif /* MATRIXDB_VERSION */
						return other->locus;
					else
					{
						if (!try_redistribute(root, segGeneral,
											  other, redistribution_clauses))
						{
#ifdef MATRIXDB_VERSION
							/*
							 * FIXME: do we need to test movable?
							 */
							/* We don't use the above numcommon since it may be 0 */
							numcommon = CdbPathLocus_CommonSegments(segGeneral->locus,
																	other->locus);
							CdbPathLocus_MakeSingleQE(&segGeneral->move_to, numcommon);
							CdbPathLocus_MakeSingleQE(&other->move_to, numcommon);
#else /* MATRIXDB_VERSION */
							numsegments = CdbPathLocus_CommonSegments(segGeneral->locus,
																	  other->locus);
							/*
							 * FIXME: do we need to test movable?
							 */
							CdbPathLocus_MakeSingleQE(&segGeneral->move_to, numsegments);
							CdbPathLocus_MakeSingleQE(&other->move_to, numsegments);
#endif /* MATRIXDB_VERSION */
						}
					}
				}
			}
		}
	}
	/*
	 * Is either source confined to a single process? NB: Motion to a single
	 * process (qDisp or qExec) is the only motion in which we may use Merge
	 * Receive to preserve an existing ordering.
	 */
	else if (CdbPathLocus_IsBottleneck(outer.locus) ||
			 CdbPathLocus_IsBottleneck(inner.locus))
	{							/* singleQE or entry db */
		CdbpathMfjRel *single = &outer;
		CdbpathMfjRel *other = &inner;
		bool		single_immovable = (outer.require_existing_order &&
										!outer_pathkeys) || outer.has_wts;
		bool		other_immovable = inner.require_existing_order &&
		!inner_pathkeys;

		/*
		 * If each of the sources has a single-process locus, then assign both
		 * sources and the join to run in the same process, without motion.
		 * The slice will be run on the entry db if either source requires it.
		 */
		if (CdbPathLocus_IsEntry(single->locus))
		{
			if (CdbPathLocus_IsBottleneck(other->locus))
				return single->locus;
		}
		else if (CdbPathLocus_IsSingleQE(single->locus))
		{
			if (CdbPathLocus_IsBottleneck(other->locus))
			{
				/*
				 * Can join directly on one of the common segments.
				 */
				numsegments = CdbPathLocus_CommonSegments(outer.locus,
														  inner.locus);

				other->locus.numsegments = numsegments;
				return other->locus;
			}
		}

		/* Let 'single' be the source whose locus is singleQE or entry. */
		else
		{
			CdbSwap(CdbpathMfjRel *, single, other);
			CdbSwap(bool, single_immovable, other_immovable);
		}

		Assert(CdbPathLocus_IsBottleneck(single->locus));
		Assert(CdbPathLocus_IsPartitioned(other->locus));

		/* If the bottlenecked rel can't be moved, bring the other rel to it. */
		if (single_immovable)
		{
			if (other_immovable)
				goto fail;
			else
				other->move_to = single->locus;
		}

		/* Redistribute single rel if joining on other rel's partitioning key */
		else if (enable_redistribute_on_rel(root, single->path->parent) && 
			cdbpath_match_preds_to_distkey(root,
												redistribution_clauses,
												other->path,
												other->locus,
												&single->move_to))	/* OUT */
		{
			AssertEquivalent(CdbPathLocus_NumSegments(other->locus),
							 CdbPathLocus_NumSegments(single->move_to));

#ifdef MATRIXDB_VERSION
			Assert(cdbpathlocus_contentids_equal(other->locus, single->move_to));
#endif /* MATRIXDB_VERSION */
		}

		/* Replicate single rel if cheaper than redistributing both rels. */
#ifdef MATRIXDB_VERSION
		else if (single->ok_to_replicate &&
				 (single->bytes * cdbpath_parallel_workers(other->path) <
				  single->bytes + other->bytes) && enable_boradcast_on_rel(root, single->path->parent))
			CdbPathLocus_MakeReplicated(&single->move_to,
										CdbPathLocus_NumSegments(other->locus),
										other->locus.contentids,
										other->path->parallel_workers);
#else /* MATRIXDB_VERSION */
		else if (single->ok_to_replicate &&
				 (single->bytes * CdbPathLocus_NumSegments(other->locus) <
				  single->bytes + other->bytes) && enable_boradcast_on_rel(root, single->path->parent))
			CdbPathLocus_MakeReplicated(&single->move_to,
										CdbPathLocus_NumSegments(other->locus));
#endif /* MATRIXDB_VERSION */

		/*
		 * Redistribute both rels on equijoin cols.
		 *
		 * Redistribute both to the same segments, here we choose the
		 * same segments with other.
		 */
		else if (!other_immovable &&
				 enable_redistribute_on_rel(root, single->path->parent) &&
				 enable_redistribute_on_rel(root, other->path->parent) &&
				 cdbpath_distkeys_from_preds(root,
											 redistribution_clauses,
											 single->path,
											 CdbPathLocus_NumSegments(other->locus),
#ifdef MATRIXDB_VERSION
											 other->locus.contentids,
											 Max(single->path->parallel_workers,
												 other->path->parallel_workers),
#endif /* MATRIXDB_VERSION */
											 &single->move_to,	/* OUT */
											 &other->move_to))	/* OUT */
		{
			/* ok */
		}

		/* Broadcast single rel for below cases. */
		else if (single->ok_to_replicate &&
				 (other_immovable ||
				  single->bytes < other->bytes ||
				  other->has_wts) && enable_boradcast_on_rel(root, single->path->parent))
#ifdef MATRIXDB_VERSION
			CdbPathLocus_MakeReplicated(&single->move_to,
										CdbPathLocus_NumSegments(other->locus),
										other->locus.contentids,
										other->path->parallel_workers);
#else /* MATRIXDB_VERSION */
			CdbPathLocus_MakeReplicated(&single->move_to,
										CdbPathLocus_NumSegments(other->locus));
#endif /* MATRIXDB_VERSION */

		/* Last resort: If possible, move all partitions of other rel to single QE. */
		else if (!other_immovable)
			other->move_to = single->locus;
		else
			goto fail;
	}							/* singleQE or entry */

	/*
	 * No motion if partitioned alike and joining on the partitioning keys.
	 */
	
#ifdef MATRIXDB_VERSION
	else if (cdbpath_match_preds_to_both_distkeys(root, redistribution_clauses,
												  outer.path, inner.path,
												  outer.locus, inner.locus,
												  parallel_hash)) 
		return cdbpathlocus_join(jointype, outer.locus, inner.locus);
												  
#else /* MATRIXDB_VERSION */
	else if (cdbpath_match_preds_to_both_distkeys(root, redistribution_clauses,
												  outer.locus, inner.locus))
		return cdbpathlocus_join(jointype, outer.locus, inner.locus);
#endif /* MATRIXDB_VERSION */

	/*
	 * Both sources are partitioned.  Redistribute or replicate one or both.
	 */
	else
	{							/* partitioned */
		CdbpathMfjRel *large_rel = &outer;
		CdbpathMfjRel *small_rel = &inner;

		/* Which rel is bigger? */
		if (large_rel->bytes < small_rel->bytes)
			CdbSwap(CdbpathMfjRel *, large_rel, small_rel);

		/* Both side are distribued in 1 segment, it can join without motion. */
#ifdef MATRIXDB_VERSION
		if (CdbPathLocus_NumSegments(large_rel->locus) == 1 &&
			CdbPathLocus_NumSegments(small_rel->locus) == 1 &&
			!(CdbPathLocus_ParallelWorkers(large_rel->locus) > 0 &&
			  CdbPathLocus_ParallelWorkers(small_rel->locus) > 0) &&
			cdbpathlocus_contentids_equal(large_rel->locus, small_rel->locus))
		{
			/* Join locus should be consistent with the partial path */
			if (small_rel->locus.parallel_workers > large_rel->locus.parallel_workers)
				return small_rel->locus;
			else
				return large_rel->locus;
		}
#else /* MATRIXDB_VERSION */
		if (CdbPathLocus_NumSegments(large_rel->locus) == 1 &&
			CdbPathLocus_NumSegments(small_rel->locus) == 1)
			return large_rel->locus;
#endif /* MATRIXDB_VERSION */

		/* If joining on larger rel's partitioning key, redistribute smaller. */
		if (!small_rel->require_existing_order &&
			enable_redistribute_on_rel(root, small_rel->path->parent) &&
			cdbpath_match_preds_to_distkey(root,
										   redistribution_clauses,
										   large_rel->path,
										   large_rel->locus,
										   &small_rel->move_to))	/* OUT */
		{
			AssertEquivalent(CdbPathLocus_NumSegments(large_rel->locus),
							 CdbPathLocus_NumSegments(small_rel->move_to));

#ifdef MATRIXDB_VERSION
			Assert(cdbpathlocus_contentids_equal(large_rel->locus, small_rel->move_to));
#endif /* MATRIXDB_VERSION */
		}

		/*
		 * Replicate smaller rel if cheaper than redistributing larger rel.
		 * But don't replicate a rel that is to be preserved in outer join.
		 */
#ifdef MATRIXDB_VERSION
		else if (!small_rel->require_existing_order &&
				 small_rel->ok_to_replicate &&
				 (small_rel->bytes * cdbpath_parallel_workers(large_rel->path) <
				  large_rel->bytes) && enable_boradcast_on_rel(root, small_rel->path->parent))
			CdbPathLocus_MakeReplicated(&small_rel->move_to,
										CdbPathLocus_NumSegments(large_rel->locus),
										large_rel->locus.contentids,
										large_rel->path->parallel_workers);
#else /* MATRIXDB_VERSION */
		else if (!small_rel->require_existing_order &&
				 small_rel->ok_to_replicate &&
				 (small_rel->bytes * CdbPathLocus_NumSegments(large_rel->locus) <
				  large_rel->bytes) && enable_boradcast_on_rel(root, small_rel->path->parent))
			CdbPathLocus_MakeReplicated(&small_rel->move_to,
										CdbPathLocus_NumSegments(large_rel->locus));
#endif /* MATRIXDB_VERSION */

		/*
		 * Replicate larger rel if cheaper than redistributing smaller rel.
		 * But don't replicate a rel that is to be preserved in outer join.
		 */
#ifdef MATRIXDB_VERSION
		else if (!large_rel->require_existing_order &&
				 large_rel->ok_to_replicate &&
				 (large_rel->bytes * cdbpath_parallel_workers(small_rel->path) <
				  small_rel->bytes) && enable_boradcast_on_rel(root, large_rel->path->parent))
			CdbPathLocus_MakeReplicated(&large_rel->move_to,
										CdbPathLocus_NumSegments(small_rel->locus),
										small_rel->locus.contentids,
										small_rel->path->parallel_workers);
#else /* MATRIXDB_VERSION */
		else if (!large_rel->require_existing_order &&
				 large_rel->ok_to_replicate &&
				 (large_rel->bytes * CdbPathLocus_NumSegments(small_rel->locus) <
				  small_rel->bytes) && enable_boradcast_on_rel(root, large_rel->path->parent))
			CdbPathLocus_MakeReplicated(&large_rel->move_to,
										CdbPathLocus_NumSegments(small_rel->locus));
#endif /* MATRIXDB_VERSION */

		/* If joining on smaller rel's partitioning key, redistribute larger. */
		else if (!large_rel->require_existing_order &&
				 enable_redistribute_on_rel(root, large_rel->path->parent) &&
				 cdbpath_match_preds_to_distkey(root,
												redistribution_clauses,
												small_rel->path,
												small_rel->locus,
												&large_rel->move_to))	/* OUT */
		{
			AssertEquivalent(CdbPathLocus_NumSegments(small_rel->locus),
							 CdbPathLocus_NumSegments(large_rel->move_to));

#ifdef MATRIXDB_VERSION
			Assert(cdbpathlocus_contentids_equal(small_rel->locus, large_rel->move_to));
#endif /* MATRIXDB_VERSION */
		}

		/* Replicate smaller rel if cheaper than redistributing both rels. */
#ifdef MATRIXDB_VERSION
		else if (!small_rel->require_existing_order &&
				 small_rel->ok_to_replicate &&
				 (small_rel->bytes * cdbpath_parallel_workers(large_rel->path) <
				  small_rel->bytes + large_rel->bytes) && enable_boradcast_on_rel(root, small_rel->path->parent))
			CdbPathLocus_MakeReplicated(&small_rel->move_to,
										CdbPathLocus_NumSegments(large_rel->locus),
										large_rel->locus.contentids,
										large_rel->path->parallel_workers);
#else /* MATRIXDB_VERSION */
		else if (!small_rel->require_existing_order &&
				 small_rel->ok_to_replicate &&
				 (small_rel->bytes * CdbPathLocus_NumSegments(large_rel->locus) <
				  small_rel->bytes + large_rel->bytes) && enable_boradcast_on_rel(root, small_rel->path->parent))
			CdbPathLocus_MakeReplicated(&small_rel->move_to,
										CdbPathLocus_NumSegments(large_rel->locus));
#endif /* MATRIXDB_VERSION */

		/* Replicate largeer rel if cheaper than redistributing both rels. */
#ifdef MATRIXDB_VERSION
		else if (!large_rel->require_existing_order &&
				 large_rel->ok_to_replicate &&
				 (large_rel->bytes * cdbpath_parallel_workers(small_rel->path) <
				  large_rel->bytes + small_rel->bytes) && enable_boradcast_on_rel(root, large_rel->path->parent))
			CdbPathLocus_MakeReplicated(&large_rel->move_to,
										CdbPathLocus_NumSegments(small_rel->locus),
										small_rel->locus.contentids,
										small_rel->path->parallel_workers);
#else /* MATRIXDB_VERSION */
		else if (!large_rel->require_existing_order &&
				 large_rel->ok_to_replicate &&
				 (large_rel->bytes * CdbPathLocus_NumSegments(small_rel->locus) <
				  large_rel->bytes + small_rel->bytes) && enable_boradcast_on_rel(root, large_rel->path->parent))
			CdbPathLocus_MakeReplicated(&large_rel->move_to,
										CdbPathLocus_NumSegments(small_rel->locus));
#endif /* MATRIXDB_VERSION */

#ifdef MATRIXDB_VERSION
		/*
		 * Redistribute both rels on equijoin cols.
		 *
		 * It is hard to say if it is better to distribute the results
		 * on large_rel's segment map, just simply choose one now.
		 */
#else /* MATRIXDB_VERSION */
		/*
		 * Redistribute both rels on equijoin cols.
		 *
		 * the two results should all be distributed on the same segments,
		 * here we make them the same with common segments for safe
		 * TODO: how about distribute them both to ALL segments?
		 */
#endif /* MATRIXDB_VERSION */
		else if (!small_rel->require_existing_order &&
				 !small_rel->has_wts &&
				 !large_rel->require_existing_order &&
				 !large_rel->has_wts &&
				 enable_redistribute_on_rel(root, small_rel->path->parent) &&
				 enable_redistribute_on_rel(root, large_rel->path->parent) &&
				 cdbpath_distkeys_from_preds(root,
											 redistribution_clauses,
											 large_rel->path,
#ifdef MATRIXDB_VERSION
											 large_rel->locus.numsegments,
											 large_rel->locus.contentids,
											 Max(large_rel->path->parallel_workers,
												 small_rel->path->parallel_workers),
#else /* MATRIXDB_VERSION */
											 CdbPathLocus_CommonSegments(large_rel->locus,
																		 small_rel->locus),
#endif /* MATRIXDB_VERSION */
											 &large_rel->move_to,
											 &small_rel->move_to))
		{
			/* ok */
		}

		/*
		 * No usable equijoin preds, or couldn't consider the preferred
		 * motion. Replicate one rel if possible. MPP TODO: Consider number of
		 * seg dbs per host.
		 */
		else if (!small_rel->require_existing_order &&
				 small_rel->ok_to_replicate && enable_boradcast_on_rel(root, small_rel->path->parent))
#ifdef MATRIXDB_VERSION
			CdbPathLocus_MakeReplicated(&small_rel->move_to,
										CdbPathLocus_NumSegments(large_rel->locus),
										large_rel->locus.contentids,
										large_rel->path->parallel_workers);
#else /* MATRIXDB_VERSION */
			CdbPathLocus_MakeReplicated(&small_rel->move_to,
										CdbPathLocus_NumSegments(large_rel->locus));
#endif /* MATRIXDB_VERSION */
		else if (!large_rel->require_existing_order &&
				 large_rel->ok_to_replicate && enable_boradcast_on_rel(root, large_rel->path->parent))
#ifdef MATRIXDB_VERSION
			CdbPathLocus_MakeReplicated(&large_rel->move_to,
										CdbPathLocus_NumSegments(small_rel->locus),
										small_rel->locus.contentids,
										small_rel->path->parallel_workers);
#else /* MATRIXDB_VERSION */
			CdbPathLocus_MakeReplicated(&large_rel->move_to,
										CdbPathLocus_NumSegments(small_rel->locus));
#endif /* MATRIXDB_VERSION */

		/* Last resort: Move both rels to a single qExec. */
		else
		{
			int numsegments = CdbPathLocus_CommonSegments(outer.locus,
														  inner.locus);
			CdbPathLocus_MakeSingleQE(&outer.move_to, numsegments);
			CdbPathLocus_MakeSingleQE(&inner.move_to, numsegments);
		}
	}							/* partitioned */

	/*
	 * Move outer.
	 */
	if (!CdbPathLocus_IsNull(outer.move_to))
	{   
	    // set guc enable_broadcast_motion before call cdbpath_create_motion_path, reset it after call
	    int				save_nestlevel;
	    save_nestlevel = NewGUCNestLevel();
	    set_motion_config_options_for_rel(root, outer.path->parent);
		outer.path = cdbpath_create_motion_path(root,
												outer.path,
												outer_pathkeys,
												outer.require_existing_order,
												outer.move_to);
		
		/*
		 * Restore the GUC variables we set above.
		 */
		AtEOXact_GUC(true, save_nestlevel);
		
		if (!outer.path)		/* fail if outer motion not feasible */
			goto fail;

		if (IsA(outer.path, MaterialPath) && !root->config->may_rescan)
		{
			/*
			 * If we are the outer path and can never be rescanned,
			 * we could remove the materialize path.
			 */
			MaterialPath *mpath = (MaterialPath *) outer.path;
			outer.path = mpath->subpath;
		}
	}

	/*
	 * Move inner.
	 */
	if (!CdbPathLocus_IsNull(inner.move_to))
	{   
	    // set guc enable_broadcast_motion before call cdbpath_create_motion_path, reset it after call
	    int				save_nestlevel;
	    save_nestlevel = NewGUCNestLevel();
	    set_motion_config_options_for_rel(root, inner.path->parent);
		inner.path = cdbpath_create_motion_path(root,
												inner.path,
												inner_pathkeys,
												inner.require_existing_order,
												inner.move_to);
		
		/*
		 * Restore the GUC variables we set above.
		 */
		AtEOXact_GUC(true, save_nestlevel);
		
		if (!inner.path)		/* fail if inner motion not feasible */
			goto fail;
	}

	/*
	 * Ok to join.  Give modified subpaths to caller.
	 */
	*p_outer_path = outer.path;
	*p_inner_path = inner.path;

	/* Tell caller where the join will be done. */
	return cdbpathlocus_join(jointype, outer.path->locus, inner.path->locus);

fail:							/* can't do this join */
	CdbPathLocus_MakeNull(&outer.move_to);
	return outer.move_to;
}								/* cdbpath_motion_for_join_wrapper */

bool
enable_boradcast_on_rel(PlannerInfo *root, RelOptInfo *rel)
{
	if (rel->reloptkind != RELOPT_BASEREL)
		return false;

	MotionHint *motion_hint;
	motion_hint = find_motion_hint(root, rel->relid);

	if (motion_hint != NULL)
	{
		if (motion_hint->enforce_mask & ENABLE_BROADCASTMOTION)
			return true;
		else
			return false;
	}
	else
	{
		return enable_broadcast_motion;
	}
}

bool
enable_redistribute_on_rel(PlannerInfo *root, RelOptInfo *rel)
{
	if (rel->reloptkind != RELOPT_BASEREL)
		return false;

	MotionHint *motion_hint;
	motion_hint = find_motion_hint(root, rel->relid);

	if (motion_hint != NULL)
	{
		if (motion_hint->enforce_mask & ENABLE_REDISTRIBUTEMOTION)
			return true;
		else
			return false;
	}
	else
	{
		return pg_hint_plan_enable_redistribute_motion;
	}
}

#define standard_join_search pg_hint_plan_standard_join_search
#define join_search_one_level pg_hint_plan_join_search_one_level
#define make_join_rel make_join_rel_wrapper
#include "core.c"

#undef make_join_rel
#define make_join_rel pg_hint_plan_make_join_rel
#define add_paths_to_joinrel add_paths_to_joinrel_wrapper
#include "make_join_rel.c"

#include "pg_stat_statements.c"

#undef add_paths_to_joinrel
#define add_paths_to_joinrel add_paths_to_joinrel_motion_wrapper
#define cdbpath_motion_for_join cdbpath_motion_for_join_wrapper
#define create_hashjoin_path pg_hint_plan_create_hashjoin_path
#define create_mergejoin_path pg_hint_plan_create_mergejoin_path
#define create_nestloop_path pg_hint_plan_create_nestloop_path
#include "motion.c"
