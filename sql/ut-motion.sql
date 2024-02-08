SET search_path TO public;

CREATE SCHEMA s1;

CREATE TABLE t1 (id int PRIMARY KEY, val int) DISTRIBUTED BY (id);
CREATE TABLE t2 (id int PRIMARY KEY, val int) DISTRIBUTED BY (id);
CREATE TABLE t3 (id int PRIMARY KEY, val int);
INSERT INTO t1 SELECT i, i % 100 FROM (SELECT generate_series(1, 10000) i) t;
INSERT INTO t2 SELECT i, i % 10 FROM (SELECT generate_series(1, 1000) i) t;
INSERT INTO t3 SELECT i, i % 10 FROM (SELECT generate_series(1, 10) i) t;
ANALYZE t1;
ANALYZE t2;
ANALYZE t3;

LOAD 'pg_hint_plan';
SET pg_hint_plan.enable_hint TO on;
SET pg_hint_plan.debug_print TO on;
SET client_min_messages TO LOG;
SET search_path TO public, s1;

----
---- No. M-1 comment pattern
----

-- No. M-1-1
EXPLAIN (COSTS false) SELECT * FROM t1, t2;

-- No. M-1-2
/*+ DisableBroadcast(t2) */
EXPLAIN (COSTS false) SELECT * FROM t1, t2;

-- No. M-1-3
/*+ DisableBroadcast(t1) DisableBroadcast(t2) */
EXPLAIN (COSTS false) SELECT * FROM t1, t2;

-- No. M-2-1
EXPLAIN (COSTS false) SELECT * FROM t1, t2 where t1.id=t2.id;

-- No. M-3-1
EXPLAIN (COSTS false) SELECT * FROM t1, t2 where t1.id=t2.val;

-- No. M-3-2
/*+ DisableRedistribute(t2) */
EXPLAIN (COSTS false) SELECT * FROM t1, t2 where t1.id=t2.val;

-- No. M-4-1
EXPLAIN (COSTS false) SELECT * FROM t3, t2 where t2.val=t3.id;

-- No. M-4-2
/*+  DisableBroadcast(t3) */
EXPLAIN (COSTS false) SELECT * FROM t3, t2 where t2.val=t3.id;

-- No. M-4-3
/*+  DisableBroadcast(t3) DisableRedistribute(t2) */
EXPLAIN (COSTS false) SELECT * FROM t3, t2 where t2.val=t3.id;

-- No. M-4-4
/*+  DisableBroadcast(t2) DisableRedistribute(t2) */
EXPLAIN (COSTS false) SELECT * FROM t3, t2 where t2.val=t3.id;

-- No. M-5-1
EXPLAIN (COSTS false) SELECT * FROM (t1 JOIN t2 ON t1.id=t2.val) JOIN t3 ON t2.val=t3.id;

-- No. M-5-2
/*+ DisableBroadcast(t1)  */
EXPLAIN (COSTS false) SELECT * FROM (t1 JOIN t2 ON t1.id=t2.val) JOIN t3 ON t2.val=t3.id;

-- No. M-6-1
EXPLAIN (COSTS false) SELECT * FROM (t1 JOIN t2 ON t1.val=t2.val) JOIN t3 ON t2.val=t3.id;

-- No. M-6-2
/*+ DisableBroadcast(t2)  */
EXPLAIN (COSTS false) SELECT * FROM (t1 JOIN t2 ON t1.val=t2.val) JOIN t3 ON t2.val=t3.id;

-- No. M-6-3
/*+ DisableBroadcast(t2) DisableRedistribute(t3) */
EXPLAIN (COSTS false) SELECT * FROM (t1 JOIN t2 ON t1.val=t2.val) JOIN t3 ON t2.val=t3.id;

-- No. M-6-4
/*+ DisableBroadcast(t2) DisableBroadcast(t3) */
EXPLAIN (COSTS false) SELECT * FROM (t1 JOIN t2 ON t1.val=t2.val) JOIN t3 ON t2.val=t3.id;

-- No. M-6-5
/*+ DisableBroadcast(t2) DisableBroadcast(t3) DisableBroadcast(t4) */
EXPLAIN (COSTS false) SELECT * FROM (t1 JOIN t2 ON t1.val=t2.val) JOIN t3 ON t2.val=t3.id;