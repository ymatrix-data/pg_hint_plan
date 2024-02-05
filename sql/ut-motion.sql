LOAD 'pg_hint_plan';
SET pg_hint_plan.enable_hint TO on;
SET pg_hint_plan.debug_print TO on;
SET client_min_messages TO LOG;
SET search_path TO public, s1, s2;

----
---- No. M-1 comment pattern
----

-- No. M-1-1
explain select * from t1, t2;

-- No. M-1-2
/*+ DisableBroadcast(t2) */
explain select * from t1, t2;

-- No. M-1-3
explain select * from t1, t2 where t1.id=t2.id;

-- No. M-1-4
explain select * from t1, t2 where t1.id=t2.val;

-- No. M-1-5
/*+ DisableRedistribute(t2) */
explain select * from t1, t2 where t1.id=t2.val;

-- No. M-1-6
explain select * from t3, t2 where t2.val=t3.id;

-- No. M-1-7
/*+  DisableBroadcast(t3) */
explain select * from t3, t2 where t2.val=t3.id;

-- No. M-1-8
/*+  DisableBroadcast(t3) DisableRedistribute(t2) */
explain select * from t3, t2 where t2.val=t3.id;

-- No. M-1-9
/*+  DisableBroadcast(t2) DisableRedistribute(t2) */
explain select * from t3, t2 where t2.val=t3.id;

-- No. M-1-10
explain select * from (t1 join t2 on t1.id=t2.val) join t3 on t2.val=t3.id;

-- No. M-1-11
/* DisableBroadcast(t1)  */
explain select * from (t1 join t2 on t1.id=t2.val) join t3 on t2.val=t3.id;

-- No. M-1-12
explain select * from (t1 join t2 on t1.val=t2.val) join t3 on t2.val=t3.id;

-- No. M-1-13
/*+ DisableBroadcast(t2)  */
explain select * from (t1 join t2 on t1.val=t2.val) join t3 on t2.val=t3.id;

-- No. M-1-14
/*+ DisableBroadcast(t2) DisableRedistribute(t3) */ explain select * from (t1 join t2 on t1.val=t2.val) join t3 on t2.val=t3.id;

-- No. M-1-15
/*+ DisableBroadcast(t2) DisableBroadcast(t3) */ explain select * from (t1 join t2 on t1.val=t2.val) join t3 on t2.val=t3.id;