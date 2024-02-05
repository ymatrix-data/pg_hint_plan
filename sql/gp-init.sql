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
