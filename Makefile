#
# pg_hint_plan: Makefile
#
# Copyright (c) 2012-2020, NIPPON TELEGRAPH AND TELEPHONE CORPORATION
#

MODULES = pg_hint_plan

NUM_PRIMARY_MIRROR_PAIRS ?= 1

ifeq ($(NUM_PRIMARY_MIRROR_PAIRS),1)
  # Execute original unit tests in single-node mode only, as Greenplum's plan merely adds an extra Gather Motion compared to PostgreSQL's plan.
  REGRESS = init base_plan ut-init ut-A ut-fini
else
  REGRESS = ut-motion
endif

#REGRESS = ut-motion

#REGRESS = init base_plan pg_hint_plan #ut-init ut-A ut-S ut-J ut-L ut-G ut-R \
	ut-fdw ut-W ut-T ut-fini

# pg_hint_plan 会卡住  ut-init 可以了

ifeq ($(PORT),)
  # PORT is not defined
else ifeq ($(USER),)
  # USER is not defined
else
  # Both PORT and USER are defined
  REGRESS_OPTS = --port=${PORT} --user=${USER}
endif

EXTENSION = pg_hint_plan
DATA = pg_hint_plan--*.sql

ifdef USE_PGXS
PG_CONFIG = pg_config
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
else
subdir = contrib/pg_hint_plan
top_builddir = ../..
include $(top_builddir)/src/Makefile.global
include $(top_srcdir)/contrib/contrib-global.mk
endif

ifeq (,$(filter $(shell uname),Darwin SunOS))
LDFLAGS+=-Wl,--build-id
endif

# pg_hint_plan.c includes core.c, make_join_rel.c and pg_stat_statements.c motion.c
pg_hint_plan.o: core.c make_join_rel.c pg_stat_statements.c motion.c

OBJS = pg_hint_plan.o

override CPPFLAGS += -I$(top_srcdir)/src/pl/plpgsql/src
