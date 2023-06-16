#
# pg_hint_plan: Makefile
#
# Copyright (c) 2012-2020, NIPPON TELEGRAPH AND TELEPHONE CORPORATION
#

MODULES = pg_hint_plan

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

# pg_hint_plan.c includes core.c, make_join_rel.c and pg_stat_statements.c
pg_hint_plan.o: core.c make_join_rel.c pg_stat_statements.c

OBJS = pg_hint_plan.o

override CPPFLAGS += -I$(top_srcdir)/src/pl/plpgsql/src
