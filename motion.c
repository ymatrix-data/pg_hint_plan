
/*
 * add_paths_to_joinrel
 *	  Given a join relation and two component rels from which it can be made,
 *	  consider all possible paths that use the two component rels as outer
 *	  and inner rel respectively.  Add these paths to the join rel's pathlist
 *	  if they survive comparison with other paths (and remove any existing
 *	  paths that are dominated by these paths).
 *
 * Modifies the pathlist field of the joinrel node to contain the best
 * paths found so far.
 *
 * jointype is not necessarily the same as sjinfo->jointype; it might be
 * "flipped around" if we are considering joining the rels in the opposite
 * direction from what's indicated in sjinfo.
 *
 * Also, this routine and others in this module accept the special JoinTypes
 * JOIN_UNIQUE_OUTER and JOIN_UNIQUE_INNER to indicate that we should
 * unique-ify the outer or inner relation and then apply a regular inner
 * join.  These values are not allowed to propagate outside this module,
 * however.  Path cost estimation code may need to recognize that it's
 * dealing with such a case --- the combination of nominal jointype INNER
 * with sjinfo->jointype == JOIN_SEMI indicates that.
 */
void
add_paths_to_joinrel(PlannerInfo *root,
					 RelOptInfo *joinrel,
					 RelOptInfo *outerrel,
					 RelOptInfo *innerrel,
					 JoinType jointype,
					 SpecialJoinInfo *sjinfo,
					 List *restrictlist)
{
	JoinPathExtraData extra;
	bool		mergejoin_allowed = true;
	ListCell   *lc;
	Relids		joinrelids;

	/*
	 * PlannerInfo doesn't contain the SpecialJoinInfos created for joins
	 * between child relations, even if there is a SpecialJoinInfo node for
	 * the join between the topmost parents. So, while calculating Relids set
	 * representing the restriction, consider relids of topmost parent of
	 * partitions.
	 */
	if (joinrel->reloptkind == RELOPT_OTHER_JOINREL)
		joinrelids = joinrel->top_parent_relids;
	else
		joinrelids = joinrel->relids;

	extra.restrictlist = restrictlist;
	extra.mergeclause_list = NIL;
	extra.sjinfo = sjinfo;
	extra.param_source_rels = NULL;
	extra.redistribution_clauses = NIL;

	Assert(outerrel->pathlist &&
		   outerrel->cheapest_total_path);
	Assert(innerrel->pathlist &&
		   innerrel->cheapest_total_path);

	/*
	 * Don't consider paths that have WorkTableScan as inner rel. If the outer
	 * rel has a WorkTableScan as well, we won't be able to produce a usable
	 * join so we need to error out.  This case can happen when to RECURSIVE
	 * clauses are joined. RECURSIVE_CTE_FIXME: Revisit this when we gain
	 * rescannable motions.
	 */
	if (innerrel->cheapest_startup_path && cdbpath_contains_wts(innerrel->cheapest_startup_path))
	{
		if (outerrel->cheapest_startup_path && cdbpath_contains_wts(outerrel->cheapest_startup_path))
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("joining nested RECURSIVE clauses is not supported")));
		return;
	}
	if (cdbpath_contains_wts(innerrel->cheapest_total_path))
		return;

	/*
	 * See if the inner relation is provably unique for this outer rel.
	 *
	 * We have some special cases: for JOIN_SEMI and JOIN_ANTI, it doesn't
	 * matter since the executor can make the equivalent optimization anyway;
	 * we need not expend planner cycles on proofs.  For JOIN_UNIQUE_INNER, we
	 * must be considering a semijoin whose inner side is not provably unique
	 * (else reduce_unique_semijoins would've simplified it), so there's no
	 * point in calling innerrel_is_unique.  However, if the LHS covers all of
	 * the semijoin's min_lefthand, then it's appropriate to set inner_unique
	 * because the path produced by create_unique_path will be unique relative
	 * to the LHS.  (If we have an LHS that's only part of the min_lefthand,
	 * that is *not* true.)  For JOIN_UNIQUE_OUTER, pass JOIN_INNER to avoid
	 * letting that value escape this module.
	 */
	switch (jointype)
	{
		case JOIN_SEMI:
		case JOIN_ANTI:
			extra.inner_unique = false; /* well, unproven */
			break;
		case JOIN_UNIQUE_INNER:
			extra.inner_unique = bms_is_subset(sjinfo->min_lefthand,
											   outerrel->relids);
			break;
		case JOIN_UNIQUE_OUTER:
			extra.inner_unique = innerrel_is_unique(root,
													joinrel->relids,
													outerrel->relids,
													innerrel,
													JOIN_INNER,
													restrictlist,
													false);
			break;
		default:
			extra.inner_unique = innerrel_is_unique(root,
													joinrel->relids,
													outerrel->relids,
													innerrel,
													jointype,
													restrictlist,
													false);
			break;
	}

	/*
	 * Find potential mergejoin clauses.  We can skip this if we are not
	 * interested in doing a mergejoin.  However, mergejoin may be our only
	 * way of implementing a full outer join, so override enable_mergejoin if
	 * it's a full join.
	 *
	 * CDB: Always build mergeclause_list.  We need it for motion planning.
	 */
	extra.redistribution_clauses = select_cdb_redistribute_clauses(root,
															 joinrel,
															 outerrel,
															 innerrel,
															 restrictlist,
															 jointype);

	/*
	 * If it's SEMI, ANTI, or inner_unique join, compute correction factors
	 * for cost estimation.  These will be the same for all paths.
	 */
	if (jointype == JOIN_SEMI || jointype == JOIN_ANTI || extra.inner_unique)
		compute_semi_anti_join_factors(root, joinrel, outerrel, innerrel,
									   jointype, sjinfo, restrictlist,
									   &extra.semifactors);

	/*
	 * Decide whether it's sensible to generate parameterized paths for this
	 * joinrel, and if so, which relations such paths should require.  There
	 * is usually no need to create a parameterized result path unless there
	 * is a join order restriction that prevents joining one of our input rels
	 * directly to the parameter source rel instead of joining to the other
	 * input rel.  (But see allow_star_schema_join().)	This restriction
	 * reduces the number of parameterized paths we have to deal with at
	 * higher join levels, without compromising the quality of the resulting
	 * plan.  We express the restriction as a Relids set that must overlap the
	 * parameterization of any proposed join path.
	 */
	foreach(lc, root->join_info_list)
	{
		SpecialJoinInfo *sjinfo2 = (SpecialJoinInfo *) lfirst(lc);

		/*
		 * SJ is relevant to this join if we have some part of its RHS
		 * (possibly not all of it), and haven't yet joined to its LHS.  (This
		 * test is pretty simplistic, but should be sufficient considering the
		 * join has already been proven legal.)  If the SJ is relevant, it
		 * presents constraints for joining to anything not in its RHS.
		 */
		if (bms_overlap(joinrelids, sjinfo2->min_righthand) &&
			!bms_overlap(joinrelids, sjinfo2->min_lefthand))
			extra.param_source_rels = bms_join(extra.param_source_rels,
											   bms_difference(root->all_baserels,
															  sjinfo2->min_righthand));

		/* full joins constrain both sides symmetrically */
		if (sjinfo2->jointype == JOIN_FULL &&
			bms_overlap(joinrelids, sjinfo2->min_lefthand) &&
			!bms_overlap(joinrelids, sjinfo2->min_righthand))
			extra.param_source_rels = bms_join(extra.param_source_rels,
											   bms_difference(root->all_baserels,
															  sjinfo2->min_lefthand));
	}

	/*
	 * However, when a LATERAL subquery is involved, there will simply not be
	 * any paths for the joinrel that aren't parameterized by whatever the
	 * subquery is parameterized by, unless its parameterization is resolved
	 * within the joinrel.  So we might as well allow additional dependencies
	 * on whatever residual lateral dependencies the joinrel will have.
	 */
	extra.param_source_rels = bms_add_members(extra.param_source_rels,
											  joinrel->lateral_relids);

	/*
	 * 1. Consider mergejoin paths where both relations must be explicitly
	 * sorted.  Skip this if we can't mergejoin.
	 */
	extra.mergeclause_list = select_mergejoin_clauses(root,
													  joinrel,
													  outerrel,
													  innerrel,
													  restrictlist,
													  jointype,
													  &mergejoin_allowed);
	if (mergejoin_allowed && jointype != JOIN_LASJ_NOTIN)
		sort_inner_and_outer(root, joinrel, outerrel, innerrel,
							 jointype, &extra);

	/*
	 * 2. Consider paths where the outer relation need not be explicitly
	 * sorted. This includes both nestloops and mergejoins where the outer
	 * path is already ordered.  Again, skip this if we can't mergejoin.
	 * (That's okay because we know that nestloop can't handle right/full
	 * joins at all, so it wouldn't work in the prohibited cases either.)
	 */
	if (mergejoin_allowed)
		match_unsorted_outer(root, joinrel, outerrel, innerrel,
							 jointype, &extra);

#ifdef NOT_USED

	/*
	 * 3. Consider paths where the inner relation need not be explicitly
	 * sorted.  This includes mergejoins only (nestloops were already built in
	 * match_unsorted_outer).
	 *
	 * Diked out as redundant 2/13/2000 -- tgl.  There isn't any really
	 * significant difference between the inner and outer side of a mergejoin,
	 * so match_unsorted_inner creates no paths that aren't equivalent to
	 * those made by match_unsorted_outer when add_paths_to_joinrel() is
	 * invoked with the two rels given in the other order.
	 */
	if (mergejoin_allowed)
		match_unsorted_inner(root, joinrel, outerrel, innerrel,
							 jointype, &extra);
#endif

	/*
	 * 4. Consider paths where both outer and inner relations must be hashed
	 * before being joined.  As above, disregard enable_hashjoin for full
	 * joins, because there may be no other alternative.
	 */
	if (enable_hashjoin || jointype == JOIN_FULL)
		hash_inner_and_outer(root, joinrel, outerrel, innerrel,
							 jointype, &extra);

	/*
	 * 5. If inner and outer relations are foreign tables (or joins) belonging
	 * to the same server and assigned to the same user to check access
	 * permissions as, give the FDW a chance to push down joins.
	 */
	if (joinrel->fdwroutine &&
		joinrel->fdwroutine->GetForeignJoinPaths)
		joinrel->fdwroutine->GetForeignJoinPaths(root, joinrel,
												 outerrel, innerrel,
												 jointype, &extra);

	/*
	 * 6. Finally, give extensions a chance to manipulate the path list.
	 */
	if (set_join_pathlist_hook)
		set_join_pathlist_hook(root, joinrel, outerrel, innerrel,
							   jointype, &extra);
}



/*
 * hash_inner_and_outer
 *	  Create hashjoin join paths by explicitly hashing both the outer and
 *	  inner keys of each available hash clause.
 *
 * 'joinrel' is the join relation
 * 'outerrel' is the outer join relation
 * 'innerrel' is the inner join relation
 * 'jointype' is the type of join to do
 * 'extra' contains additional input values
 */
static void
hash_inner_and_outer(PlannerInfo *root,
					 RelOptInfo *joinrel,
					 RelOptInfo *outerrel,
					 RelOptInfo *innerrel,
					 JoinType jointype,
					 JoinPathExtraData *extra)
{
	JoinType	save_jointype = jointype;
	bool		isouterjoin = IS_OUTER_JOIN(jointype);
	List	   *hashclauses;
	ListCell   *l;

#ifdef MATRIXDB_VERSION
	double		saved_rel_rows = 0;
#endif /* MATRIXDB_VERSION */

#ifdef MATRIXDB_VERSION
	if (jointype == JOIN_DEDUP_SEMI || jointype == JOIN_DEDUP_SEMI_REVERSE)
	{
		Assert(extra->sjinfo->jointype == JOIN_SEMI);
		saved_rel_rows = joinrel->rows;
		/* we need to re-estimate the size of joinrel using JOIN_INNER */
		extra->sjinfo->jointype = JOIN_INNER;
		set_joinrel_size_estimates(root,
								   joinrel,
								   outerrel,
								   innerrel,
								   extra->sjinfo,
								   extra->restrictlist);

		/* bring back the JOIN_SEMI */
		extra->sjinfo->jointype = JOIN_SEMI;

		jointype = JOIN_INNER;
	}
#else /* MATRIXDB_VERSION */
	if (jointype == JOIN_DEDUP_SEMI || jointype == JOIN_DEDUP_SEMI_REVERSE)
		jointype = JOIN_INNER;
#endif /* MATRIXDB_VERSION */

	/*
	 * We need to build only one hashclauses list for any given pair of outer
	 * and inner relations; all of the hashable clauses will be used as keys.
	 *
	 * Scan the join's restrictinfo list to find hashjoinable clauses that are
	 * usable with this pair of sub-relations.
	 */
	hashclauses = NIL;
	foreach(l, extra->restrictlist)
	{
		RestrictInfo *restrictinfo = (RestrictInfo *) lfirst(l);

		/*
		 * A qual like "(a = b) IS NOT FALSE" is treated as hashable in
		 * check_hashjoinable(), for the benefit of LASJ joins. It will be
		 * hashed like "a = b", but the special LASJ handlng in the hash join
		 * executor node will ensure that NULLs are treated correctly. For
		 * other kinds of joins, we cannot use "(a = b) IS NOT FALSE" as a
		 * hash qual.
		 */
		if (jointype != JOIN_LASJ_NOTIN && IsA(restrictinfo->clause, BooleanTest))
			continue;

		/*
		 * If processing an outer join, only use its own join clauses for
		 * hashing.  For inner joins we need not be so picky.
		 */
		if (isouterjoin && RINFO_IS_PUSHED_DOWN(restrictinfo, joinrel->relids))
			continue;

		if (!restrictinfo->can_join ||
			restrictinfo->hashjoinoperator == InvalidOid)
			continue;			/* not hashjoinable */

		/*
		 * Check if clause has the form "outer op inner" or "inner op outer".
		 */
		if (!clause_sides_match_join(restrictinfo, outerrel, innerrel))
			continue;			/* no good for these input relations */

		hashclauses = lappend(hashclauses, restrictinfo);
	}

	/* If we found any usable hashclauses, make paths */
	if (hashclauses)
	{
		/*
		 * We consider both the cheapest-total-cost and cheapest-startup-cost
		 * outer paths.  There's no need to consider any but the
		 * cheapest-total-cost inner path, however.
		 */
		Path	   *cheapest_startup_outer = outerrel->cheapest_startup_path;
		Path	   *cheapest_total_outer = outerrel->cheapest_total_path;
		Path	   *cheapest_total_inner = innerrel->cheapest_total_path;

		/*
		 * If either cheapest-total path is parameterized by the other rel, we
		 * can't use a hashjoin.  (There's no use looking for alternative
		 * input paths, since these should already be the least-parameterized
		 * available paths.)
		 */
		if (PATH_PARAM_BY_REL(cheapest_total_outer, innerrel) ||
			PATH_PARAM_BY_REL(cheapest_total_inner, outerrel))
			return;

		/* Unique-ify if need be; we ignore parameterized possibilities */
		if (jointype == JOIN_UNIQUE_OUTER)
		{
			cheapest_total_outer = (Path *)
				create_unique_path(root, outerrel,
								   cheapest_total_outer, extra->sjinfo);
			Assert(cheapest_total_outer);
			jointype = JOIN_INNER;
			try_hashjoin_path(root,
							  joinrel,
							  cheapest_total_outer,
							  cheapest_total_inner,
							  hashclauses,
							  jointype,
							  save_jointype,
							  extra);
			/* no possibility of cheap startup here */
		}
		else if (jointype == JOIN_UNIQUE_INNER)
		{
			cheapest_total_inner = (Path *)
				create_unique_path(root, innerrel,
								   cheapest_total_inner, extra->sjinfo);
			Assert(cheapest_total_inner);
			jointype = JOIN_INNER;
			try_hashjoin_path(root,
							  joinrel,
							  cheapest_total_outer,
							  cheapest_total_inner,
							  hashclauses,
							  jointype,
							  save_jointype,
							  extra);

#ifdef MATRIXDB_VERSION
			if (cheapest_startup_outer != NULL &&
				cheapest_startup_outer != cheapest_total_outer &&
				!PATH_PARAM_BY_REL(cheapest_startup_outer, innerrel))
#else /* MATRIXDB_VERSION */
			if (cheapest_startup_outer != NULL &&
				cheapest_startup_outer != cheapest_total_outer)
#endif /* MATRIXDB_VERSION */
				try_hashjoin_path(root,
								  joinrel,
								  cheapest_startup_outer,
								  cheapest_total_inner,
								  hashclauses,
								  jointype,
								  save_jointype,
								  extra);
		}
		else
		{
			/*
			 * For other jointypes, we consider the cheapest startup outer
			 * together with the cheapest total inner, and then consider
			 * pairings of cheapest-total paths including parameterized ones.
			 * There is no use in generating parameterized paths on the basis
			 * of possibly cheap startup cost, so this is sufficient.
			 */
			ListCell   *lc1;
			ListCell   *lc2;

#ifdef MATRIXDB_VERSION
			if (cheapest_startup_outer != NULL &&
				!PATH_PARAM_BY_REL(cheapest_startup_outer, innerrel))
#else /* MATRIXDB_VERSION */
			if (cheapest_startup_outer != NULL)
#endif /* MATRIXDB_VERSION */
				try_hashjoin_path(root,
								  joinrel,
								  cheapest_startup_outer,
								  cheapest_total_inner,
								  hashclauses,
								  jointype,
								  save_jointype,
								  extra);

			foreach(lc1, outerrel->cheapest_parameterized_paths)
			{
				Path	   *outerpath = (Path *) lfirst(lc1);

				/*
				 * We cannot use an outer path that is parameterized by the
				 * inner rel.
				 */
				if (PATH_PARAM_BY_REL(outerpath, innerrel))
					continue;

				foreach(lc2, innerrel->cheapest_parameterized_paths)
				{
					Path	   *innerpath = (Path *) lfirst(lc2);

					/*
					 * We cannot use an inner path that is parameterized by
					 * the outer rel, either.
					 */
					if (PATH_PARAM_BY_REL(innerpath, outerrel))
						continue;

					if (outerpath == cheapest_startup_outer &&
						innerpath == cheapest_total_inner)
						continue;	/* already tried it */

					try_hashjoin_path(root,
									  joinrel,
									  outerpath,
									  innerpath,
									  hashclauses,
									  jointype,
									  save_jointype,
									  extra);
				}
			}
		}

		/*
		 * If the joinrel is parallel-safe, we may be able to consider a
		 * partial hash join.  However, we can't handle JOIN_UNIQUE_OUTER,
		 * because the outer path will be partial, and therefore we won't be
		 * able to properly guarantee uniqueness.  Similarly, we can't handle
		 * JOIN_FULL and JOIN_RIGHT, because they can produce false null
		 * extended rows.  Also, the resulting path must not be parameterized.
		 * We would be able to support JOIN_FULL and JOIN_RIGHT for Parallel
		 * Hash, since in that case we're back to a single hash table with a
		 * single set of match bits for each batch, but that will require
		 * figuring out a deadlock-free way to wait for the probe to finish.
		 */
		if (joinrel->consider_parallel &&
			save_jointype != JOIN_UNIQUE_OUTER &&
			save_jointype != JOIN_FULL &&
			save_jointype != JOIN_RIGHT &&
			outerrel->partial_pathlist != NIL &&
			bms_is_empty(joinrel->lateral_relids))
		{
			Path	   *cheapest_partial_outer;
			Path	   *cheapest_partial_inner = NULL;
			Path	   *cheapest_safe_inner = NULL;

			cheapest_partial_outer =
				(Path *) linitial(outerrel->partial_pathlist);

			/*
			 * Can we use a partial inner plan too, so that we can build a
			 * shared hash table in parallel?  We can't handle
			 * JOIN_UNIQUE_INNER because we can't guarantee uniqueness.
			 */
			if (innerrel->partial_pathlist != NIL &&
				save_jointype != JOIN_UNIQUE_INNER &&
				enable_parallel_hash)
			{
				cheapest_partial_inner =
					(Path *) linitial(innerrel->partial_pathlist);
				try_partial_hashjoin_path(root, joinrel,
										  cheapest_partial_outer,
										  cheapest_partial_inner,
										  hashclauses,
										  jointype,
										  save_jointype,
										  extra,
										  true /* parallel_hash */ );
			}

#ifdef MATRIXDB_VERSION
			/*
			 * MatrixDB: can also try non-parallel-hashjoin on partial inner
			 * path.
			 */
			if (innerrel->partial_pathlist != NIL &&
				save_jointype != JOIN_UNIQUE_INNER)
			{
				cheapest_partial_inner =
					(Path *) linitial(innerrel->partial_pathlist);

				try_partial_hashjoin_path(root, joinrel,
										  cheapest_partial_outer,
										  cheapest_partial_inner,
										  hashclauses,
										  jointype,
										  save_jointype,
										  extra,
										  false /* non parallel_hash */ );
			}
#endif /* MATRIXDB_VERSION */

			/*
			 * Normally, given that the joinrel is parallel-safe, the cheapest
			 * total inner path will also be parallel-safe, but if not, we'll
			 * have to search for the cheapest safe, unparameterized inner
			 * path.  If doing JOIN_UNIQUE_INNER, we can't use any alternative
			 * inner path.
			 */
			if (cheapest_total_inner->parallel_safe)
				cheapest_safe_inner = cheapest_total_inner;
			else if (save_jointype != JOIN_UNIQUE_INNER)
				cheapest_safe_inner =
					get_cheapest_parallel_safe_total_inner(innerrel->pathlist);

			if (cheapest_safe_inner != NULL)
				try_partial_hashjoin_path(root, joinrel,
										  cheapest_partial_outer,
										  cheapest_safe_inner,
										  hashclauses, jointype,
										  save_jointype,
										  extra,
										  false /* parallel_hash */ );
		}
	}

#ifdef MATRIXDB_VERSION
	if (save_jointype == JOIN_DEDUP_SEMI || save_jointype == JOIN_DEDUP_SEMI_REVERSE)
		joinrel->rows = saved_rel_rows;
#endif /* MATRIXDB_VERSION */
}


/*
 * try_hashjoin_path
 *	  Consider a hash join path; if it appears useful, push it into
 *	  the joinrel's pathlist via add_path().
 */
static void
try_hashjoin_path(PlannerInfo *root,
				  RelOptInfo *joinrel,
				  Path *outer_path,
				  Path *inner_path,
				  List *hashclauses,
				  JoinType jointype,
				  JoinType orig_jointype,
				  JoinPathExtraData *extra)
{
	Relids		required_outer;
	JoinCostWorkspace workspace;

	/*
	 * Check to see if proposed path is still parameterized, and reject if the
	 * parameterization wouldn't be sensible.
	 */
	required_outer = calc_non_nestloop_required_outer(outer_path,
													  inner_path);
	if (required_outer &&
		!bms_overlap(required_outer, extra->param_source_rels))
	{
		/* Waste no memory when we reject a path here */
		bms_free(required_outer);
		return;
	}

	/*
	 * See comments in try_nestloop_path().  Also note that hashjoin paths
	 * never have any output pathkeys, per comments in create_hashjoin_path.
	 */
	initial_cost_hashjoin(root, &workspace, jointype, hashclauses,
						  outer_path, inner_path, extra, false);

	if (add_path_precheck(joinrel,
						  workspace.startup_cost, workspace.total_cost,
						  NIL, required_outer))
	{
		add_path(joinrel, (Path *)
				 create_hashjoin_path(root,
									  joinrel,
									  jointype,
									  orig_jointype,
									  &workspace,
									  extra,
									  outer_path,
									  inner_path,
									  false,	/* parallel_hash */
#ifdef MATRIXDB_VERSION
									  true,
#endif
									  extra->restrictlist,
									  required_outer,
									  extra->redistribution_clauses,
									  hashclauses));
	}
	else
	{
		/* Waste no memory when we reject a path here */
		bms_free(required_outer);
	}
}



/*
 * create_hashjoin_path
 *	  Creates a pathnode corresponding to a hash join between two relations.
 *
 * 'joinrel' is the join relation
 * 'jointype' is the type of join required
 * 'workspace' is the result from initial_cost_hashjoin
 * 'extra' contains various information about the join
 * 'outer_path' is the cheapest outer path
 * 'inner_path' is the cheapest inner path
 * 'parallel_hash' to select Parallel Hash of inner path (shared hash table)
 * 'restrict_clauses' are the RestrictInfo nodes to apply at the join
 * 'required_outer' is the set of required outer rels
 * 'hashclauses' are the RestrictInfo nodes to use as hash clauses
 *		(this should be a subset of the restrict_clauses list)
 */
Path *
create_hashjoin_path(PlannerInfo *root,
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
					 List *hashclauses)
{
	HashPath   *pathnode;
	CdbPathLocus join_locus;
	bool		outer_must_be_local = !bms_is_empty(PATH_REQ_OUTER(outer_path));
	bool		inner_must_be_local = !bms_is_empty(PATH_REQ_OUTER(inner_path));
	int			rowidexpr_id;

	/* Add motion nodes above subpaths and decide where to join. */
	join_locus = cdbpath_motion_for_join(root,
										 orig_jointype,
										 &outer_path,       /* INOUT */
										 &inner_path,       /* INOUT */
										 &rowidexpr_id,
										 redistribution_clauses,
										 restrict_clauses,
										 NIL,   /* don't care about ordering */
										 NIL,
										 outer_must_be_local,
#ifdef MATRIXDB_VERSION
										 inner_must_be_local,
										 consider_replicate,
										 parallel_hash);
#else /* MATRIXDB_VERSION */
										 inner_must_be_local);
#endif /* MATRIXDB_VERSION */

	if (CdbPathLocus_IsNull(join_locus))
		return NULL;

#ifdef MATRIXDB_VERSION
	/*
	 * Do not generate parallel hash join if child paths contain motion,
	 * because the barrier mechanism used by parallel hash join to sync
	 * workers does not work as expected if their inputs are from a motion
	 * node, specific execution order of the workers can lead to wrong
	 * query results.
	 */
	if (parallel_hash &&
		(outer_path->motionHazard || inner_path->motionHazard))
		return NULL;
#endif /* MATRIXDB_VERSION */

	/*
	 * CDB: If gp_enable_hashjoin_size_heuristic is set, disallow inner
	 * joins where the inner rel is the larger of the two inputs.
	 *
	 * Note cdbpath_motion_for_join() has to precede this so we can get
	 * the right row count, in case Broadcast Motion is inserted above an
	 * input path.
	 */
	if (jointype == JOIN_INNER && gp_enable_hashjoin_size_heuristic)
	{
		double		outersize;
		double		innersize;

		outersize = ExecHashRowSize(outer_path->parent->reltarget->width) *
			outer_path->rows;
		innersize = ExecHashRowSize(inner_path->parent->reltarget->width) *
			inner_path->rows;

		if (innersize > outersize)
			return NULL;
	}

	pathnode = makeNode(HashPath);

	pathnode->jpath.path.pathtype = T_HashJoin;
	pathnode->jpath.path.parent = joinrel;
	pathnode->jpath.path.pathtarget = joinrel->reltarget;
	pathnode->jpath.path.param_info =
		get_joinrel_parampathinfo(root,
								  joinrel,
								  outer_path,
								  inner_path,
								  extra->sjinfo,
								  required_outer,
								  &restrict_clauses);
	pathnode->jpath.path.parallel_aware =
		joinrel->consider_parallel && parallel_hash;
	pathnode->jpath.path.parallel_safe = joinrel->consider_parallel &&
		outer_path->parallel_safe && inner_path->parallel_safe;
	/* This is a foolish way to estimate parallel_workers, but for now... */
#ifdef MATRIXDB_VERSION
	/*
	 * In Matrixdb, let's keep it the same with the join_locus after
	 * the motions are decorated
	 */
	pathnode->jpath.path.parallel_workers = join_locus.parallel_workers;
#else
	pathnode->jpath.path.parallel_workers = outer_path->parallel_workers;
#endif /* MATRIXDB_VERSION */

	/*
	 * A hashjoin never has pathkeys, since its output ordering is
	 * unpredictable due to possible batching.  XXX If the inner relation is
	 * small enough, we could instruct the executor that it must not batch,
	 * and then we could assume that the output inherits the outer relation's
	 * ordering, which might save a sort step.  However there is considerable
	 * downside if our estimate of the inner relation size is badly off. For
	 * the moment we don't risk it.  (Note also that if we wanted to take this
	 * seriously, joinpath.c would have to consider many more paths for the
	 * outer rel than it does now.)
	 */
	pathnode->jpath.path.pathkeys = NIL;
	pathnode->jpath.path.locus = join_locus;

	pathnode->jpath.jointype = jointype;
	pathnode->jpath.inner_unique = extra->inner_unique;
	pathnode->jpath.outerjoinpath = outer_path;
	pathnode->jpath.innerjoinpath = inner_path;
	pathnode->jpath.joinrestrictinfo = restrict_clauses;
	pathnode->path_hashclauses = hashclauses;
	/* final_cost_hashjoin will fill in pathnode->num_batches */

	/*
	 * If hash table overflows to disk, and an ancestor node requests rescan
	 * (e.g. because the HJ is in the inner subtree of a NJ), then the HJ has
	 * to be redone, including rescanning the inner rel in order to rebuild
	 * the hash table.
	 */
	pathnode->jpath.path.rescannable = outer_path->rescannable && inner_path->rescannable;

	/* see the comment above; we may have a motion hazard on our inner ?! */
	if (pathnode->jpath.path.rescannable)
		pathnode->jpath.path.motionHazard = outer_path->motionHazard;
	else
		pathnode->jpath.path.motionHazard = outer_path->motionHazard || inner_path->motionHazard;
	pathnode->jpath.path.sameslice_relids = bms_union(inner_path->sameslice_relids, outer_path->sameslice_relids);

	/*
	 * inner_path & outer_path are possibly modified above. Let's recalculate
	 * the initial cost.
	 */
	initial_cost_hashjoin(root, workspace, jointype, hashclauses,
						  outer_path, inner_path,
						  extra, parallel_hash);

	final_cost_hashjoin(root, pathnode, workspace, extra);

	if (orig_jointype == JOIN_DEDUP_SEMI ||
		orig_jointype == JOIN_DEDUP_SEMI_REVERSE)
	{
		return (Path *) create_unique_rowid_path(root,
												 joinrel,
												 (Path *) pathnode,
												 pathnode->jpath.innerjoinpath->parent->relids,
												 rowidexpr_id);
	}

	/*
	 * See the comments at the end of create_nestloop_path.
	 */
	return turn_volatile_seggen_to_singleqe(root,
											(Path *) pathnode,
											(Node *) (pathnode->jpath.joinrestrictinfo));
}


/*
 * try_redistribute
 *     helper function for A join B when
 *     - A's locus is general or segmentgeneral
 *     - B's locus is partitioned
 *     it tries to redistribute A to B's locus
 *     or redistribute both A and B to the same
 *     partitioned locus.
 *
 *     return values:
 *     - true: redistributed motion has been added for A
 *     - false: cannot add redistributed motion, caller should
 *       continue to find other solutions.
 */
static bool
try_redistribute(PlannerInfo *root, CdbpathMfjRel *g, CdbpathMfjRel *o,
				 List *redistribution_clauses)
{
	bool g_immovable;
	bool o_immovable;

	Assert(CdbPathLocus_IsGeneral(g->locus) ||
		   CdbPathLocus_IsSegmentGeneral(g->locus));
	Assert(CdbPathLocus_IsPartitioned(o->locus));

	/*
	 * we cannot add motion if requiring order.
	 * has_wts can be true only for general locus
	 * otherwise, it is false and not impact the
	 * value of <x>_immovable.
	 */
	g_immovable = (g->require_existing_order &&
				   !g->pathkeys) || g->has_wts;

	/*
	 * if g cannot be added motion on,
	 * we should return immediately.
	 */
	if (g_immovable)
		return false;

	if (!enable_redistribute_on_rel(root, g->path->parent))
		return false;
	
	o_immovable = (o->require_existing_order &&
				   !o->pathkeys) || o->has_wts;

	if (CdbPathLocus_IsHashed(o->locus) ||
		CdbPathLocus_IsHashedOJ(o->locus))
	{
		/*
		 * first try to only redistribute g as o's locus
		 * if fails then try to redistribute both g and o
		 */
		if (cdbpath_match_preds_to_distkey(root,
										   redistribution_clauses,
										   o->path,
										   o->locus,
										   &g->move_to))
			return true;
		else
		{
			if (!enable_redistribute_on_rel(root, o->path->parent))
				return false;

			/*
			 * both g and o can be added motion on,
			 * we should try each possible case.
			 */
			int			numsegments;

#ifdef MATRIXDB_VERSION
			int16      *contentids;
			int			parallel_workers;

			numsegments = CdbPathLocus_NumSegments(o->locus);
			contentids = o->locus.contentids;

			parallel_workers = Max(o->path->parallel_workers, g->path->parallel_workers);
#else /* MATRIXDB_VERSION */
			if (CdbPathLocus_IsGeneral(g->locus))
				numsegments = CdbPathLocus_NumSegments(o->locus);
			else
				numsegments = CdbPathLocus_CommonSegments(o->locus, g->locus);
#endif /* MATRIXDB_VERSION */

			if(cdbpath_distkeys_from_preds(root,
										   redistribution_clauses,
										   o->path,
										   numsegments,
#ifdef MATRIXDB_VERSION
										   contentids,
										   parallel_workers,
#endif /* MATRIXDB_VERSION */
										   &o->move_to,
										   &g->move_to))
			{
				return true;
			}
		}
	}
	else
	{
		/*
		 * the only possible solution is to
		 * redistributed both g and o, so
		 * both g and o should be movable.
		 */

		if (!enable_redistribute_on_rel(root, o->path->parent))
				return false;

		int			numsegments;

#ifdef MATRIXDB_VERSION
		int16      *contentids;
		int			parallel_workers;

		numsegments = CdbPathLocus_NumSegments(o->locus);
		contentids = o->locus.contentids;

		parallel_workers = Max(o->path->parallel_workers, g->path->parallel_workers);
#else /* MATRIXDB_VERSION */
		if (CdbPathLocus_IsGeneral(g->locus))
			numsegments = CdbPathLocus_NumSegments(o->locus);
		else
			numsegments = CdbPathLocus_CommonSegments(o->locus, g->locus);
#endif /* MATRIXDB_VERSION */

		if (!o_immovable &&
			cdbpath_distkeys_from_preds(root,
										redistribution_clauses,
										o->path,
										numsegments,
#ifdef MATRIXDB_VERSION
										contentids,
										parallel_workers,
#endif /* MATRIXDB_VERSION */
										&o->move_to,
										&g->move_to))
		{
			return true;
		}
	}

	/*
	 * fail to redistribute, return false
	 * to let caller know.
	 */
	return false;
}



/*
 * Add a RowIdExpr to the target list of 'path'. Returns the ID
 * of the generated rowid expression in *rowidexpr_id.
 */
static Path *
add_rowid_to_path(PlannerInfo *root, Path *path, int *rowidexpr_id)
{
	RowIdExpr *rowidexpr;
	PathTarget *newpathtarget;

	/*
	 * 'last_rowidexpr_id' is used to generate a unique ID for the RowIdExpr
	 * node that we generate. It only needs to be unique within this query
	 * plan, and the simplest way to achieve that is to just have a global
	 * counter. (Actually, it isn't really needed at the moment because the
	 * deduplication is always done immediately on top of the join, so two
	 * different RowIdExprs should never appear in the same part of the plan
	 * tree. But it might come handy when debugging, if nothing else.
	 * XXX: If we start to rely on it for something important, consider
	 * overflow behavior more carefully.)
	 */
	static uint32 last_rowidexpr_id = 0;

	rowidexpr = makeNode(RowIdExpr);
	last_rowidexpr_id++;

	*rowidexpr_id = rowidexpr->rowidexpr_id = (int) last_rowidexpr_id;

#ifdef MATRIXDB_VERSION
	/*
	 * RowIdExpr should include parallel worker id with multiple workers.
	 */
	rowidexpr->parallel_workers = path->parallel_workers;
#endif /* MATRIXDB_VERSION */

	newpathtarget = copy_pathtarget(path->pathtarget);
	add_column_to_pathtarget(newpathtarget, (Expr *) rowidexpr, 0);

	return (Path *) create_projection_path_with_quals(root, path->parent,
													  path, newpathtarget,
													  NIL, true);
}


static bool
cdbpath_match_preds_to_distkey_tail(CdbpathMatchPredsContext *ctx,
									ListCell *distkeycell)
{
	DistributionKey *distkey = (DistributionKey *) lfirst(distkeycell);
	DistributionKey *codistkey;
	ListCell   *cell;
	ListCell   *rcell;

	Assert(CdbPathLocus_IsHashed(ctx->locus) ||
		   CdbPathLocus_IsHashedOJ(ctx->locus));

#ifdef MATRIXDB_VERSION
	/* do hash locus precheck first */
	if (!cdbpathlocus_is_hash_distkey_valid(ctx->locus))
		return false;
#endif /* MATRIXDB_VERSION */

	/*----------------
	 * Is there a "<distkey item> = <constant expr>" predicate?
	 *
	 * If table T is distributed on cols (C,D,E) and query contains preds
	 *		T.C = U.A AND T.D = <constant expr> AND T.E = U.B
	 * then we would like to report a match and return the colocus
	 * 		(U.A, <constant expr>, U.B)
	 * so the caller can join T and U by redistributing only U.
	 * (Note that "T.D = <constant expr>" won't be in the mergeclause_list
	 * because it isn't a join pred.)
	 *----------------
	 */
	codistkey = NULL;

	foreach(cell, distkey->dk_eclasses)
	{
		EquivalenceClass *ec = (EquivalenceClass *) lfirst(cell);

#ifdef MATRIXDB_VERSION
		if (CdbEquivClassIsConstant(ec) &&
			cdbpath_eclass_constant_is_hashable(ec, distkey->dk_opfamily) &&
			!ECAllMemberContainParam(ec, ctx))
#else
		if (CdbEquivClassIsConstant(ec) &&
			cdbpath_eclass_constant_is_hashable(ec, distkey->dk_opfamily))
#endif
		{
			codistkey = distkey;
			break;
		}
	}

	/* Look for an equijoin comparison to the distkey item. */
	if (!codistkey)
	{
		foreach(rcell, ctx->mergeclause_list)
		{
			EquivalenceClass *a_ec; /* Corresponding to ctx->path. */
			EquivalenceClass *b_ec;
			ListCell   *i;
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(rcell);

			update_mergeclause_eclasses(ctx->root, rinfo);

			if (bms_is_subset(rinfo->right_relids, ctx->path->parent->relids))
			{
				a_ec = rinfo->right_ec;
				b_ec = rinfo->left_ec;
			}
			else
			{
				a_ec = rinfo->left_ec;
				b_ec = rinfo->right_ec;
				Assert(bms_is_subset(rinfo->left_relids, ctx->path->parent->relids));
			}

			foreach(i, distkey->dk_eclasses)
			{
				EquivalenceClass *dk_eclass = (EquivalenceClass *) lfirst(i);

				if (dk_eclass == a_ec)
					codistkey = makeDistributionKeyForEC(b_ec, distkey->dk_opfamily); /* break earlier? */
			}

			if (codistkey)
				break;
		}
	}

	/* Fail if didn't find a match for this distkey item. */
	if (!codistkey)
		return false;

	/* Might need to build co-locus if locus is outer join source or result. */
	if (codistkey != lfirst(distkeycell))
		ctx->colocus_eq_locus = false;

	/* Match remaining partkey items. */
	distkeycell = lnext(distkeycell);
	if (distkeycell)
	{
		if (!cdbpath_match_preds_to_distkey_tail(ctx, distkeycell))
			return false;
	}

	/* Success!  Matched all items.  Return co-locus if requested. */
	if (ctx->colocus)
	{
		if (ctx->colocus_eq_locus)
			*ctx->colocus = ctx->locus;
		else if (!distkeycell)
#ifdef MATRIXDB_VERSION
			CdbPathLocus_MakeHashed(ctx->colocus, list_make1(codistkey),
									CdbPathLocus_NumSegments(ctx->locus),
									ctx->locus.contentids,
									ctx->locus.parallel_workers,
									ctx->locus.parallel_workers ?
									HASHED_ON_WORKERS : HASHED_ON_SEGMENT);
#else /* MATRIXDB_VERSION */
			CdbPathLocus_MakeHashed(ctx->colocus, list_make1(codistkey),
									CdbPathLocus_NumSegments(ctx->locus));
#endif /* MATRIXDB_VERSION */
		else
		{
			ctx->colocus->distkey = lcons(codistkey, ctx->colocus->distkey);
			Assert(cdbpathlocus_is_valid(*ctx->colocus));
		}
	}
	return true;
}								/* cdbpath_match_preds_to_partkey_tail */



/*
 * cdbpath_match_preds_to_partkey
 *
 * Returns true if an equijoin predicate is found in the mergeclause_list
 * for each item of the locus's partitioning key.
 *
 * (Also, a partkey item that is equal to a constant is treated as a match.)
 *
 * Readers may refer also to these related functions:
 *          select_mergejoin_clauses() in joinpath.c
 *          find_mergeclauses_for_pathkeys() in pathkeys.c
 */
static bool
cdbpath_match_preds_to_distkey(PlannerInfo *root,
							   List *mergeclause_list,
							   Path *path,
							   CdbPathLocus locus,
							   CdbPathLocus *colocus)	/* OUT */
{
	CdbpathMatchPredsContext ctx;

	if (!CdbPathLocus_IsHashed(locus) &&
		!CdbPathLocus_IsHashedOJ(locus))
		return false;

	Assert(cdbpathlocus_is_valid(locus));

	ctx.root = root;
	ctx.mergeclause_list = mergeclause_list;
	ctx.path = path;
	ctx.locus = locus;
	ctx.colocus = colocus;
	ctx.colocus_eq_locus = true;

	return cdbpath_match_preds_to_distkey_tail(&ctx, list_head(locus.distkey));
}


/*
 * cdbpath_distkeys_from_preds
 *
 * Makes a CdbPathLocus for repartitioning, driven by
 * the equijoin predicates in the mergeclause_list (a List of RestrictInfo).
 * Returns true if successful, or false if no usable equijoin predicates.
 *
 * Readers may refer also to these related functions:
 *      select_mergejoin_clauses() in joinpath.c
 *      make_pathkeys_for_mergeclauses() in pathkeys.c
 */
static bool
cdbpath_distkeys_from_preds(PlannerInfo *root,
							List *mergeclause_list,
							Path *a_path,
							int numsegments,
#ifdef MATRIXDB_VERSION
							int16 *contentids,
							int parallel_workers,
							CdbPathLocus *a_locus,  /* OUT */
							CdbPathLocus *b_locus)  /* OUT */
#else /* MATRIXDB_VERSION */
							CdbPathLocus *a_locus,	/* OUT */
							CdbPathLocus *b_locus)	/* OUT */
#endif /* MATRIXDB_VERSION */
{
	List	   *a_distkeys = NIL;
	List	   *b_distkeys = NIL;
	ListCell   *rcell;

	foreach(rcell, mergeclause_list)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(rcell);
		Oid			lhs_opno;
		Oid			rhs_opno;
		Oid			opfamily;

		update_mergeclause_eclasses(root, rinfo);

		/*
		 * skip non-hashable keys
		 */
		if (!rinfo->hashjoinoperator)
			continue;

		/*
		 * look up a hash operator family that is compatible for the left and right datatypes
		 * of the hashjoin = operator
		 */
		if (!get_compatible_hash_operators_and_family(rinfo->hashjoinoperator,
													  &lhs_opno, &rhs_opno, &opfamily))
			continue;

		/* Left & right pathkeys are usually the same... */
		if (!b_distkeys && rinfo->left_ec == rinfo->right_ec)
		{
			ListCell   *i;
			bool        found = false;

			foreach(i, a_distkeys)
			{
				DistributionKey *distkey = (DistributionKey *) lfirst(i);
				EquivalenceClass *dk_eclass;

				/*
				 * we only create Hashed DistributionKeys with a single eclass
				 * in this function.
				 */
				Assert(list_length(distkey->dk_eclasses) == 1);
				dk_eclass = (EquivalenceClass *) linitial(distkey->dk_eclasses);

				if (dk_eclass == rinfo->left_ec)
				{
					found = true;
					break;
				}
			}
			if (!found)
			{
				DistributionKey *a_dk = makeDistributionKeyForEC(rinfo->left_ec, opfamily);
				a_distkeys = lappend(a_distkeys, a_dk);
			}
		}

		/* ... except in outer join ON-clause. */
		else
		{
			EquivalenceClass *a_ec;
			EquivalenceClass *b_ec;
			ListCell   *i;
			bool		found = false;

			if (bms_is_subset(rinfo->right_relids, a_path->parent->relids))
			{
				a_ec = rinfo->right_ec;
				b_ec = rinfo->left_ec;
			}
			else
			{
				a_ec = rinfo->left_ec;
				b_ec = rinfo->right_ec;
				Assert(bms_is_subset(rinfo->left_relids, a_path->parent->relids));
			}

			if (!b_ec)
				b_ec = a_ec;

			/*
			 * Convoluted logic to ensure that (a_ec not in a_distkeys) AND
			 * (b_ec not in b_distkeys)
			 */
			found = false;
			foreach(i, a_distkeys)
			{
				DistributionKey *distkey = (DistributionKey *) lfirst(i);
				EquivalenceClass *dk_eclass;

				/*
				 * we only create Hashed DistributionKeys with a single eclass
				 * in this function.
				 */
				Assert(list_length(distkey->dk_eclasses) == 1);
				dk_eclass = (EquivalenceClass *) linitial(distkey->dk_eclasses);

				if (dk_eclass == a_ec)
				{
					found = true;
					break;
				}
			}
			if (!found)
			{
				foreach(i, b_distkeys)
				{
					DistributionKey *distkey = (DistributionKey *) lfirst(i);
					EquivalenceClass *dk_eclass;

					/*
					 * we only create Hashed DistributionKeys with a single eclass
					 * in this function.
					 */
					Assert(list_length(distkey->dk_eclasses) == 1);
					dk_eclass = (EquivalenceClass *) linitial(distkey->dk_eclasses);

					if (dk_eclass == b_ec)
					{
						found = true;
						break;
					}
				}
			}

			if (!found)
			{
				DistributionKey *a_dk = makeDistributionKeyForEC(a_ec, opfamily);
				DistributionKey *b_dk = makeDistributionKeyForEC(b_ec, opfamily);

				a_distkeys = lappend(a_distkeys, a_dk);
				b_distkeys = lappend(b_distkeys, b_dk);
			}
		}

		if (list_length(a_distkeys) >= 20)
			break;
	}

	if (!a_distkeys)
		return false;

#ifdef MATRIXDB_VERSION
	CdbPathLocus_MakeHashed(a_locus, a_distkeys,
							numsegments,
							contentids,
							parallel_workers,
							parallel_workers ?
							HASHED_ON_WORKERS : HASHED_ON_SEGMENT);
#else /* MATRIXDB_VERSION */
	CdbPathLocus_MakeHashed(a_locus, a_distkeys, numsegments);
#endif /* MATRIXDB_VERSION */

	if (b_distkeys)
#ifdef MATRIXDB_VERSION
		CdbPathLocus_MakeHashed(b_locus, b_distkeys,
								numsegments,
								contentids,
								parallel_workers,
								parallel_workers ?
								HASHED_ON_WORKERS : HASHED_ON_SEGMENT);
#else /* MATRIXDB_VERSION */
		CdbPathLocus_MakeHashed(b_locus, b_distkeys, numsegments);
#endif /* MATRIXDB_VERSION */
	else
		*b_locus = *a_locus;
	return true;
}								/* cdbpath_distkeys_from_preds */


/*
 * select_cdb_redistribute_clauses
 *	  Select redistribute clauses that are usable for a particular join.
 *	  Returns a list of RestrictInfo nodes for those clauses.
 *
 * The result of this function is a subset of mergejoin_clauses. Also
 * verify that the operator can be cdbhash.
 */
static List *
select_cdb_redistribute_clauses(PlannerInfo *root,
								RelOptInfo *joinrel,
								RelOptInfo *outerrel,
								RelOptInfo *innerrel,
								List *restrictlist,
								JoinType jointype)
{
	List	   *result_list = NIL;
	bool		isouterjoin = IS_OUTER_JOIN(jointype);
	bool		have_nonmergeable_joinclause = false;
	ListCell   *l;

	foreach(l, restrictlist)
	{
		RestrictInfo *restrictinfo = (RestrictInfo *) lfirst(l);

		/*
		 * If processing an outer join, only use its own join clauses in the
		 * merge.  For inner joins we can use pushed-down clauses too. (Note:
		 * we don't set have_nonmergeable_joinclause here because pushed-down
		 * clauses will become otherquals not joinquals.)
		 */
		if (isouterjoin && restrictinfo->is_pushed_down)
			continue;

		if (!has_redistributable_clause(restrictinfo))
			continue;

		/* Check that clause is a mergeable operator clause */
		if (!restrictinfo->can_join ||
			restrictinfo->mergeopfamilies == NIL)
		{
			/*
			 * The executor can handle extra joinquals that are constants, but
			 * not anything else, when doing right/full merge join.  (The
			 * reason to support constants is so we can do FULL JOIN ON
			 * FALSE.)
			 */
			if (!restrictinfo->clause || !IsA(restrictinfo->clause, Const))
				have_nonmergeable_joinclause = true;
			continue;			/* not mergejoinable */
		}

		/*
		 * Check if clause has the form "outer op inner" or "inner op outer".
		 */
		if (!clause_sides_match_join(restrictinfo, outerrel, innerrel))
		{
			have_nonmergeable_joinclause = true;
			continue;			/* no good for these input relations */
		}

		/*
		 * Insist that each side have a non-redundant eclass.  This
		 * restriction is needed because various bits of the planner expect
		 * that each clause in a merge be associatable with some pathkey in a
		 * canonical pathkey list, but redundant eclasses can't appear in
		 * canonical sort orderings.  (XXX it might be worth relaxing this,
		 * but not enough time to address it for 8.3.)
		 *
		 * Note: it would be bad if this condition failed for an otherwise
		 * mergejoinable FULL JOIN clause, since that would result in
		 * undesirable planner failure.  I believe that is not possible
		 * however; a variable involved in a full join could only appear in
		 * below_outer_join eclasses, which aren't considered redundant.
		 *
		 * This case *can* happen for left/right join clauses: the outer-side
		 * variable could be equated to a constant.  Because we will propagate
		 * that constant across the join clause, the loss of ability to do a
		 * mergejoin is not really all that big a deal, and so it's not clear
		 * that improving this is important.
		 */
		update_mergeclause_eclasses(root, restrictinfo);

		if (EC_MUST_BE_REDUNDANT(restrictinfo->left_ec) ||
			EC_MUST_BE_REDUNDANT(restrictinfo->right_ec))
		{
			have_nonmergeable_joinclause = true;
			continue;			/* can't handle redundant eclasses */
		}

		result_list = lappend(result_list, restrictinfo);
	}

	return result_list;
}



/*
 * select_mergejoin_clauses
 *	  Select mergejoin clauses that are usable for a particular join.
 *	  Returns a list of RestrictInfo nodes for those clauses.
 *
 * *mergejoin_allowed is normally set to true, but it is set to false if
 * this is a right/full join and there are nonmergejoinable join clauses.
 * The executor's mergejoin machinery cannot handle such cases, so we have
 * to avoid generating a mergejoin plan.  (Note that this flag does NOT
 * consider whether there are actually any mergejoinable clauses.  This is
 * correct because in some cases we need to build a clauseless mergejoin.
 * Simply returning NIL is therefore not enough to distinguish safe from
 * unsafe cases.)
 *
 * We also mark each selected RestrictInfo to show which side is currently
 * being considered as outer.  These are transient markings that are only
 * good for the duration of the current add_paths_to_joinrel() call!
 *
 * We examine each restrictinfo clause known for the join to see
 * if it is mergejoinable and involves vars from the two sub-relations
 * currently of interest.
 */
static List *
select_mergejoin_clauses(PlannerInfo *root,
						 RelOptInfo *joinrel,
						 RelOptInfo *outerrel,
						 RelOptInfo *innerrel,
						 List *restrictlist,
						 JoinType jointype,
						 bool *mergejoin_allowed)
{
	List	   *result_list = NIL;
	bool		isouterjoin = IS_OUTER_JOIN(jointype);
	bool		have_nonmergeable_joinclause = false;
	ListCell   *l;

	foreach(l, restrictlist)
	{
		RestrictInfo *restrictinfo = (RestrictInfo *) lfirst(l);

		/*
		 * If processing an outer join, only use its own join clauses in the
		 * merge.  For inner joins we can use pushed-down clauses too. (Note:
		 * we don't set have_nonmergeable_joinclause here because pushed-down
		 * clauses will become otherquals not joinquals.)
		 */
		if (isouterjoin && RINFO_IS_PUSHED_DOWN(restrictinfo, joinrel->relids))
			continue;

		/* Check that clause is a mergeable operator clause */
		if (!restrictinfo->can_join ||
			restrictinfo->mergeopfamilies == NIL)
		{
			/*
			 * The executor can handle extra joinquals that are constants, but
			 * not anything else, when doing right/full merge join.  (The
			 * reason to support constants is so we can do FULL JOIN ON
			 * FALSE.)
			 */
			if (!restrictinfo->clause || !IsA(restrictinfo->clause, Const))
				have_nonmergeable_joinclause = true;
			continue;			/* not mergejoinable */
		}

		if (!OidIsValid(get_commutator(((OpExpr *)(restrictinfo->clause))->opno)))
			continue;

		/*
		 * Check if clause has the form "outer op inner" or "inner op outer".
		 */
		if (!clause_sides_match_join(restrictinfo, outerrel, innerrel))
		{
			have_nonmergeable_joinclause = true;
			continue;			/* no good for these input relations */
		}

		/*
		 * Insist that each side have a non-redundant eclass.  This
		 * restriction is needed because various bits of the planner expect
		 * that each clause in a merge be associable with some pathkey in a
		 * canonical pathkey list, but redundant eclasses can't appear in
		 * canonical sort orderings.  (XXX it might be worth relaxing this,
		 * but not enough time to address it for 8.3.)
		 *
		 * Note: it would be bad if this condition failed for an otherwise
		 * mergejoinable FULL JOIN clause, since that would result in
		 * undesirable planner failure.  I believe that is not possible
		 * however; a variable involved in a full join could only appear in
		 * below_outer_join eclasses, which aren't considered redundant.
		 *
		 * This case *can* happen for left/right join clauses: the outer-side
		 * variable could be equated to a constant.  Because we will propagate
		 * that constant across the join clause, the loss of ability to do a
		 * mergejoin is not really all that big a deal, and so it's not clear
		 * that improving this is important.
		 */
		update_mergeclause_eclasses(root, restrictinfo);

		if (EC_MUST_BE_REDUNDANT(restrictinfo->left_ec) ||
			EC_MUST_BE_REDUNDANT(restrictinfo->right_ec))
		{
			have_nonmergeable_joinclause = true;
			continue;			/* can't handle redundant eclasses */
		}

		result_list = lappend(result_list, restrictinfo);
	}

	/*
	 * Report whether mergejoin is allowed (see comment at top of function).
	 */
	switch (jointype)
	{
		case JOIN_RIGHT:
		case JOIN_FULL:
			*mergejoin_allowed = !have_nonmergeable_joinclause;
			break;
		default:
			*mergejoin_allowed = true;
			break;
	}

	return result_list;
}



/*
 * sort_inner_and_outer
 *	  Create mergejoin join paths by explicitly sorting both the outer and
 *	  inner join relations on each available merge ordering.
 *
 * 'joinrel' is the join relation
 * 'outerrel' is the outer join relation
 * 'innerrel' is the inner join relation
 * 'jointype' is the type of join to do
 * 'extra' contains additional input values
 */
static void
sort_inner_and_outer(PlannerInfo *root,
					 RelOptInfo *joinrel,
					 RelOptInfo *outerrel,
					 RelOptInfo *innerrel,
					 JoinType jointype,
					 JoinPathExtraData *extra)
{
	JoinType	save_jointype = jointype;
	Path	   *outer_path;
	Path	   *inner_path;
	Path	   *cheapest_partial_outer = NULL;
	Path	   *cheapest_safe_inner = NULL;
	List	   *all_pathkeys;
	ListCell   *l;

#ifdef MATRIXDB_VERSION
	double		saved_rel_rows = 0;
#endif /* MATRIXDB_VERSION */

#ifdef MATRIXDB_VERSION
	if (jointype == JOIN_DEDUP_SEMI || jointype == JOIN_DEDUP_SEMI_REVERSE)
	{
		Assert(extra->sjinfo->jointype == JOIN_SEMI);
		saved_rel_rows = joinrel->rows;
		/* we need to re-estimate the size of joinrel using JOIN_INNER */
		extra->sjinfo->jointype = JOIN_INNER;
		set_joinrel_size_estimates(root,
								   joinrel,
								   outerrel,
								   innerrel,
								   extra->sjinfo,
								   extra->restrictlist);

		/* bring back the JOIN_SEMI */
		extra->sjinfo->jointype = JOIN_SEMI;

		jointype = JOIN_INNER;
	}
#else /* MATRIXDB_VERSION */
	if (jointype == JOIN_DEDUP_SEMI || jointype == JOIN_DEDUP_SEMI_REVERSE)
		jointype = JOIN_INNER;
#endif /* MATRIXDB_VERSION */

	/*
	 * We only consider the cheapest-total-cost input paths, since we are
	 * assuming here that a sort is required.  We will consider
	 * cheapest-startup-cost input paths later, and only if they don't need a
	 * sort.
	 *
	 * This function intentionally does not consider parameterized input
	 * paths, except when the cheapest-total is parameterized.  If we did so,
	 * we'd have a combinatorial explosion of mergejoin paths of dubious
	 * value.  This interacts with decisions elsewhere that also discriminate
	 * against mergejoins with parameterized inputs; see comments in
	 * src/backend/optimizer/README.
	 */
	outer_path = outerrel->cheapest_total_path;
	inner_path = innerrel->cheapest_total_path;

	/*
	 * If either cheapest-total path is parameterized by the other rel, we
	 * can't use a mergejoin.  (There's no use looking for alternative input
	 * paths, since these should already be the least-parameterized available
	 * paths.)
	 */
	if (PATH_PARAM_BY_REL(outer_path, innerrel) ||
		PATH_PARAM_BY_REL(inner_path, outerrel))
		return;

	/*
	 * If unique-ification is requested, do it and then handle as a plain
	 * inner join.
	 */
	if (jointype == JOIN_UNIQUE_OUTER)
	{
		outer_path = (Path *) create_unique_path(root, outerrel,
												 outer_path, extra->sjinfo);
		Assert(outer_path);
		jointype = JOIN_INNER;
	}
	else if (jointype == JOIN_UNIQUE_INNER)
	{
		inner_path = (Path *) create_unique_path(root, innerrel,
												 inner_path, extra->sjinfo);
		Assert(inner_path);
		jointype = JOIN_INNER;
	}

	/*
	 * If the joinrel is parallel-safe, we may be able to consider a partial
	 * merge join.  However, we can't handle JOIN_UNIQUE_OUTER, because the
	 * outer path will be partial, and therefore we won't be able to properly
	 * guarantee uniqueness.  Similarly, we can't handle JOIN_FULL and
	 * JOIN_RIGHT, because they can produce false null extended rows.  Also,
	 * the resulting path must not be parameterized.
	 */
	if (joinrel->consider_parallel &&
		save_jointype != JOIN_UNIQUE_OUTER &&
		save_jointype != JOIN_FULL &&
		save_jointype != JOIN_RIGHT &&
		outerrel->partial_pathlist != NIL &&
		bms_is_empty(joinrel->lateral_relids))
	{
		cheapest_partial_outer = (Path *) linitial(outerrel->partial_pathlist);

		if (inner_path->parallel_safe)
			cheapest_safe_inner = inner_path;
		else if (save_jointype != JOIN_UNIQUE_INNER)
			cheapest_safe_inner =
				get_cheapest_parallel_safe_total_inner(innerrel->pathlist);
	}

	/*
	 * Each possible ordering of the available mergejoin clauses will generate
	 * a differently-sorted result path at essentially the same cost.  We have
	 * no basis for choosing one over another at this level of joining, but
	 * some sort orders may be more useful than others for higher-level
	 * mergejoins, so it's worth considering multiple orderings.
	 *
	 * Actually, it's not quite true that every mergeclause ordering will
	 * generate a different path order, because some of the clauses may be
	 * partially redundant (refer to the same EquivalenceClasses).  Therefore,
	 * what we do is convert the mergeclause list to a list of canonical
	 * pathkeys, and then consider different orderings of the pathkeys.
	 *
	 * Generating a path for *every* permutation of the pathkeys doesn't seem
	 * like a winning strategy; the cost in planning time is too high. For
	 * now, we generate one path for each pathkey, listing that pathkey first
	 * and the rest in random order.  This should allow at least a one-clause
	 * mergejoin without re-sorting against any other possible mergejoin
	 * partner path.  But if we've not guessed the right ordering of secondary
	 * keys, we may end up evaluating clauses as qpquals when they could have
	 * been done as mergeclauses.  (In practice, it's rare that there's more
	 * than two or three mergeclauses, so expending a huge amount of thought
	 * on that is probably not worth it.)
	 *
	 * The pathkey order returned by select_outer_pathkeys_for_merge() has
	 * some heuristics behind it (see that function), so be sure to try it
	 * exactly as-is as well as making variants.
	 */
	all_pathkeys = select_outer_pathkeys_for_merge(root,
												   extra->mergeclause_list,
												   joinrel);

	foreach(l, all_pathkeys)
	{
		List	   *front_pathkey = (List *) lfirst(l);
		List	   *cur_mergeclauses;
		List	   *outerkeys;
		List	   *innerkeys;
		List	   *merge_pathkeys;

		/* Make a pathkey list with this guy first */
		if (l != list_head(all_pathkeys))
			outerkeys = lcons(front_pathkey,
							  list_delete_ptr(list_copy(all_pathkeys),
											  front_pathkey));
		else
			outerkeys = all_pathkeys;	/* no work at first one... */

		/* Sort the mergeclauses into the corresponding ordering */
		cur_mergeclauses =
			find_mergeclauses_for_outer_pathkeys(root,
												 outerkeys,
												 extra->mergeclause_list);

		/* Should have used them all... */
		Assert(list_length(cur_mergeclauses) == list_length(extra->mergeclause_list));

		/* Build sort pathkeys for the inner side */
		innerkeys = make_inner_pathkeys_for_merge(root,
												  cur_mergeclauses,
												  outerkeys);

		/* Build pathkeys representing output sort order */
		merge_pathkeys = build_join_pathkeys(root, joinrel, jointype,
											 outerkeys);

		/*
		 * And now we can make the path.
		 *
		 * Note: it's possible that the cheapest paths will already be sorted
		 * properly.  try_mergejoin_path will detect that case and suppress an
		 * explicit sort step, so we needn't do so here.
		 */
		try_mergejoin_path(root,
						   joinrel,
						   outer_path,
						   inner_path,
						   merge_pathkeys,
						   cur_mergeclauses,
						   outerkeys,
						   innerkeys,
						   jointype,
						   save_jointype,
						   extra,
						   false);

		/*
		 * If we have partial outer and parallel safe inner path then try
		 * partial mergejoin path.
		 */
		if (cheapest_partial_outer && cheapest_safe_inner)
			try_partial_mergejoin_path(root,
									   joinrel,
									   cheapest_partial_outer,
									   cheapest_safe_inner,
									   merge_pathkeys,
									   cur_mergeclauses,
									   outerkeys,
									   innerkeys,
									   jointype,
#ifdef MATRIXDB_VERSION
									   save_jointype,
#endif
									   extra);
	}

#ifdef MATRIXDB_VERSION
	if (save_jointype == JOIN_DEDUP_SEMI || save_jointype == JOIN_DEDUP_SEMI_REVERSE)
		joinrel->rows = saved_rel_rows;
#endif /* MATRIXDB_VERSION */
}

/*
 * match_unsorted_outer
 *	  Creates possible join paths for processing a single join relation
 *	  'joinrel' by employing either iterative substitution or
 *	  mergejoining on each of its possible outer paths (considering
 *	  only outer paths that are already ordered well enough for merging).
 *
 * We always generate a nestloop path for each available outer path.
 * In fact we may generate as many as five: one on the cheapest-total-cost
 * inner path, one on the same with materialization, one on the
 * cheapest-startup-cost inner path (if different), one on the
 * cheapest-total inner-indexscan path (if any), and one on the
 * cheapest-startup inner-indexscan path (if different).
 *
 * We also consider mergejoins if mergejoin clauses are available.  See
 * detailed comments in generate_mergejoin_paths.
 *
 * 'joinrel' is the join relation
 * 'outerrel' is the outer join relation
 * 'innerrel' is the inner join relation
 * 'jointype' is the type of join to do
 * 'extra' contains additional input values
 */
static void
match_unsorted_outer(PlannerInfo *root,
					 RelOptInfo *joinrel,
					 RelOptInfo *outerrel,
					 RelOptInfo *innerrel,
					 JoinType jointype,
					 JoinPathExtraData *extra)
{
	JoinType	save_jointype = jointype;
	bool		nestjoinOK;
	bool		useallclauses;
	Path	   *inner_cheapest_total = innerrel->cheapest_total_path;
	Path	   *matpath = NULL;
	ListCell   *lc1;

#ifdef MATRIXDB_VERSION
	double		saved_rel_rows = 0;
#endif /* MATRIXDB_VERSION */

#ifdef MATRIXDB_VERSION
	if (jointype == JOIN_DEDUP_SEMI || jointype == JOIN_DEDUP_SEMI_REVERSE)
	{
		Assert(extra->sjinfo->jointype == JOIN_SEMI);
		saved_rel_rows = joinrel->rows;
		/* we need to re-estimate the size of joinrel using JOIN_INNER */
		extra->sjinfo->jointype = JOIN_INNER;
		set_joinrel_size_estimates(root,
								   joinrel,
								   outerrel,
								   innerrel,
								   extra->sjinfo,
								   extra->restrictlist);

		/* bring back the JOIN_SEMI */
		extra->sjinfo->jointype = JOIN_SEMI;

		jointype = JOIN_INNER;
	}
#else /* MATRIXDB_VERSION */
	if (jointype == JOIN_DEDUP_SEMI || jointype == JOIN_DEDUP_SEMI_REVERSE)
		jointype = JOIN_INNER;
#endif /* MATRIXDB_VERSION */

	/*
	 * Nestloop only supports inner, left, semi, and anti joins.  Also, if we
	 * are doing a right or full mergejoin, we must use *all* the mergeclauses
	 * as join clauses, else we will not have a valid plan.  (Although these
	 * two flags are currently inverses, keep them separate for clarity and
	 * possible future changes.)
	 */
	switch (jointype)
	{
		case JOIN_INNER:
		case JOIN_LEFT:
		case JOIN_SEMI:
		case JOIN_ANTI:
		case JOIN_LASJ_NOTIN:
			nestjoinOK = true;
			useallclauses = false;
			break;
		case JOIN_RIGHT:
		case JOIN_FULL:
			nestjoinOK = false;
			useallclauses = true;
			break;
		case JOIN_UNIQUE_OUTER:
		case JOIN_UNIQUE_INNER:
			jointype = JOIN_INNER;
			nestjoinOK = true;
			useallclauses = false;
			break;
		default:
			elog(ERROR, "unrecognized join type: %d",
				 (int) jointype);
			nestjoinOK = false; /* keep compiler quiet */
			useallclauses = false;
			break;
	}

	/*
	 * If inner_cheapest_total is parameterized by the outer rel, ignore it;
	 * we will consider it below as a member of cheapest_parameterized_paths,
	 * but the other possibilities considered in this routine aren't usable.
	 */
	if (PATH_PARAM_BY_REL(inner_cheapest_total, outerrel))
		inner_cheapest_total = NULL;

	/*
	 * If we need to unique-ify the inner path, we will consider only the
	 * cheapest-total inner.
	 */
	if (save_jointype == JOIN_UNIQUE_INNER)
	{
		/* No way to do this with an inner path parameterized by outer rel */
		if (inner_cheapest_total == NULL)
			return;
		inner_cheapest_total = (Path *)
			create_unique_path(root, innerrel, inner_cheapest_total, extra->sjinfo);
		Assert(inner_cheapest_total);
	}
	else if (nestjoinOK)
	{
		/*
		 * Consider materializing the cheapest inner path, unless
		 * enable_material is off or the path in question materializes its
		 * output anyway.
		 */
		if (enable_material && inner_cheapest_total != NULL &&
			!ExecMaterializesOutput(inner_cheapest_total->pathtype))
			matpath = (Path *)
				create_material_path(root, innerrel, inner_cheapest_total);
	}

	foreach(lc1, outerrel->pathlist)
	{
		Path	   *outerpath = (Path *) lfirst(lc1);
		List	   *merge_pathkeys;

		/*
		 * We cannot use an outer path that is parameterized by the inner rel.
		 */
		if (PATH_PARAM_BY_REL(outerpath, innerrel))
			continue;

		/*
		 * If we need to unique-ify the outer path, it's pointless to consider
		 * any but the cheapest outer.  (XXX we don't consider parameterized
		 * outers, nor inners, for unique-ified cases.  Should we?)
		 */
		if (save_jointype == JOIN_UNIQUE_OUTER)
		{
			if (outerpath != outerrel->cheapest_total_path)
				continue;
			outerpath = (Path *) create_unique_path(root, outerrel,
													outerpath, extra->sjinfo);
			Assert(outerpath);
		}

		/*
		 * The result will have this sort order (even if it is implemented as
		 * a nestloop, and even if some of the mergeclauses are implemented by
		 * qpquals rather than as true mergeclauses):
		 */
		merge_pathkeys = build_join_pathkeys(root, joinrel, jointype,
											 outerpath->pathkeys);

		if (save_jointype == JOIN_UNIQUE_INNER)
		{
			/*
			 * Consider nestloop join, but only with the unique-ified cheapest
			 * inner path
			 */
			try_nestloop_path(root,
							  joinrel,
							  outerpath,
							  inner_cheapest_total,
							  merge_pathkeys,
							  jointype,
							  save_jointype,
							  extra);
		}
		else if (nestjoinOK)
		{
			/*
			 * Consider nestloop joins using this outer path and various
			 * available paths for the inner relation.  We consider the
			 * cheapest-total paths for each available parameterization of the
			 * inner relation, including the unparameterized case.
			 */
			ListCell   *lc2;

			foreach(lc2, innerrel->cheapest_parameterized_paths)
			{
				Path	   *innerpath = (Path *) lfirst(lc2);

#ifdef MATRIXDB_VERSION
				/*
				 * If the inner path is parameterized, don't consider rowid
				 * unique because one tuple in inner path might be selected
				 * out multiple times along with the index scan, this makes
				 * a unique tuple be decorated with different rowid and cause
				 * duplicated results.
				 */
				if (save_jointype == JOIN_DEDUP_SEMI_REVERSE)
					continue;
#endif /* MATRIXDB_VERSION */

				try_nestloop_path(root,
								  joinrel,
								  outerpath,
								  innerpath,
								  merge_pathkeys,
								  jointype,
								  save_jointype,
								  extra);
			}

			/* Also consider materialized form of the cheapest inner path */
			if (matpath != NULL)
				try_nestloop_path(root,
								  joinrel,
								  outerpath,
								  matpath,
								  merge_pathkeys,
								  jointype,
								  save_jointype,
								  extra);
		}

		/* Can't do anything else if outer path needs to be unique'd */
		if (save_jointype == JOIN_UNIQUE_OUTER)
			continue;

		/* Can't do anything else if inner rel is parameterized by outer */
		if (inner_cheapest_total == NULL)
			continue;

		/* Generate merge join paths */
		generate_mergejoin_paths(root, joinrel, innerrel, outerpath,
								 save_jointype, extra, useallclauses,
								 inner_cheapest_total, merge_pathkeys,
								 false);
	}

	/*
	 * Consider partial nestloop and mergejoin plan if outerrel has any
	 * partial path and the joinrel is parallel-safe.  However, we can't
	 * handle JOIN_UNIQUE_OUTER, because the outer path will be partial, and
	 * therefore we won't be able to properly guarantee uniqueness.  Nor can
	 * we handle extra_lateral_rels, since partial paths must not be
	 * parameterized. Similarly, we can't handle JOIN_FULL and JOIN_RIGHT,
	 * because they can produce false null extended rows.
	 */
	if (joinrel->consider_parallel &&
		save_jointype != JOIN_UNIQUE_OUTER &&
		save_jointype != JOIN_FULL &&
		save_jointype != JOIN_RIGHT &&
		outerrel->partial_pathlist != NIL &&
		bms_is_empty(joinrel->lateral_relids))
	{
		if (nestjoinOK)
			consider_parallel_nestloop(root, joinrel, outerrel, innerrel,
									   save_jointype, extra);

		/*
		 * If inner_cheapest_total is NULL or non parallel-safe then find the
		 * cheapest total parallel safe path.  If doing JOIN_UNIQUE_INNER, we
		 * can't use any alternative inner path.
		 */
		if (inner_cheapest_total == NULL ||
			!inner_cheapest_total->parallel_safe)
		{
			if (save_jointype == JOIN_UNIQUE_INNER)
				return;

			inner_cheapest_total = get_cheapest_parallel_safe_total_inner(
																		  innerrel->pathlist);
		}

		if (inner_cheapest_total)
			consider_parallel_mergejoin(root, joinrel, outerrel, innerrel,
										save_jointype, extra,
										inner_cheapest_total);
	}

#ifdef MATRIXDB_VERSION
	if (save_jointype == JOIN_DEDUP_SEMI || save_jointype == JOIN_DEDUP_SEMI_REVERSE)
		joinrel->rows = saved_rel_rows;
#endif /* MATRIXDB_VERSION */
}


/*
 * clause_sides_match_join
 *	  Determine whether a join clause is of the right form to use in this join.
 *
 * We already know that the clause is a binary opclause referencing only the
 * rels in the current join.  The point here is to check whether it has the
 * form "outerrel_expr op innerrel_expr" or "innerrel_expr op outerrel_expr",
 * rather than mixing outer and inner vars on either side.  If it matches,
 * we set the transient flag outer_is_left to identify which side is which.
 */
static inline bool
clause_sides_match_join(RestrictInfo *rinfo, RelOptInfo *outerrel,
						RelOptInfo *innerrel)
{
	if (bms_is_subset(rinfo->left_relids, outerrel->relids) &&
		bms_is_subset(rinfo->right_relids, innerrel->relids))
	{
		/* lefthand side is outer */
		rinfo->outer_is_left = true;
		return true;
	}
	else if (bms_is_subset(rinfo->left_relids, innerrel->relids) &&
			 bms_is_subset(rinfo->right_relids, outerrel->relids))
	{
		/* righthand side is outer */
		rinfo->outer_is_left = false;
		return true;
	}
	return false;				/* no good for these input relations */
}


/*
 * try_partial_hashjoin_path
 *	  Consider a partial hashjoin join path; if it appears useful, push it into
 *	  the joinrel's partial_pathlist via add_partial_path().
 *	  The outer side is partial.  If parallel_hash is true, then the inner path
 *	  must be partial and will be run in parallel to create one or more shared
 *	  hash tables; otherwise the inner path must be complete and a copy of it
 *	  is run in every process to create separate identical private hash tables.
 */
static void
try_partial_hashjoin_path(PlannerInfo *root,
						  RelOptInfo *joinrel,
						  Path *outer_path,
						  Path *inner_path,
						  List *hashclauses,
						  JoinType jointype,
						  JoinType orig_jointype,
						  JoinPathExtraData *extra,
						  bool parallel_hash)
{
	JoinCostWorkspace workspace;

	/*
	 * If the inner path is parameterized, the parameterization must be fully
	 * satisfied by the proposed outer path.  Parameterized partial paths are
	 * not supported.  The caller should already have verified that no
	 * extra_lateral_rels are required here.
	 */
	Assert(bms_is_empty(joinrel->lateral_relids));
	if (inner_path->param_info != NULL)
	{
		Relids		inner_paramrels = inner_path->param_info->ppi_req_outer;

		if (!bms_is_empty(inner_paramrels))
			return;
	}

#ifdef MATRIXDB_VERSION
	/* 
	 * GPDB: for parallel hashjoin, it's only efficient when the outer/inner are
	 * co-located
	 */
	if (parallel_hash &&
		!cdbpath_match_preds_to_both_distkeys(root,
											  extra->redistribution_clauses,
											  outer_path,
											  inner_path,
											  outer_path->locus,
											  inner_path->locus,
											  true))
		return;	
#endif /* MATRIXDB_VERSION */

	/*
	 * Before creating a path, get a quick lower bound on what it is likely to
	 * cost.  Bail out right away if it looks terrible.
	 */
	initial_cost_hashjoin(root, &workspace, jointype, hashclauses,
						  outer_path, inner_path, extra, parallel_hash);
	if (!add_partial_path_precheck(joinrel, workspace.total_cost, NIL))
		return;

	/* Might be good enough to be worth trying, so let's try it. */
	add_partial_path(joinrel, (Path *)
					 create_hashjoin_path(root,
										  joinrel,
										  jointype,
										  orig_jointype,
										  &workspace,
										  extra,
										  outer_path,
										  inner_path,
										  parallel_hash,
#ifdef MATRIXDB_VERSION
										  true,
#endif
										  extra->restrictlist,
										  NULL,
										  extra->redistribution_clauses,
										  hashclauses));
#ifdef MATRIXDB_VERSION
	add_partial_path(joinrel, (Path *)
					 create_hashjoin_path(root,
										  joinrel,
										  jointype,
										  orig_jointype,
										  &workspace,
										  extra,
										  outer_path,
										  inner_path,
										  parallel_hash,
										  false,
										  extra->restrictlist,
										  NULL,
										  extra->redistribution_clauses,
										  hashclauses));
#endif
}

/*
 * cdbpath_eclass_constant_is_hashable
 *
 * Iterates through a list of equivalence class members and determines if
 * expression in pseudoconstant is hashable under the given hash opfamily.
 *
 * If there are multiple constants in the equivalence class, it is sufficient
 * that one of them is usable.
 */
static bool
cdbpath_eclass_constant_is_hashable(EquivalenceClass *ec, Oid hashOpFamily)
{
	ListCell   *j;

	foreach(j, ec->ec_members)
	{
		EquivalenceMember *em = (EquivalenceMember *) lfirst(j);

		if (!em->em_is_const)
			continue;

		if (get_opfamily_member(hashOpFamily, em->em_datatype, em->em_datatype,
								HTEqualStrategyNumber))
			return true;
	}

	return false;
}

static bool
ECAllMemberContainParam(EquivalenceClass *ec, CdbpathMatchPredsContext *ctx)
{
	ListCell *lc;
	foreach(lc, ec->ec_members)
	{
		EquivalenceMember *em = (EquivalenceMember *) lfirst(lc);
		Bitmapset *em_param_ids = NULL;
		expr_param_walker(em->em_expr, &em_param_ids);

		if (bms_is_empty(em_param_ids))
			return false;
	}

	return true;
}


/*
 * A helper function to create a DistributionKey for an EquivalenceClass.
 */
static DistributionKey *
makeDistributionKeyForEC(EquivalenceClass *eclass, Oid opfamily)
{
	DistributionKey *dk = makeNode(DistributionKey);

	Assert(OidIsValid(opfamily));

	dk->dk_eclasses = list_make1(eclass);
	dk->dk_opfamily = opfamily;

#ifdef MATRIXDB_VERSION
	dk->dk_opclass = InvalidOid;
#endif /* MATRIXDB_VERSION */

	return dk;
}


/*
 * consider_parallel_mergejoin
 *	  Try to build partial paths for a joinrel by joining a partial path
 *	  for the outer relation to a complete path for the inner relation.
 *
 * 'joinrel' is the join relation
 * 'outerrel' is the outer join relation
 * 'innerrel' is the inner join relation
 * 'jointype' is the type of join to do
 * 'extra' contains additional input values
 * 'inner_cheapest_total' cheapest total path for innerrel
 */
static void
consider_parallel_mergejoin(PlannerInfo *root,
							RelOptInfo *joinrel,
							RelOptInfo *outerrel,
							RelOptInfo *innerrel,
							JoinType jointype,
							JoinPathExtraData *extra,
							Path *inner_cheapest_total)
{
	ListCell   *lc1;

	/* generate merge join path for each partial outer path */
	foreach(lc1, outerrel->partial_pathlist)
	{
		Path	   *outerpath = (Path *) lfirst(lc1);
		List	   *merge_pathkeys;

		/*
		 * Figure out what useful ordering any paths we create will have.
		 */
		merge_pathkeys = build_join_pathkeys(root, joinrel, jointype,
											 outerpath->pathkeys);

		generate_mergejoin_paths(root, joinrel, innerrel, outerpath, jointype,
								 extra, false, inner_cheapest_total,
								 merge_pathkeys, true);
	}
}



/*
 * try_mergejoin_path
 *	  Consider a merge join path; if it appears useful, push it into
 *	  the joinrel's pathlist via add_path().
 */
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
				   bool is_partial)
{
	Relids		required_outer;
	JoinCostWorkspace workspace;

	if (is_partial)
	{
		try_partial_mergejoin_path(root,
								   joinrel,
								   outer_path,
								   inner_path,
								   pathkeys,
								   mergeclauses,
								   outersortkeys,
								   innersortkeys,
								   jointype,
#ifdef MATRIXDB_VERSION
								   orig_jointype,
#endif
								   extra);
		return;
	}

	/*
	 * Check to see if proposed path is still parameterized, and reject if the
	 * parameterization wouldn't be sensible.
	 */
	required_outer = calc_non_nestloop_required_outer(outer_path,
													  inner_path);
	if (required_outer &&
		!bms_overlap(required_outer, extra->param_source_rels))
	{
		/* Waste no memory when we reject a path here */
		bms_free(required_outer);
		return;
	}

	/*
	 * If the given paths are already well enough ordered, we can skip doing
	 * an explicit sort.
	 */
	if (outersortkeys &&
		pathkeys_contained_in(outersortkeys, outer_path->pathkeys))
		outersortkeys = NIL;
	if (innersortkeys &&
		pathkeys_contained_in(innersortkeys, inner_path->pathkeys))
		innersortkeys = NIL;

	/*
	 * See comments in try_nestloop_path().
	 */
	initial_cost_mergejoin(root, &workspace, jointype, mergeclauses,
						   outer_path, inner_path,
						   outersortkeys, innersortkeys,
						   extra);

	if (add_path_precheck(joinrel,
						  workspace.startup_cost, workspace.total_cost,
						  pathkeys, required_outer))
	{
		add_path(joinrel, (Path *)
				 create_mergejoin_path(root,
									   joinrel,
									   jointype,
									   orig_jointype,
									   &workspace,
									   extra,
									   outer_path,
									   inner_path,
									   extra->restrictlist,
									   pathkeys,
									   required_outer,
									   mergeclauses,
									   extra->redistribution_clauses,
									   outersortkeys,
									   innersortkeys));
	}
	else
	{
		/* Waste no memory when we reject a path here */
		bms_free(required_outer);
	}
}


/*
 * try_partial_mergejoin_path
 *	  Consider a partial merge join path; if it appears useful, push it into
 *	  the joinrel's pathlist via add_partial_path().
 */
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
						   JoinPathExtraData *extra)
{
	JoinCostWorkspace workspace;

	/*
	 * See comments in try_partial_hashjoin_path().
	 */
	Assert(bms_is_empty(joinrel->lateral_relids));
	if (inner_path->param_info != NULL)
	{
		Relids		inner_paramrels = inner_path->param_info->ppi_req_outer;

		if (!bms_is_empty(inner_paramrels))
			return;
	}

	/*
	 * If the given paths are already well enough ordered, we can skip doing
	 * an explicit sort.
	 */
	if (outersortkeys &&
		pathkeys_contained_in(outersortkeys, outer_path->pathkeys))
		outersortkeys = NIL;
	if (innersortkeys &&
		pathkeys_contained_in(innersortkeys, inner_path->pathkeys))
		innersortkeys = NIL;

	/*
	 * See comments in try_partial_nestloop_path().
	 */
	initial_cost_mergejoin(root, &workspace, jointype, mergeclauses,
						   outer_path, inner_path,
						   outersortkeys, innersortkeys,
						   extra);

	if (!add_partial_path_precheck(joinrel, workspace.total_cost, pathkeys))
		return;

	/* Might be good enough to be worth trying, so let's try it. */
	add_partial_path(joinrel, (Path *)
					 create_mergejoin_path(root,
										   joinrel,
										   jointype,
										   orig_jointype,
										   &workspace,
										   extra,
										   outer_path,
										   inner_path,
										   extra->restrictlist,
										   pathkeys,
										   NULL,
										   mergeclauses,
										   extra->redistribution_clauses,
										   outersortkeys,
										   innersortkeys));
}


/*
 * try_nestloop_path
 *	  Consider a nestloop join path; if it appears useful, push it into
 *	  the joinrel's pathlist via add_path().
 */
static void
try_nestloop_path(PlannerInfo *root,
				  RelOptInfo *joinrel,
				  Path *outer_path,
				  Path *inner_path,
				  List *pathkeys,
				  JoinType jointype,
				  JoinType orig_jointype,	/* CDB */
				  JoinPathExtraData *extra)
{
	Relids		required_outer;
	JoinCostWorkspace workspace;
	RelOptInfo *innerrel = inner_path->parent;
	RelOptInfo *outerrel = outer_path->parent;
	Relids		innerrelids;
	Relids		outerrelids;
	Relids		inner_paramrels = PATH_REQ_OUTER(inner_path);
	Relids		outer_paramrels = PATH_REQ_OUTER(outer_path);

	/*
	 * Paths are parameterized by top-level parents, so run parameterization
	 * tests on the parent relids.
	 */
	if (innerrel->top_parent_relids)
		innerrelids = innerrel->top_parent_relids;
	else
		innerrelids = innerrel->relids;

	if (outerrel->top_parent_relids)
		outerrelids = outerrel->top_parent_relids;
	else
		outerrelids = outerrel->relids;

	/*
	 * Check to see if proposed path is still parameterized, and reject if the
	 * parameterization wouldn't be sensible --- unless allow_star_schema_join
	 * says to allow it anyway.  Also, we must reject if have_dangerous_phv
	 * doesn't like the look of it, which could only happen if the nestloop is
	 * still parameterized.
	 */
	required_outer = calc_nestloop_required_outer(outerrelids, outer_paramrels,
												  innerrelids, inner_paramrels);
	if (required_outer &&
		((!bms_overlap(required_outer, extra->param_source_rels) &&
		  !allow_star_schema_join(root, outerrelids, inner_paramrels)) ||
		 have_dangerous_phv(root, outerrelids, inner_paramrels)))
	{
		/* Waste no memory when we reject a path here */
		bms_free(required_outer);
		return;
	}

	/*
	 * Do a precheck to quickly eliminate obviously-inferior paths.  We
	 * calculate a cheap lower bound on the path's cost and then use
	 * add_path_precheck() to see if the path is clearly going to be dominated
	 * by some existing path for the joinrel.  If not, do the full pushup with
	 * creating a fully valid path structure and submitting it to add_path().
	 * The latter two steps are expensive enough to make this two-phase
	 * methodology worthwhile.
	 */
	initial_cost_nestloop(root, &workspace, jointype,
						  outer_path, inner_path, extra);

	if (add_path_precheck(joinrel,
						  workspace.startup_cost, workspace.total_cost,
						  pathkeys, required_outer))
	{
		/*
		 * If the inner path is parameterized, it is parameterized by the
		 * topmost parent of the outer rel, not the outer rel itself.  Fix
		 * that.
		 */
		if (PATH_PARAM_BY_PARENT(inner_path, outer_path->parent))
		{
			inner_path = reparameterize_path_by_child(root, inner_path,
													  outer_path->parent);

			/*
			 * If we could not translate the path, we can't create nest loop
			 * path.
			 */
			if (!inner_path)
			{
				bms_free(required_outer);
				return;
			}
		}

		add_path(joinrel, (Path *)
				 create_nestloop_path(root,
									  joinrel,
									  jointype,
									  orig_jointype,
									  &workspace,
									  extra,
									  outer_path,
									  inner_path,
									  extra->restrictlist,
									  extra->redistribution_clauses,
									  pathkeys,
									  required_outer));
	}
	else
	{
		/* Waste no memory when we reject a path here */
		bms_free(required_outer);
	}
}

/*
 * We override the param_source_rels heuristic to accept nestloop paths in
 * which the outer rel satisfies some but not all of the inner path's
 * parameterization.  This is necessary to get good plans for star-schema
 * scenarios, in which a parameterized path for a large table may require
 * parameters from multiple small tables that will not get joined directly to
 * each other.  We can handle that by stacking nestloops that have the small
 * tables on the outside; but this breaks the rule the param_source_rels
 * heuristic is based on, namely that parameters should not be passed down
 * across joins unless there's a join-order-constraint-based reason to do so.
 * So we ignore the param_source_rels restriction when this case applies.
 *
 * allow_star_schema_join() returns true if the param_source_rels restriction
 * should be overridden, ie, it's okay to perform this join.
 */
static inline bool
allow_star_schema_join(PlannerInfo *root,
					   Relids outerrelids,
					   Relids inner_paramrels)
{
	/*
	 * It's a star-schema case if the outer rel provides some but not all of
	 * the inner rel's parameterization.
	 */
	return (bms_overlap(inner_paramrels, outerrelids) &&
			bms_nonempty_difference(inner_paramrels, outerrelids));
}

/*
 * consider_parallel_nestloop
 *	  Try to build partial paths for a joinrel by joining a partial path for the
 *	  outer relation to a complete path for the inner relation.
 *
 * 'joinrel' is the join relation
 * 'outerrel' is the outer join relation
 * 'innerrel' is the inner join relation
 * 'jointype' is the type of join to do
 * 'extra' contains additional input values
 */
static void
consider_parallel_nestloop(PlannerInfo *root,
						   RelOptInfo *joinrel,
						   RelOptInfo *outerrel,
						   RelOptInfo *innerrel,
						   JoinType jointype,
						   JoinPathExtraData *extra)
{
	JoinType	save_jointype = jointype;
	ListCell   *lc1;

	if (jointype == JOIN_UNIQUE_INNER)
		jointype = JOIN_INNER;

	foreach(lc1, outerrel->partial_pathlist)
	{
		Path	   *outerpath = (Path *) lfirst(lc1);
		List	   *pathkeys;
		ListCell   *lc2;

		/* Figure out what useful ordering any paths we create will have. */
		pathkeys = build_join_pathkeys(root, joinrel, jointype,
									   outerpath->pathkeys);

		/*
		 * Try the cheapest parameterized paths; only those which will produce
		 * an unparameterized path when joined to this outerrel will survive
		 * try_partial_nestloop_path.  The cheapest unparameterized path is
		 * also in this list.
		 */
		foreach(lc2, innerrel->cheapest_parameterized_paths)
		{
			Path	   *innerpath = (Path *) lfirst(lc2);

			/* Can't join to an inner path that is not parallel-safe */
			if (!innerpath->parallel_safe)
				continue;

			/*
			 * If we're doing JOIN_UNIQUE_INNER, we can only use the inner's
			 * cheapest_total_path, and we have to unique-ify it.  (We might
			 * be able to relax this to allow other safe, unparameterized
			 * inner paths, but right now create_unique_path is not on board
			 * with that.)
			 */
			if (save_jointype == JOIN_UNIQUE_INNER)
			{
				if (innerpath != innerrel->cheapest_total_path)
					continue;
				innerpath = (Path *) create_unique_path(root, innerrel,
														innerpath,
														extra->sjinfo);
				Assert(innerpath);
			}

			try_partial_nestloop_path(root, joinrel, outerpath, innerpath,
									  pathkeys, jointype,
									  save_jointype,
									  extra);
		}

#ifdef MATRIXDB_VERSION
		/* try cheapest inner partial path */
		if (innerrel->partial_pathlist && save_jointype != JOIN_UNIQUE_INNER)
		{
			Path *innerpath = (Path *) linitial(innerrel->partial_pathlist);

			try_partial_nestloop_path(root, joinrel, outerpath, innerpath,
									  pathkeys, jointype,
									  save_jointype,
									  extra);
		}
#endif /* MATRIXDB_VERSION */
	}
}

/*
 * try_partial_nestloop_path
 *	  Consider a partial nestloop join path; if it appears useful, push it into
 *	  the joinrel's partial_pathlist via add_partial_path().
 */
static void
try_partial_nestloop_path(PlannerInfo *root,
						  RelOptInfo *joinrel,
						  Path *outer_path,
						  Path *inner_path,
						  List *pathkeys,
						  JoinType jointype,
						  JoinType orig_jointype,
						  JoinPathExtraData *extra)
{
	JoinCostWorkspace workspace;

	/*
	 * If the inner path is parameterized, the parameterization must be fully
	 * satisfied by the proposed outer path.  Parameterized partial paths are
	 * not supported.  The caller should already have verified that no
	 * extra_lateral_rels are required here.
	 */
	Assert(bms_is_empty(joinrel->lateral_relids));
	if (inner_path->param_info != NULL)
	{
		Relids		inner_paramrels = inner_path->param_info->ppi_req_outer;
		RelOptInfo *outerrel = outer_path->parent;
		Relids		outerrelids;

		/*
		 * The inner and outer paths are parameterized, if at all, by the top
		 * level parents, not the child relations, so we must use those relids
		 * for our parameterization tests.
		 */
		if (outerrel->top_parent_relids)
			outerrelids = outerrel->top_parent_relids;
		else
			outerrelids = outerrel->relids;

		if (!bms_is_subset(inner_paramrels, outerrelids))
			return;
	}

	/*
	 * Before creating a path, get a quick lower bound on what it is likely to
	 * cost.  Bail out right away if it looks terrible.
	 */
	initial_cost_nestloop(root, &workspace, jointype,
						  outer_path, inner_path, extra);
	if (!add_partial_path_precheck(joinrel, workspace.total_cost, pathkeys))
		return;

	/*
	 * If the inner path is parameterized, it is parameterized by the topmost
	 * parent of the outer rel, not the outer rel itself.  Fix that.
	 */
	if (PATH_PARAM_BY_PARENT(inner_path, outer_path->parent))
	{
		inner_path = reparameterize_path_by_child(root, inner_path,
												  outer_path->parent);

		/*
		 * If we could not translate the path, we can't create nest loop path.
		 */
		if (!inner_path)
			return;
	}

	/* Might be good enough to be worth trying, so let's try it. */
	add_partial_path(joinrel, (Path *)
					 create_nestloop_path(root,
										  joinrel,
										  jointype,
										  orig_jointype,
										  &workspace,
										  extra,
										  outer_path,
										  inner_path,
										  extra->restrictlist,
										  extra->redistribution_clauses,
										  pathkeys,
										  NULL));
}


/*
 * generate_mergejoin_paths
 *	Creates possible mergejoin paths for input outerpath.
 *
 * We generate mergejoins if mergejoin clauses are available.  We have
 * two ways to generate the inner path for a mergejoin: sort the cheapest
 * inner path, or use an inner path that is already suitably ordered for the
 * merge.  If we have several mergeclauses, it could be that there is no inner
 * path (or only a very expensive one) for the full list of mergeclauses, but
 * better paths exist if we truncate the mergeclause list (thereby discarding
 * some sort key requirements).  So, we consider truncations of the
 * mergeclause list as well as the full list.  (Ideally we'd consider all
 * subsets of the mergeclause list, but that seems way too expensive.)
 */
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
						 bool is_partial)
{
	List	   *mergeclauses;
	List	   *innersortkeys;
	List	   *trialsortkeys;
	Path	   *cheapest_startup_inner;
	Path	   *cheapest_total_inner;
	JoinType	save_jointype = jointype;
	int			num_sortkeys;
	int			sortkeycnt;

	/* The merge join executor code doesn't support LASJ_NOTIN */
	if (jointype == JOIN_LASJ_NOTIN)
		return;

	if (jointype == JOIN_UNIQUE_OUTER || jointype == JOIN_UNIQUE_INNER)
		jointype = JOIN_INNER;

	if (jointype == JOIN_DEDUP_SEMI || jointype == JOIN_DEDUP_SEMI_REVERSE)
		jointype = JOIN_INNER;

	/* Look for useful mergeclauses (if any) */
	mergeclauses =
		find_mergeclauses_for_outer_pathkeys(root,
											 outerpath->pathkeys,
											 extra->mergeclause_list);

	/*
	 * Done with this outer path if no chance for a mergejoin.
	 *
	 * Special corner case: for "x FULL JOIN y ON true", there will be no join
	 * clauses at all.  Ordinarily we'd generate a clauseless nestloop path,
	 * but since mergejoin is our only join type that supports FULL JOIN
	 * without any join clauses, it's necessary to generate a clauseless
	 * mergejoin path instead.
	 */
	if (mergeclauses == NIL)
	{
		if (jointype == JOIN_FULL)
			 /* okay to try for mergejoin */ ;
		else
			return;
	}
	if (useallclauses &&
		list_length(mergeclauses) != list_length(extra->mergeclause_list))
		return;

	/* Compute the required ordering of the inner path */
	innersortkeys = make_inner_pathkeys_for_merge(root,
												  mergeclauses,
												  outerpath->pathkeys);

	/*
	 * Generate a mergejoin on the basis of sorting the cheapest inner. Since
	 * a sort will be needed, only cheapest total cost matters. (But
	 * try_mergejoin_path will do the right thing if inner_cheapest_total is
	 * already correctly sorted.)
	 */
	try_mergejoin_path(root,
					   joinrel,
					   outerpath,
					   inner_cheapest_total,
					   merge_pathkeys,
					   mergeclauses,
					   NIL,
					   innersortkeys,
					   jointype,
					   save_jointype,
					   extra,
					   is_partial);

	/* Can't do anything else if inner path needs to be unique'd */
	if (save_jointype == JOIN_UNIQUE_INNER)
		return;

	/*
	 * Look for presorted inner paths that satisfy the innersortkey list ---
	 * or any truncation thereof, if we are allowed to build a mergejoin using
	 * a subset of the merge clauses.  Here, we consider both cheap startup
	 * cost and cheap total cost.
	 *
	 * Currently we do not consider parameterized inner paths here. This
	 * interacts with decisions elsewhere that also discriminate against
	 * mergejoins with parameterized inputs; see comments in
	 * src/backend/optimizer/README.
	 *
	 * As we shorten the sortkey list, we should consider only paths that are
	 * strictly cheaper than (in particular, not the same as) any path found
	 * in an earlier iteration.  Otherwise we'd be intentionally using fewer
	 * merge keys than a given path allows (treating the rest as plain
	 * joinquals), which is unlikely to be a good idea.  Also, eliminating
	 * paths here on the basis of compare_path_costs is a lot cheaper than
	 * building the mergejoin path only to throw it away.
	 *
	 * If inner_cheapest_total is well enough sorted to have not required a
	 * sort in the path made above, we shouldn't make a duplicate path with
	 * it, either.  We handle that case with the same logic that handles the
	 * previous consideration, by initializing the variables that track
	 * cheapest-so-far properly.  Note that we do NOT reject
	 * inner_cheapest_total if we find it matches some shorter set of
	 * pathkeys.  That case corresponds to using fewer mergekeys to avoid
	 * sorting inner_cheapest_total, whereas we did sort it above, so the
	 * plans being considered are different.
	 */
	if (pathkeys_contained_in(innersortkeys,
							  inner_cheapest_total->pathkeys))
	{
		/* inner_cheapest_total didn't require a sort */
		cheapest_startup_inner = inner_cheapest_total;
		cheapest_total_inner = inner_cheapest_total;
	}
	else
	{
		/* it did require a sort, at least for the full set of keys */
		cheapest_startup_inner = NULL;
		cheapest_total_inner = NULL;
	}
	num_sortkeys = list_length(innersortkeys);
	if (num_sortkeys > 1 && !useallclauses)
		trialsortkeys = list_copy(innersortkeys);	/* need modifiable copy */
	else
		trialsortkeys = innersortkeys;	/* won't really truncate */

	for (sortkeycnt = num_sortkeys; sortkeycnt > 0; sortkeycnt--)
	{
		Path	   *innerpath;
		List	   *newclauses = NIL;

		/*
		 * Look for an inner path ordered well enough for the first
		 * 'sortkeycnt' innersortkeys.  NB: trialsortkeys list is modified
		 * destructively, which is why we made a copy...
		 */
		trialsortkeys = list_truncate(trialsortkeys, sortkeycnt);
		innerpath = get_cheapest_path_for_pathkeys(innerrel->pathlist,
												   trialsortkeys,
												   NULL,
												   TOTAL_COST,
												   is_partial);
		if (innerpath != NULL &&
			(cheapest_total_inner == NULL ||
			 compare_path_costs(innerpath, cheapest_total_inner,
								TOTAL_COST) < 0))
		{
			/* Found a cheap (or even-cheaper) sorted path */
			/* Select the right mergeclauses, if we didn't already */
			if (sortkeycnt < num_sortkeys)
			{
				newclauses =
					trim_mergeclauses_for_inner_pathkeys(root,
														 mergeclauses,
														 trialsortkeys);
				Assert(newclauses != NIL);
			}
			else
				newclauses = mergeclauses;
			try_mergejoin_path(root,
							   joinrel,
							   outerpath,
							   innerpath,
							   merge_pathkeys,
							   newclauses,
							   NIL,
							   NIL,
							   jointype,
							   save_jointype,
							   extra,
							   is_partial);
			cheapest_total_inner = innerpath;
		}
		/* Same on the basis of cheapest startup cost ... */
		innerpath = get_cheapest_path_for_pathkeys(innerrel->pathlist,
												   trialsortkeys,
												   NULL,
												   STARTUP_COST,
												   is_partial);
		if (innerpath != NULL &&
			(cheapest_startup_inner == NULL ||
			 compare_path_costs(innerpath, cheapest_startup_inner,
								STARTUP_COST) < 0))
		{
			/* Found a cheap (or even-cheaper) sorted path */
			if (innerpath != cheapest_total_inner)
			{
				/*
				 * Avoid rebuilding clause list if we already made one; saves
				 * memory in big join trees...
				 */
				if (newclauses == NIL)
				{
					if (sortkeycnt < num_sortkeys)
					{
						newclauses =
							trim_mergeclauses_for_inner_pathkeys(root,
																 mergeclauses,
																 trialsortkeys);
						Assert(newclauses != NIL);
					}
					else
						newclauses = mergeclauses;
				}
				try_mergejoin_path(root,
								   joinrel,
								   outerpath,
								   innerpath,
								   merge_pathkeys,
								   newclauses,
								   NIL,
								   NIL,
								   jointype,
								   save_jointype,
								   extra,
								   is_partial);
			}
			cheapest_startup_inner = innerpath;
		}

		/*
		 * Don't consider truncated sortkeys if we need all clauses.
		 */
		if (useallclauses)
			break;
	}
}

static bool
expr_param_walker(Expr *expr, Bitmapset** param_ids)
{
	if (IsA(expr, Param))
	{
		*param_ids = bms_add_member(*param_ids, ((Param *)expr)->paramid);
		return false;
	}

	return expression_tree_walker(expr, expr_param_walker, param_ids);
}


/*
 * create_mergejoin_path
 *	  Creates a pathnode corresponding to a mergejoin join between
 *	  two relations
 *
 * 'joinrel' is the join relation
 * 'jointype' is the type of join required
 * 'workspace' is the result from initial_cost_mergejoin
 * 'extra' contains various information about the join
 * 'outer_path' is the outer path
 * 'inner_path' is the inner path
 * 'restrict_clauses' are the RestrictInfo nodes to apply at the join
 * 'pathkeys' are the path keys of the new join path
 * 'required_outer' is the set of required outer rels
 * 'mergeclauses' are the RestrictInfo nodes to use as merge clauses
 *		(this should be a subset of the restrict_clauses list)
 * 'allmergeclauses' are the RestrictInfo nodes that are of the form
 *      required of merge clauses (equijoin between outer and inner rel).
 *      Consists of the ones to be used for merging ('mergeclauses') plus
 *      any others in 'restrict_clauses' that are to be applied after the
 *      merge.  We use them for motion planning.  (CDB)

 * 'outersortkeys' are the sort varkeys for the outer relation
 *      or NIL to use existing ordering
 * 'innersortkeys' are the sort varkeys for the inner relation
 *      or NIL to use existing ordering
 */
Path *
create_mergejoin_path(PlannerInfo *root,
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
					  List *innersortkeys)
{
	MergePath  *pathnode = makeNode(MergePath);
	CdbPathLocus join_locus;
	List	   *outermotionkeys;
	List	   *innermotionkeys;
	bool		preserve_outer_ordering;
	bool		preserve_inner_ordering;
	int			rowidexpr_id;

	/*
	 * GPDB_92_MERGE_FIXME: Should we keep the pathkeys_contained_in calls?
	 */
	/*
	 * Do subpaths have useful ordering?
	 */
	if (outersortkeys == NIL)           /* must preserve existing ordering */
		outermotionkeys = outer_path->pathkeys;
	else if (pathkeys_contained_in(outersortkeys, outer_path->pathkeys))
		outermotionkeys = outersortkeys;/* lucky coincidence, already ordered */
	else                                /* existing order useless; must sort */
		outermotionkeys = NIL;

	if (innersortkeys == NIL)
		innermotionkeys = inner_path->pathkeys;
	else if (pathkeys_contained_in(innersortkeys, inner_path->pathkeys))
		innermotionkeys = innersortkeys;
	else
		innermotionkeys = NIL;

	/*
	 * Add motion nodes above subpaths and decide where to join.
	 *
	 * If we're explicitly sorting one or both sides of the join, don't choose
	 * a Motion that would break that ordering again. But as a special case,
	 * if there are no merge clauses, then there is no join order that would need
	 * preserving. That case can occur with a query like "a FULL JOIN b ON true"
	 */
	if (mergeclauses)
	{
		preserve_outer_ordering = (outersortkeys == NIL);
		preserve_inner_ordering = (innersortkeys == NIL);
	}
	else
		preserve_outer_ordering = preserve_inner_ordering = false;

	preserve_outer_ordering = preserve_outer_ordering || !bms_is_empty(PATH_REQ_OUTER(outer_path));
	preserve_inner_ordering = preserve_inner_ordering || !bms_is_empty(PATH_REQ_OUTER(inner_path));

	join_locus = cdbpath_motion_for_join(root,
										 orig_jointype,
										 &outer_path,       /* INOUT */
										 &inner_path,       /* INOUT */
										 &rowidexpr_id,
										 redistribution_clauses,
										 restrict_clauses,
										 outermotionkeys,
										 innermotionkeys,
										 preserve_outer_ordering,
#ifdef MATRIXDB_VERSION
										 preserve_inner_ordering,
										 true,
										 false);
#else /* MATRIXDB_VERSION */
										 preserve_inner_ordering);
#endif /* MATRIXDB_VERSION */

	if (CdbPathLocus_IsNull(join_locus))
		return NULL;

	/*
	 * Sort is not needed if subpath is already well enough ordered and a
	 * disordering motion node (with pathkeys == NIL) hasn't been added.
	 */
	if (outermotionkeys &&
		outer_path->pathkeys)
		outersortkeys = NIL;
	if (innermotionkeys &&
		inner_path->pathkeys)
		innersortkeys = NIL;

#ifdef MATRIXDB_VERSION
	if (Gp_role == GP_ROLE_DISPATCH)
	{
		bool		has_open_wtscan;

		has_open_wtscan = path_contains_same_slice_wts(inner_path);
		has_open_wtscan |= path_contains_same_slice_wts(outer_path);

		/*
		 * In MergeJoin rescan, it needs both side node rescan. Holding the all data
		 * in current slice is not efficient.
		 */
		if (has_open_wtscan)
		{
			if (!outer_path->rescannable)
				outer_path = (Path *)create_material_path(root, outer_path->parent, outer_path);

			if (!inner_path->rescannable)
				inner_path = (Path *)create_material_path(root, inner_path->parent, inner_path);
		}
	}
#endif

	pathnode->jpath.path.pathtype = T_MergeJoin;
	pathnode->jpath.path.parent = joinrel;
	pathnode->jpath.path.pathtarget = joinrel->reltarget;
	pathnode->jpath.path.param_info =
		get_joinrel_parampathinfo(root,
								  joinrel,
								  outer_path,
								  inner_path,
								  extra->sjinfo,
								  required_outer,
								  &restrict_clauses);
	pathnode->jpath.path.parallel_aware = false;
	pathnode->jpath.path.parallel_safe = joinrel->consider_parallel &&
		outer_path->parallel_safe && inner_path->parallel_safe;
	/* This is a foolish way to estimate parallel_workers, but for now... */
#ifdef MATRIXDB_VERSION
	/*
	 * In Matrixdb, let's keep it the same with the join_locus after
	 * the motions are decorated
	 */
	pathnode->jpath.path.parallel_workers = join_locus.parallel_workers;
#else
	pathnode->jpath.path.parallel_workers = outer_path->parallel_workers;
#endif /* MATRIXDB_VERSION */
	pathnode->jpath.path.pathkeys = pathkeys;

	pathnode->jpath.path.locus = join_locus;

	pathnode->jpath.path.motionHazard = outer_path->motionHazard || inner_path->motionHazard;
	pathnode->jpath.path.rescannable = outer_path->rescannable && inner_path->rescannable;
	pathnode->jpath.path.sameslice_relids = bms_union(inner_path->sameslice_relids, outer_path->sameslice_relids);

	pathnode->jpath.jointype = jointype;
	pathnode->jpath.inner_unique = extra->inner_unique;
	pathnode->jpath.outerjoinpath = outer_path;
	pathnode->jpath.innerjoinpath = inner_path;
	pathnode->jpath.joinrestrictinfo = restrict_clauses;
	pathnode->path_mergeclauses = mergeclauses;
	pathnode->outersortkeys = outersortkeys;
	pathnode->innersortkeys = innersortkeys;
	/* pathnode->skip_mark_restore will be set by final_cost_mergejoin */
	/* pathnode->materialize_inner will be set by final_cost_mergejoin */

	/*
	 * inner_path & outer_path are possibly modified above. Let's recalculate
	 * the initial cost.
	 */
	initial_cost_mergejoin(root, workspace, jointype, mergeclauses,
						   outer_path, inner_path,
						   outersortkeys, innersortkeys,
						   extra);

	final_cost_mergejoin(root, pathnode, workspace, extra);

	if (orig_jointype == JOIN_DEDUP_SEMI ||
		orig_jointype == JOIN_DEDUP_SEMI_REVERSE)
	{
		return (Path *) create_unique_rowid_path(root,
												 joinrel,
												 (Path *) pathnode,
												 pathnode->jpath.innerjoinpath->parent->relids,
												 rowidexpr_id);
	}

	/*
	 * See the comments at the end of create_nestloop_path.
	 */
	return turn_volatile_seggen_to_singleqe(root,
											(Path *) pathnode,
											(Node *) (pathnode->jpath.joinrestrictinfo));
}

/*
 * create_nestloop_path
 *	  Creates a pathnode corresponding to a nestloop join between two
 *	  relations.
 *
 * 'joinrel' is the join relation.
 * 'jointype' is the type of join required
 * 'workspace' is the result from initial_cost_nestloop
 * 'extra' contains various information about the join
 * 'outer_path' is the outer path
 * 'inner_path' is the inner path
 * 'restrict_clauses' are the RestrictInfo nodes to apply at the join
 * 'pathkeys' are the path keys of the new join path
 * 'required_outer' is the set of required outer rels
 *
 * Returns the resulting path node.
 */
Path *
create_nestloop_path(PlannerInfo *root,
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
					 Relids required_outer)
{
	NestPath   *pathnode;
	CdbPathLocus join_locus;
	Relids		outer_req_outer = PATH_REQ_OUTER(outer_path);
	bool		outer_must_be_local = !bms_is_empty(outer_req_outer);
	Relids		inner_req_outer = PATH_REQ_OUTER(inner_path);
	bool		inner_must_be_local = !bms_is_empty(inner_req_outer);
	int			rowidexpr_id;

	/* Add motion nodes above subpaths and decide where to join. */
	join_locus = cdbpath_motion_for_join(root,
										 orig_jointype,
										 &outer_path,       /* INOUT */
										 &inner_path,       /* INOUT */
										 &rowidexpr_id,		/* OUT */
										 redistribution_clauses,
										 restrict_clauses,
										 pathkeys,
										 NIL,
										 outer_must_be_local,
#ifdef MATRIXDB_VERSION
										 inner_must_be_local,
										 true,
										 false);
#else /* MATRIXDB_VERSION */
										 inner_must_be_local);
#endif /* MATRIXDB_VERSION */

	if (CdbPathLocus_IsNull(join_locus))
		return NULL;

	/* Outer might not be ordered anymore after motion. */
	if (!outer_path->pathkeys)
		pathkeys = NIL;

	/*
	 * If this join path is parameterized by a parameter above this path, then
	 * this path needs to be rescannable. A NestLoop is rescannable, when both
	 * outer and inner paths rescannable, so make them both rescannable.
	 */
	if (!outer_path->rescannable && !bms_is_empty(required_outer))
	{
		MaterialPath *matouter = create_material_path(root, outer_path->parent, outer_path);

		matouter->cdb_shield_child_from_rescans = true;

		outer_path = (Path *) matouter;
	}

	/*
	 * If outer has at most one row, NJ will make at most one pass over inner.
	 * Else materialize inner rel after motion so NJ can loop over results.
	 */
#ifdef MATRIXDB_VERSION
	if (inner_path->parallel_workers > 0 ||
		(!inner_path->rescannable &&
		(!bms_is_empty(required_outer))))
	{
		if (bms_overlap(inner_req_outer, outer_path->parent->relids) &&
			motion_unmaterial(inner_path, NULL)) {
			return NULL;
		}
#elif
	if (!inner_path->rescannable && !bms_is_empty(required_outer))
	{
#endif /* MATRIXDB_VERSION */

		/*
		 * NLs potentially rescan the inner; if our inner path
		 * isn't rescannable we have to add a materialize node
		 */
		MaterialPath *matinner = create_material_path(root, inner_path->parent, inner_path);

		matinner->cdb_shield_child_from_rescans = true;

		/*
		 * If we have motion on the outer, to avoid a deadlock; we
		 * need to set cdb_strict. In order for materialize to
		 * fully fetch the underlying (required to avoid our
		 * deadlock hazard) we must set cdb_strict!
		 */
		if (inner_path->motionHazard && outer_path->motionHazard)
		{
			matinner->cdb_strict = true;
			matinner->path.motionHazard = false;
		}

		inner_path = (Path *) matinner;
	}

	/*
	 * If the inner path is parameterized by the outer, we must drop any
	 * restrict_clauses that are due to be moved into the inner path.  We have
	 * to do this now, rather than postpone the work till createplan time,
	 * because the restrict_clauses list can affect the size and cost
	 * estimates for this path.
	 */
	if (bms_overlap(inner_req_outer, outer_path->parent->relids))
	{
		Relids		inner_and_outer = bms_union(inner_path->parent->relids,
												inner_req_outer);
		List	   *jclauses = NIL;
		ListCell   *lc;

		foreach(lc, restrict_clauses)
		{
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

			if (!join_clause_is_movable_into(rinfo,
											 inner_path->parent->relids,
											 inner_and_outer))
				jclauses = lappend(jclauses, rinfo);
		}
		restrict_clauses = jclauses;
	}


	pathnode = makeNode(NestPath);
	pathnode->path.pathtype = T_NestLoop;
	pathnode->path.parent = joinrel;
	pathnode->path.pathtarget = joinrel->reltarget;
	pathnode->path.param_info =
		get_joinrel_parampathinfo(root,
								  joinrel,
								  outer_path,
								  inner_path,
								  extra->sjinfo,
								  required_outer,
								  &restrict_clauses);
	pathnode->path.parallel_aware = false;
	pathnode->path.parallel_safe = joinrel->consider_parallel &&
		outer_path->parallel_safe && inner_path->parallel_safe;
	/* This is a foolish way to estimate parallel_workers, but for now... */
#ifdef MATRIXDB_VERSION
	/*
	 * In Matrixdb, let's keep it the same with the join_locus after
	 * the motions are decorated
	 */
	pathnode->path.parallel_workers = join_locus.parallel_workers;
#else
	pathnode->path.parallel_workers = outer_path->parallel_workers;
#endif /* MATRIXDB_VERSION */
	pathnode->path.pathkeys = pathkeys;
	pathnode->jointype = jointype;
	pathnode->inner_unique = extra->inner_unique;
	pathnode->outerjoinpath = outer_path;
	pathnode->innerjoinpath = inner_path;
	pathnode->joinrestrictinfo = restrict_clauses;

	pathnode->path.locus = join_locus;
	pathnode->path.motionHazard = outer_path->motionHazard || inner_path->motionHazard;

	/* we're only as rescannable as our child plans */
	pathnode->path.rescannable = outer_path->rescannable && inner_path->rescannable;

	pathnode->path.sameslice_relids = bms_union(inner_path->sameslice_relids, outer_path->sameslice_relids);

	/*
	 * inner_path & outer_path are possibly modified above. Let's recalculate
	 * the initial cost.
	 */
	initial_cost_nestloop(root, workspace, jointype,
						  outer_path, inner_path,
						  extra);

	final_cost_nestloop(root, pathnode, workspace, extra);

	if (orig_jointype == JOIN_DEDUP_SEMI ||
		orig_jointype == JOIN_DEDUP_SEMI_REVERSE)
	{
		return (Path *) create_unique_rowid_path(root,
												 joinrel,
												 (Path *) pathnode,
												 pathnode->innerjoinpath->parent->relids,
												 rowidexpr_id);
	}

	/*
	 * Greenplum specific behavior:
	 * If we find the join locus is general or segmentgeneral,
	 * we should check the joinqual, if it contains volatile functions
	 * we have to turn the join path to singleQE.
	 *
	 * NB: we do not add this logic in the above create_unique_rowid_path
	 * code block, the reason is:
	 *   create_unique_rowid_path is a technique to implement semi join
	 *   using normal join, it can only happens for sublink query:
	 *   1. if the sublink query contains volatile target list or havingQual
	 *      it cannot be pulled up in pull_up_subquery, so it will be a
	 *      subselect and be handled in the function set_subquery_pathlist
	 *   2. if the sublink query contains volatile functions in joinqual
	 *      or where clause, it will be handled in set_rel_pathlist and
	 *      here.
	 */
	return turn_volatile_seggen_to_singleqe(root,
											(Path *) pathnode,
											(Node *) (pathnode->joinrestrictinfo));
}

static bool
motion_unmaterial(Path *path, void *context)
{
	if (path == NULL)
		return false;

	if (IsA(path, MaterialPath) &&
		IsA(((MaterialPath *)path)->subpath, CdbMotionPath))
		return false;

	if (IsA(path, CdbMotionPath))
		return true;

	return path_tree_walker(path, motion_unmaterial, context, false);
}
