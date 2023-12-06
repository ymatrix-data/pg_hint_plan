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