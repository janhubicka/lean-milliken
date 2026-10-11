import Milliken.Applications

/-!
Transitive axiom audit for the unconditional Halpern--Läuchli bridge and
Milliken endpoints.
-/

#print axioms Milliken.StrongTreeSpace.amalgamation_refine
#print axioms Milliken.StrongTreeSpace.isTychonoffClosed
#print axioms Milliken.HalpernLauchli.HalesJewettBridge.strongSubtreeHL
#print axioms Milliken.Chapter6.milliken
#print axioms Milliken.Chapter6.milliken_onBasicNeighborhoods

#print axioms Milliken.Applications.millikenFiniteColouring
#print axioms Milliken.Applications.millikenFixedStemFiniteColouring
#print axioms Milliken.Applications.exists_refinement_realising
#print axioms Milliken.Applications.milliken1979_homogeneous
#print axioms Milliken.Applications.todorcevic62_homogeneous

#print axioms Milliken.Applications.millikenFixedStem1979_homogeneous
#print axioms Milliken.GeneralTree.StrongSubtree.sourceLevel_nonempty
#print axioms Milliken.GeneralTree.StrongSubtree.initialPart_mono
#print axioms Milliken.StrongTreeSpace.comparison_leFin
#print axioms Milliken.StrongTreeSpace.comparison_not_bookLeFin
#print axioms Milliken.StrongTreeSpace.bookLeFin_refl
#print axioms Milliken.StrongTreeSpace.bookLeFin_of_zero
#print axioms Milliken.GeneralTree.bookLeFin_refl
#print axioms Milliken.GeneralTree.bookLeFin_zero_left
#print axioms Milliken.GeneralTree.self_mem_basicNeighborhood

#print axioms Milliken.GeneralTree.StrongSubtree.initialPart_succ
#print axioms Milliken.GeneralTree.StrongSubtree.carrier_eq_iUnion_sourceLevel
#print axioms Milliken.GeneralTree.StrongSubtree.sourceLevel_disjoint
#print axioms Milliken.GeneralTree.FiniteApprox.ext_carrier
#print axioms Milliken.GeneralTree.r_surjective
#print axioms Milliken.GeneralTree.r_zero_eq
#print axioms Milliken.GeneralTree.basicNeighborhood_trans
#print axioms Milliken.GeneralTree.bookLeFin_iff
#print axioms Milliken.GeneralTree.bookLeFin_trans

#print axioms Milliken.GeneralTree.strictMono_eq_of_range_eq
#print axioms Milliken.GeneralTree.StrongSubtree.range_levels_eq_carrier_ranks
#print axioms Milliken.GeneralTree.StrongSubtree.ext_carrier
#print axioms Milliken.GeneralTree.r_separated

#print axioms Milliken.AmbientTree.level_mono
#print axioms Milliken.AmbientTree.level_covBy
#print axioms Milliken.AmbientTree.level_lt
#print axioms Milliken.AmbientTree.eq_of_le_of_level_eq
#print axioms Milliken.GeneralTree.identityStrongSubtree
#print axioms Milliken.GeneralTree.sinfinity_nonempty
#print axioms Milliken.GeneralTree.milliken_zero

#print axioms Milliken.AmbientTree.levelSet_finite
#print axioms Milliken.AmbientTree.levelSet_nonempty
#print axioms Milliken.GeneralTree.StrongSubtree.sourceLevel_finite
#print axioms Milliken.GeneralTree.StrongSubtree.initialPart_finite
#print axioms Milliken.GeneralTree.StrongSubtree.ambientBoundary_finite
#print axioms Milliken.GeneralTree.StrongSubtree.ambientBoundary_nonempty
#print axioms Milliken.GeneralTree.StrongSubtree.boundaryAtStem_finite
#print axioms Milliken.GeneralTree.StrongSubtree.boundaryAtStem_nonempty
#print axioms Milliken.GeneralTree.FiniteApprox.carrier_finite
#print axioms Milliken.GeneralTree.maxLevel_r_succ
#print axioms Milliken.GeneralTree.maxLevel_r_zero

#print axioms Milliken.GeneralTree.StrongVectorSubtree.refines_trans
#print axioms Milliken.GeneralTree.StrongVectorSubtree.ext_coordinate
#print axioms Milliken.GeneralTree.FiniteVectorApprox.ext_carriers
#print axioms Milliken.GeneralTree.vectorApprox_surjective
#print axioms Milliken.GeneralTree.vectorApprox_zero_eq
#print axioms Milliken.GeneralTree.vectorApprox_separated
#print axioms Milliken.Applications.homogeneousVectorHalpernLauchli

#print axioms Milliken.GeneralTree.boundaryEquivFin_mem
#print axioms Milliken.GeneralTree.childIndex_nonempty
#print axioms Milliken.Applications.finiteIndexedStrongSubtreeHL

#print axioms Milliken.GeneralTree.StrongSubtree.initialPart_eq_diff
#print axioms Milliken.GeneralTree.r_prev_eq_of_succ
#print axioms Milliken.GeneralTree.r_coherent_le
#print axioms Milliken.GeneralTree.vectorApprox_coherent

#print axioms Milliken.GeneralTree.generalApproximationSystem
#print axioms Milliken.GeneralTree.generalNeighborhood_eq
#print axioms Milliken.GeneralTree.identityVectorStrongSubtree
#print axioms Milliken.GeneralTree.vectorApproximationSystem
#print axioms Milliken.GeneralTree.vectorNeighborhood_eq

#print axioms Milliken.GeneralTree.boundedApprox_finite
#print axioms Milliken.GeneralTree.bookLeFin_fixedHeight_lowerFinite

#print axioms Milliken.GeneralTree.height_le_ncard_of_subset
#print axioms Milliken.GeneralTree.bookLeFin_lowerFinite

#print axioms Milliken.GeneralTree.StrongSubtree.selectedLevel_of_refines
#print axioms Milliken.GeneralTree.StrongSubtree.mem_initialPart_of_level_le
#print axioms Milliken.GeneralTree.exists_bookLeFin_r_of_refines
#print axioms Milliken.GeneralTree.refines_of_forall_bookLeFin_r
#print axioms Milliken.GeneralTree.refines_iff_forall_bookLeFin_r

#print axioms Milliken.GeneralTree.bookLeFin_prefix_compatible
#print axioms Milliken.GeneralTree.generalBookFinitization

#print axioms Milliken.GeneralTree.StrongSubtree.sourceLevel_zero_eq_singleton
#print axioms Milliken.GeneralTree.StrongSubtree.exists_sourceLevel_ancestor
#print axioms Milliken.GeneralTree.StrongSubtree.exists_frontier_ancestor

#print axioms Milliken.GeneralTree.StrongSubtree.existsUnique_sourceLevel_ancestor
#print axioms Milliken.GeneralTree.StrongSubtree.existsUnique_frontier_ancestor
#print axioms Milliken.GeneralTree.maxLevel_nonempty_succ
#print axioms Milliken.GeneralTree.bookLeFin_succ_lastLevel
#print axioms Milliken.GeneralTree.bookDepth_zero_of_empty
#print axioms Milliken.GeneralTree.bookDepth_succ_lastLevel
#print axioms Milliken.GeneralTree.neighborhood_nonempty_zero

#print axioms Milliken.GeneralTree.StrongSubtree.spliceLevels_before
#print axioms Milliken.GeneralTree.StrongSubtree.spliceLevels_at
#print axioms Milliken.GeneralTree.StrongSubtree.spliceLevels_strictMono
#print axioms Milliken.GeneralTree.StrongSubtree.initialPart_level_lt
#print axioms Milliken.GeneralTree.StrongSubtree.spliceTail_level_ge
#print axioms Milliken.GeneralTree.StrongSubtree.spliceTail_at_frontier
#print axioms Milliken.GeneralTree.StrongSubtree.spliceCarrier_level_before
#print axioms Milliken.GeneralTree.StrongSubtree.spliceCarrier_level_at
#print axioms Milliken.GeneralTree.StrongSubtree.disjoint_initialPart_spliceTail

#print axioms Milliken.GeneralTree.StrongSubtree.spliceLevels_ge
#print axioms Milliken.GeneralTree.StrongSubtree.spliceTail_upward_in_T
#print axioms Milliken.GeneralTree.StrongSubtree.spliceCarrier_level_tail
#print axioms Milliken.GeneralTree.StrongSubtree.spliceCarrier_levels
#print axioms Milliken.GeneralTree.StrongSubtree.spliceCarrier_root_mem
#print axioms Milliken.GeneralTree.StrongSubtree.spliceCarrier_root_below
#print axioms Milliken.GeneralTree.StrongSubtree.spliceCarrier_tail_level_mem_T

#print axioms Milliken.GeneralTree.StrongSubtree.levels_refinementIndex
#print axioms Milliken.GeneralTree.StrongSubtree.refinementIndex_strictMono
#print axioms Milliken.GeneralTree.StrongSubtree.sourceLevel_subset_refinementIndex
#print axioms Milliken.GeneralTree.StrongSubtree.refinementIndex_eq_of_sourceLevel_subset
#print axioms Milliken.GeneralTree.StrongSubtree.le_refinementIndex

#print axioms Milliken.AmbientTree.le_of_common_descendant_of_level_le
#print axioms Milliken.GeneralTree.StrongSubtree.spliceTail_ancestor
#print axioms Milliken.GeneralTree.StrongSubtree.splice_source_before
#print axioms Milliken.GeneralTree.StrongSubtree.splice_source_at
#print axioms Milliken.GeneralTree.StrongSubtree.splice_source_after

#print axioms Milliken.GeneralTree.StrongSubtree.exists_sourceLevel_descendant
#print axioms Milliken.GeneralTree.StrongSubtree.exists_sourceLevel_descendant_in_childCone
#print axioms Milliken.GeneralTree.StrongSubtree.longConeRepresentative_spec
#print axioms Milliken.GeneralTree.StrongSubtree.immediateChildren_eq_of_common_descendant
#print axioms Milliken.GeneralTree.StrongSubtree.longConeRepresentative_injective

#print axioms Milliken.GeneralTree.StrongSubtree.thinningLevelData
#print axioms Milliken.GeneralTree.StrongSubtree.thinningLevel_subset_sourceLevel
#print axioms Milliken.GeneralTree.StrongSubtree.thinningLevel_zero
#print axioms Milliken.GeneralTree.StrongSubtree.thinningLevel_succ_iff
#print axioms Milliken.GeneralTree.StrongSubtree.thinningCarrier_levels

#print axioms Milliken.GeneralTree.StrongSubtree.thinningLevel_nonempty
#print axioms Milliken.GeneralTree.StrongSubtree.thinningLevel_root_below
#print axioms Milliken.GeneralTree.StrongSubtree.thinningLevel_predecessor_exists
#print axioms Milliken.GeneralTree.StrongSubtree.thinningCarrier_subset
#print axioms Milliken.GeneralTree.StrongSubtree.thinningCarrier_root_mem
#print axioms Milliken.GeneralTree.StrongSubtree.thinningCarrier_root_below
#print axioms Milliken.GeneralTree.StrongSubtree.thinningCarrier_at_level
#print axioms Milliken.GeneralTree.StrongSubtree.thinningCarrier_predecessor_exists

#print axioms Milliken.GeneralTree.StrongSubtree.spliceCarrier_predecessor_exists
#print axioms Milliken.GeneralTree.StrongSubtree.spliceCarrier_successor_unique
#print axioms Milliken.GeneralTree.StrongSubtree.spliceStrong
#print axioms Milliken.GeneralTree.StrongSubtree.spliceStrong_refines

#print axioms Milliken.AmbientTree.eq_of_common_descendant_of_level_eq
#print axioms Milliken.GeneralTree.StrongSubtree.thinningLevel_successor_unique
#print axioms Milliken.GeneralTree.StrongSubtree.thinStrong
#print axioms Milliken.GeneralTree.StrongSubtree.thinStrong_refines
#print axioms Milliken.GeneralTree.StrongSubtree.thinStrong_sourceLevel

#print axioms Milliken.GeneralTree.StrongSubtree.spliceStrong_sourceLevel_before
#print axioms Milliken.GeneralTree.StrongSubtree.spliceStrong_sourceLevel_at
#print axioms Milliken.GeneralTree.StrongSubtree.spliceStrong_initialPart
#print axioms Milliken.GeneralTree.StrongSubtree.spliceStrong_approx_succ
#print axioms Milliken.GeneralTree.generalAmalgamation_nonempty

#print axioms Milliken.GeneralTree.selectedLastLevel_eq_of_r_succ_eq
#print axioms Milliken.GeneralTree.refines_of_protected_tail
#print axioms Milliken.GeneralTree.basicNeighborhood_subset_of_protected_tail

#print axioms Milliken.AmbientTree.exists_child_le_of_lt
#print axioms Milliken.AmbientTree.children_eq_of_common_descendant

#print axioms Milliken.AmbientTree.upwardCones_upwards
#print axioms Milliken.AmbientTree.upwardCones_union
#print axioms Milliken.AmbientTree.upwardCones_disjoint_of_same_rank
#print axioms Milliken.GeneralTree.StrongSubtree.frontier_used_unused_disjoint
#print axioms Milliken.GeneralTree.StrongSubtree.frontier_used_unused_union
#print axioms Milliken.GeneralTree.StrongSubtree.carrier_mem_frontier_cones_of_level_ge
#print axioms Milliken.GeneralTree.StrongSubtree.carrier_used_or_unused_frontier

#print axioms Milliken.GeneralTree.StrongSubtree.frontier_levels_eq_of_subset
#print axioms Milliken.GeneralTree.StrongSubtree.mixedCarrier_subset_union
#print axioms Milliken.GeneralTree.StrongSubtree.mixedCarrier_level_before
#print axioms Milliken.GeneralTree.StrongSubtree.mixedCarrier_level_at
#print axioms Milliken.GeneralTree.StrongSubtree.mixedCarrier_used_sector_in_X

#print axioms Milliken.GeneralTree.StrongSubtree.mixedCarrier_unused_sector_in_D

#print axioms Milliken.GeneralTree.StrongSubtree.mixedCarrier_root_mem
#print axioms Milliken.GeneralTree.StrongSubtree.mixedCarrier_root_below
#print axioms Milliken.GeneralTree.StrongSubtree.mixedCarrier_levels
#print axioms Milliken.GeneralTree.StrongSubtree.mixedCarrier_subset_of_common_refinement

#print axioms Milliken.GeneralTree.StrongSubtree.mixedCarrier_predecessor_exists

#print axioms Milliken.GeneralTree.StrongSubtree.mixedCarrier_level_le
#print axioms Milliken.GeneralTree.StrongSubtree.mixedCarrier_successor_unique

#print axioms Milliken.GeneralTree.StrongSubtree.mixedStrong
#print axioms Milliken.GeneralTree.StrongSubtree.mixedStrong_sourceLevel_before
#print axioms Milliken.GeneralTree.StrongSubtree.mixedStrong_sourceLevel_at
#print axioms Milliken.GeneralTree.StrongSubtree.mixedStrong_initialPart
#print axioms Milliken.GeneralTree.StrongSubtree.mixedStrong_approx_succ
#print axioms Milliken.GeneralTree.StrongSubtree.mixedStrong_refines_common
#print axioms Milliken.GeneralTree.StrongSubtree.mixedStrong_used_sector_in_X
