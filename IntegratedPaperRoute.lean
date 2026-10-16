module

public import Batteries.Tactic.Alias
public import LeanResearch.RepulsiveCoulomb.CoulombCenterManuscript
public import LeanResearch.RepulsiveCoulomb.CoulombClosability
public import LeanResearch.RepulsiveCoulomb.CoulombClosedForm
public import LeanResearch.RepulsiveCoulomb.CoulombConstantDomain
public import LeanResearch.RepulsiveCoulomb.CoulombExhaustionCompact
public import LeanResearch.RepulsiveCoulomb.CoulombExhaustionGeometry
public import LeanResearch.RepulsiveCoulomb.CoulombGlobalVariationalCapacity
public import LeanResearch.RepulsiveCoulomb.DbarBranchPotentialMixedWirtinger
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCanonicalSplitting
public import LeanResearch.RepulsiveCoulomb.LabeledCoulombNormalization
public import LeanResearch.RepulsiveCoulomb.PaperRoute.AllParameterDiskEntropy
public import LeanResearch.RepulsiveCoulomb.PaperRoute.AnalyticLabeledPoincare
public import LeanResearch.RepulsiveCoulomb.PaperRoute.AtomicFormMoment
public import LeanResearch.RepulsiveCoulomb.PaperRoute.AtomicMaximalWeakForce
public import LeanResearch.RepulsiveCoulomb.PaperRoute.AtomicScoreUncertainty
public import LeanResearch.RepulsiveCoulomb.PaperRoute.CollisionPotentialLabeledPoincare
public import LeanResearch.RepulsiveCoulomb.PaperRoute.CompactDiskReferenceLabeledLSI
public import LeanResearch.RepulsiveCoulomb.PaperRoute.CompactResolventLabeledPoincare
public import LeanResearch.RepulsiveCoulomb.PaperRoute.DGFixedCoupling
public import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianCoreGlobalSPI
public import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianDiskHalfMass
public import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianFormSPI
public import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianGlobalPoincare
public import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianSPIWang
public import LeanResearch.RepulsiveCoulomb.PaperRoute.GenericDoublingSobolev
public import LeanResearch.RepulsiveCoulomb.PaperRoute.GibbsProductPower
public import LeanResearch.RepulsiveCoulomb.PaperRoute.GinibreSymmetricSharpness
public import LeanResearch.RepulsiveCoulomb.PaperRoute.LabeledEntropyFromExplicitMoments
public import LeanResearch.RepulsiveCoulomb.PaperRoute.LabeledLSIFromReferenceMoments
public import LeanResearch.RepulsiveCoulomb.PaperRoute.LipschitzMollification
public import LeanResearch.RepulsiveCoulomb.PaperRoute.LipschitzSobolevClosure
public import LeanResearch.RepulsiveCoulomb.PaperRoute.NormalizedTranspositionLabeledPoincare
public import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalCenterOfMass
public import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalCollisionCapacity
public import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalGaussianLocalGeometry
public import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalGaussianWeightedRoute
public import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalInputLabeledLSI
public import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalLipschitzSobolev
public import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalOptimalLSIRates
public import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalPointAdmissibility
public import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalPointGeometry
public import LeanResearch.RepulsiveCoulomb.PaperRoute.PointDistributionalCurvature
public import LeanResearch.RepulsiveCoulomb.PaperRoute.PositiveLogGibbsIntegrability
public import LeanResearch.RepulsiveCoulomb.PaperRoute.ProductPowerConcavity
public import LeanResearch.RepulsiveCoulomb.PaperRoute.ReferencePartitionBounds
public import LeanResearch.RepulsiveCoulomb.PaperRoute.ReferencePolynomialIntegrability
public import LeanResearch.RepulsiveCoulomb.PaperRoute.ReferenceSpatialPartition
public import LeanResearch.RepulsiveCoulomb.PaperRoute.RelativeLabeledPoincare
public import LeanResearch.RepulsiveCoulomb.PaperRoute.ResolventLabeledPoincare
public import LeanResearch.RepulsiveCoulomb.PaperRoute.SpatialReferenceLabeledLSI
public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalDiskReferenceBounds
public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalOriginalDerivativeTails
public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalOriginalReference
public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalOriginalWeakRegularity
public import LeanResearch.RepulsiveCoulomb.PlanarLadyzhenskaya
public import LeanResearch.RepulsiveCoulomb.PointConstantDomain
public import LeanResearch.RepulsiveCoulomb.PointGroundStateEnergy
public import LeanResearch.RepulsiveCoulomb.UnitDiskNormalization
public import LeanResearch.RepulsiveCoulomb.UnitDiskUniformTails

@[expose] public section

noncomputable section
namespace IntegratedMappedClaims

alias claim_01_01 := RepulsiveCoulomb.PaperRoute.paper_full_labeled_lsi_original
#check @claim_01_01
#print axioms claim_01_01
alias claim_01_02 := RepulsiveCoulomb.PaperRoute.paper_uniform_labeled_lsi_original
#check @claim_01_02
#print axioms claim_01_02
alias claim_01_03 := RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate_pos
#check @claim_01_03
#print axioms claim_01_03
alias claim_01_04 := RepulsiveCoulomb.PaperRoute.paperOriginalCompactLabeledRate_pos
#check @claim_01_04
#print axioms claim_01_04
alias claim_01_05 := RepulsiveCoulomb.PaperRoute.paper_original_particle_optimal_inf_pos
#check @claim_01_05
#print axioms claim_01_05
alias claim_01_06 := RepulsiveCoulomb.PaperRoute.paper_original_compact_optimal_double_inf_lower
#check @claim_01_06
#print axioms claim_01_06
alias claim_01_07 := RepulsiveCoulomb.PaperRoute.paper_original_compact_optimal_real_double_inf_lower
#check @claim_01_07
#print axioms claim_01_07
alias claim_01_08 := RepulsiveCoulomb.PaperRoute.paper_original_compact_optimal_double_inf_pos
#check @claim_01_08
#print axioms claim_01_08
alias claim_02_01 := RepulsiveCoulomb.PaperRoute.original_weighted_full_domain
#check @claim_02_01
#print axioms claim_02_01
alias claim_02_02 := RepulsiveCoulomb.PaperRoute.paper_weighted_named_inequalities
#check @claim_02_02
#print axioms claim_02_02
alias claim_02_03 := RepulsiveCoulomb.PaperRoute.paperCwt_scaling
#check @claim_02_03
#print axioms claim_02_03
alias claim_02_04 := RepulsiveCoulomb.PaperRoute.paperRhoWt_scaling
#check @claim_02_04
#print axioms claim_02_04
alias claim_03_01 := RepulsiveCoulomb.coulombWeight_integrable
#check @claim_03_01
#print axioms claim_03_01
alias claim_03_02 := RepulsiveCoulomb.coulombPartition_lt_top
#check @claim_03_02
#print axioms claim_03_02
alias claim_03_03 := RepulsiveCoulomb.coulombPartition_pos
#check @claim_03_03
#print axioms claim_03_03
alias claim_03_04 := RepulsiveCoulomb.coulombMeasure_isProbability
#check @claim_03_04
#print axioms claim_03_04
alias claim_03_05 := RepulsiveCoulomb.coulombCoreGraph_zero_gradient
#check @claim_03_05
#print axioms claim_03_05
alias claim_03_06 := RepulsiveCoulomb.coulombCoreGraph_zero_of_value_zero
#check @claim_03_06
#print axioms claim_03_06
alias claim_03_07 := RepulsiveCoulomb.coulombFormValueL_injective
#check @claim_03_07
#print axioms claim_03_07
alias claim_03_08 := RepulsiveCoulomb.coulombFormEnergy_eq_integral
#check @claim_03_08
#print axioms claim_03_08
alias claim_04_01 := RepulsiveCoulomb.coulombCollisionSet_capacity_zero
#check @claim_04_01
#print axioms claim_04_01
alias claim_04_02 := RepulsiveCoulomb.coulomb_collision_capacity_and_common_core
#check @claim_04_02
#print axioms claim_04_02
alias claim_04_03 := RepulsiveCoulomb.PaperRoute.paper_original_collision_capacity
#check @claim_04_03
#print axioms claim_04_03
alias claim_04_04 := RepulsiveCoulomb.PaperRoute.paper_original_collision_capacity_and_common_core
#check @claim_04_04
#print axioms claim_04_04
alias claim_04_05 := RepulsiveCoulomb.PaperRoute.paper_original_capacity_open_neighborhood
#check @claim_04_05
#print axioms claim_04_05
alias claim_04_06 := RepulsiveCoulomb.PaperRoute.paper_original_capacity_physical_cost
#check @claim_04_06
#print axioms claim_04_06
alias claim_05_01 := RepulsiveCoulomb.coulombConstantJet_mem_closedCore
#check @claim_05_01
#print axioms claim_05_01
alias claim_05_02 := RepulsiveCoulomb.coulombConstantForm_value
#check @claim_05_02
#print axioms claim_05_02
alias claim_05_03 := RepulsiveCoulomb.coulombConstantForm_energy
#check @claim_05_03
#print axioms claim_05_03
alias claim_05_04 := RepulsiveCoulomb.pointConstantJet_mem_closedCore
#check @claim_05_04
#print axioms claim_05_04
alias claim_05_05 := RepulsiveCoulomb.pointConstantForm_value
#check @claim_05_05
#print axioms claim_05_05
alias claim_05_06 := RepulsiveCoulomb.pointConstantForm_energy
#check @claim_05_06
#print axioms claim_05_06
alias claim_06_01 := RepulsiveCoulomb.coulomb_center_mass_manuscript
#check @claim_06_01
#print axioms claim_06_01
alias claim_06_02 := RepulsiveCoulomb.coulomb_center_mass_optimal_lsi_rate_all_N
#check @claim_06_02
#print axioms claim_06_02
alias claim_06_03 := RepulsiveCoulomb.PaperRoute.paper_original_center_mass
#check @claim_06_03
#print axioms claim_06_03
alias claim_06_04 := RepulsiveCoulomb.PaperRoute.paper_original_center_mass_optimal_rate
#check @claim_06_04
#print axioms claim_06_04
alias claim_06_05 := RepulsiveCoulomb.PaperRoute.paper_original_helmert_center
#check @claim_06_05
#print axioms claim_06_05
alias claim_06_06 := RepulsiveCoulomb.PaperRoute.paper_original_helmert_relative
#check @claim_06_06
#print axioms claim_06_06
alias claim_06_07 := RepulsiveCoulomb.PaperRoute.paper_original_helmert_unitary
#check @claim_06_07
#print axioms claim_06_07
alias claim_07_01 := RepulsiveCoulomb.PaperRoute.original_point_localGeometry
#check @claim_07_01
#print axioms claim_07_01
alias claim_07_02 := RepulsiveCoulomb.PaperRoute.original_point_physical_weak_one_two
#check @claim_07_02
#print axioms claim_07_02
alias claim_07_03 := RepulsiveCoulomb.PaperRoute.original_point_doubling_and_locallyLipschitz_PI
#check @claim_07_03
#print axioms claim_07_03
alias claim_07_04 := RepulsiveCoulomb.PaperRoute.strong_sobolev_squared_norm_of_dilation_two
#check @claim_07_04
#print axioms claim_07_04
alias claim_07_05 := RepulsiveCoulomb.PaperRoute.PointCurvature.pointConformalDensity_distributional_curvature
#check @claim_07_05
#print axioms claim_07_05
alias claim_07_06 := RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_c1_center
#check @claim_07_06
#print axioms claim_07_06
alias claim_07_07 := RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_closedBall
#check @claim_07_07
#print axioms claim_07_07
alias claim_07_08 := RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_locallyLipschitz
#check @claim_07_08
#print axioms claim_07_08
alias claim_07_09 := RepulsiveCoulomb.PaperRoute.original_raw_local_sobolev_locallyLipschitz
#check @claim_07_09
#print axioms claim_07_09
alias claim_07_10 := RepulsiveCoulomb.PaperRoute.lipschitzMollify_hasFDerivAt
#check @claim_07_10
#print axioms claim_07_10
alias claim_07_11 := RepulsiveCoulomb.PaperRoute.lipschitzMollify_fderiv_ae_tendsto
#check @claim_07_11
#print axioms claim_07_11
alias claim_07_12 := RepulsiveCoulomb.PaperRoute.lipschitzMollify_centered_moment_tendsto
#check @claim_07_12
#print axioms claim_07_12
alias claim_07_13 := RepulsiveCoulomb.PaperRoute.lipschitzMollify_energy_tendsto
#check @claim_07_13
#print axioms claim_07_13
alias claim_07_14 := RepulsiveCoulomb.PaperRoute.strong_sobolev_on_balls_of_lipschitzOn
#check @claim_07_14
#print axioms claim_07_14
alias claim_08_01 := RepulsiveCoulomb.PaperRoute.original_gaussian_local_geometry
#check @claim_08_01
#print axioms claim_08_01
alias claim_08_02 := RepulsiveCoulomb.PaperRoute.original_gaussian_strong_sobolev_closedBall
#check @claim_08_02
#print axioms claim_08_02
alias claim_08_03 := RepulsiveCoulomb.PaperRoute.original_gaussian_local_sobolev_locallyLipschitz
#check @claim_08_03
#print axioms claim_08_03
alias claim_09_01 := RepulsiveCoulomb.pointPartition_unitDisk_lower_uniform
#check @claim_09_01
#print axioms claim_09_01
alias claim_09_02 := RepulsiveCoulomb.pointPartition_integral_unitDisk_lower
#check @claim_09_02
#print axioms claim_09_02
alias claim_09_03 := RepulsiveCoulomb.pointMeasure_disk_tail_le
#check @claim_09_03
#print axioms claim_09_03
alias claim_09_04 := RepulsiveCoulomb.pointMeasure_disk_tail_real_le
#check @claim_09_04
#print axioms claim_09_04
alias claim_09_05 := RepulsiveCoulomb.PaperRoute.disk_half_mass_ball
#check @claim_09_05
#print axioms claim_09_05
alias claim_10_01 := RepulsiveCoulomb.PaperRoute.pointLogForce_weak_l2_atomic_maximal
#check @claim_10_01
#print axioms claim_10_01
alias claim_10_02 := RepulsiveCoulomb.PaperRoute.pointLogForce_weak_l2_atomic_maximal_of_total_le
#check @claim_10_02
#print axioms claim_10_02
alias claim_11_01 := RepulsiveCoulomb.planar_ladyzhenskaya
#check @claim_11_01
#print axioms claim_11_01
alias claim_12_01 := RepulsiveCoulomb.PaperRoute.atomic_pointScore_uncertainty
#check @claim_12_01
#print axioms claim_12_01
alias claim_13_01 := RepulsiveCoulomb.PaperRoute.atomic_pointCore_weighted_moment_bound
#check @claim_13_01
#print axioms claim_13_01
alias claim_13_02 := RepulsiveCoulomb.PaperRoute.atomic_pointForm_weighted_moment_bound
#check @claim_13_02
#print axioms claim_13_02
alias claim_13_03 := RepulsiveCoulomb.PaperRoute.atomic_pointForm_uniform_quadratic_moment
#check @claim_13_03
#print axioms claim_13_03
alias claim_13_04 := RepulsiveCoulomb.pointGroundState_energy_identity
#check @claim_13_04
#print axioms claim_13_04
alias claim_14_01 := RepulsiveCoulomb.PaperRoute.core_poincare_of_raw_sobolev
#check @claim_14_01
#print axioms claim_14_01
alias claim_14_02 := RepulsiveCoulomb.PaperRoute.form_poincare_of_raw_sobolev
#check @claim_14_02
#print axioms claim_14_02
alias claim_14_03 := RepulsiveCoulomb.PaperRoute.original_weighted_full_domain
#check @claim_14_03
#print axioms claim_14_03
alias claim_15_01 := RepulsiveCoulomb.PaperRoute.core_global_superPoincare_small
#check @claim_15_01
#print axioms claim_15_01
alias claim_15_02 := RepulsiveCoulomb.PaperRoute.core_global_superPoincare
#check @claim_15_02
#print axioms claim_15_02
alias claim_15_03 := RepulsiveCoulomb.PaperRoute.form_global_superPoincare
#check @claim_15_03
#print axioms claim_15_03
alias claim_15_04 := RepulsiveCoulomb.PaperRoute.core_defective_lsi_of_gaussian_spi
#check @claim_15_04
#print axioms claim_15_04
alias claim_16_01 := RepulsiveCoulomb.PaperRoute.paper_full_labeled_poincare_via_resolvent
#check @claim_16_01
#print axioms claim_16_01
alias claim_16_02 := RepulsiveCoulomb.PaperRoute.paper_full_labeled_poincare_uniform_via_resolvent
#check @claim_16_02
#print axioms claim_16_02
alias claim_17_01 := RepulsiveCoulomb.coulombPotential_mixedWirtinger_entry
#check @claim_17_01
#print axioms claim_17_01
alias claim_17_02 := RepulsiveCoulomb.coulombPotential_mixedWirtinger_contraction
#check @claim_17_02
#print axioms claim_17_02
alias claim_17_03 := RepulsiveCoulomb.coulombExhaustion_line_laplacian_pos
#check @claim_17_03
#print axioms claim_17_03
alias claim_17_04 := RepulsiveCoulomb.coulombExhaustion_strict_sublevel_relativelyCompact
#check @claim_17_04
#print axioms claim_17_04
alias claim_18_01 := RepulsiveCoulomb.PaperRoute.paper_dbar_graph_distance
#check @claim_18_01
#print axioms claim_18_01
alias claim_18_02 := RepulsiveCoulomb.PaperRoute.paper_dbar_core_distance
#check @claim_18_02
#print axioms claim_18_02
alias claim_18_03 := RepulsiveCoulomb.PaperRoute.paper_dbar_kernel_holomorphic
#check @claim_18_03
#print axioms claim_18_03
alias claim_18_04 := RepulsiveCoulomb.PaperRoute.paper_real_dbar_physical_energy
#check @claim_18_04
#print axioms claim_18_04
alias claim_19_01 := RepulsiveCoulomb.PaperRoute.paper_symmetric_holomorphic_removal
#check @claim_19_01
#print axioms claim_19_01
alias claim_20_01 := RepulsiveCoulomb.PaperRoute.paper_common_phase_identity
#check @claim_20_01
#print axioms claim_20_01
alias claim_21_01 := RepulsiveCoulomb.PaperRoute.paper_symmetric_poincare_small_exponent
#check @claim_21_01
#print axioms claim_21_01
alias claim_21_02 := RepulsiveCoulomb.PaperRoute.paper_symmetric_poincare_via_resolvent
#check @claim_21_02
#print axioms claim_21_02
alias claim_22_01 := RepulsiveCoulomb.PaperRoute.paper_symmetric_poincare_small_exponent
#check @claim_22_01
#print axioms claim_22_01
alias claim_22_02 := RepulsiveCoulomb.PaperRoute.paper_center_real_form_witness
#check @claim_22_02
#print axioms claim_22_02
alias claim_22_03 := RepulsiveCoulomb.PaperRoute.paper_center_imaginary_form_witness
#check @claim_22_03
#print axioms claim_22_03
alias claim_22_04 := RepulsiveCoulomb.PaperRoute.paper_ginibre_symmetric_poincare_sharp_all_N
#check @claim_22_04
#print axioms claim_22_04
alias claim_22_05 := RepulsiveCoulomb.PaperRoute.paper_ginibre_center_equality_witnesses
#check @claim_22_05
#print axioms claim_22_05
alias claim_23_01 := RepulsiveCoulomb.PaperRoute.paper_fixed_particle_form_compact
#check @claim_23_01
#print axioms claim_23_01
alias claim_23_02 := RepulsiveCoulomb.PaperRoute.paper_fixed_particle_resolvent_compact
#check @claim_23_02
#print axioms claim_23_02
alias claim_23_03 := RepulsiveCoulomb.PaperRoute.paper_fixed_particle_operator_selfAdjoint
#check @claim_23_03
#print axioms claim_23_03
alias claim_23_04 := RepulsiveCoulomb.PaperRoute.paper_fixed_particle_kernel_constants
#check @claim_23_04
#print axioms claim_23_04
alias claim_23_05 := RepulsiveCoulomb.PaperRoute.paper_fixed_particle_compact_temperature
#check @claim_23_05
#print axioms claim_23_05
alias claim_23_06 := RepulsiveCoulomb.PaperRoute.paper_resolvent_form_residual
#check @claim_23_06
#print axioms claim_23_06
alias claim_23_07 := RepulsiveCoulomb.PaperRoute.paper_fixed_particle_poincare_via_resolvent
#check @claim_23_07
#print axioms claim_23_07
alias claim_23_08 := RepulsiveCoulomb.PaperRoute.paper_coulomb_potential_distribution
#check @claim_23_08
#print axioms claim_23_08
alias claim_24_01 := RepulsiveCoulomb.PaperRoute.paper_relative_full
#check @claim_24_01
#print axioms claim_24_01
alias claim_24_02 := RepulsiveCoulomb.PaperRoute.paper_relative_core
#check @claim_24_02
#print axioms claim_24_02
alias claim_25_01 := RepulsiveCoulomb.PaperRoute.paper_relative_form_swap
#check @claim_25_01
#print axioms claim_25_01
alias claim_25_02 := RepulsiveCoulomb.PaperRoute.paper_transposition_core
#check @claim_25_02
#print axioms claim_25_02
alias claim_26_01 := RepulsiveCoulomb.PaperRoute.paper_random_transposition_gap
#check @claim_26_01
#print axioms claim_26_01
alias claim_26_02 := RepulsiveCoulomb.PaperRoute.paper_complete_graph_relative_gradient
#check @claim_26_02
#print axioms claim_26_02
alias claim_26_03 := RepulsiveCoulomb.PaperRoute.paperTranspositionKernel_row_sum
#check @claim_26_03
#print axioms claim_26_03
alias claim_26_04 := RepulsiveCoulomb.PaperRoute.paperTranspositionKernel_identity
#check @claim_26_04
#print axioms claim_26_04
alias claim_26_05 := RepulsiveCoulomb.PaperRoute.paperTranspositionKernel_swap
#check @claim_26_05
#print axioms claim_26_05
alias claim_26_06 := RepulsiveCoulomb.PaperRoute.paperUniformTransposition_gap_exact
#check @claim_26_06
#print axioms claim_26_06
alias claim_27_01 := RepulsiveCoulomb.PaperRoute.paper_label_fluctuation
#check @claim_27_01
#print axioms claim_27_01
alias claim_27_02 := RepulsiveCoulomb.PaperRoute.paper_variance_reduction
#check @claim_27_02
#print axioms claim_27_02
alias claim_28_01 := RepulsiveCoulomb.PaperRoute.thermal_physicalReference_from_minimizer
#check @claim_28_01
#print axioms claim_28_01
alias claim_28_02 := RepulsiveCoulomb.PaperRoute.thermalConstructedReference_nonempty
#check @claim_28_02
#print axioms claim_28_02
alias claim_28_03 := RepulsiveCoulomb.PaperRoute.thermalConstructedReference_measure_unique
#check @claim_28_03
#print axioms claim_28_03
alias claim_28_04 := RepulsiveCoulomb.PaperRoute.thermalConstructedReference_multiIndex_tail
#check @claim_28_04
#print axioms claim_28_04
alias claim_28_05 := RepulsiveCoulomb.PaperRoute.paper_reference_EL_normalizer_disk
#check @claim_28_05
#print axioms claim_28_05
alias claim_28_06 := RepulsiveCoulomb.PaperRoute.paper_reference_compact_bounds_disk
#check @claim_28_06
#print axioms claim_28_06
alias claim_29_01 := RepulsiveCoulomb.equilibriumReference_coulombMeasure_eq_tilted
#check @claim_29_01
#print axioms claim_29_01
alias claim_29_02 := RepulsiveCoulomb.equilibriumReferencePartition_canonical_eq
#check @claim_29_02
#print axioms claim_29_02
alias claim_29_03 := RepulsiveCoulomb.PaperRoute.paper_reference_spatial_bridge
#check @claim_29_03
#print axioms claim_29_03
alias claim_29_04 := RepulsiveCoulomb.PaperRoute.paper_reference_spatial_energy_ae
#check @claim_29_04
#print axioms claim_29_04
alias claim_29_05 := RepulsiveCoulomb.PaperRoute.paper_reference_spatial_partition_eq
#check @claim_29_05
#print axioms claim_29_05
alias claim_30_01 := RepulsiveCoulomb.PaperRoute.paper_dg_fixed_coupling
#check @claim_30_01
#print axioms claim_30_01
alias claim_30_02 := RepulsiveCoulomb.PaperRoute.paper_reference_partition_holder
#check @claim_30_02
#print axioms claim_30_02
alias claim_30_03 := RepulsiveCoulomb.PaperRoute.paper_reference_partition_uniform
#check @claim_30_03
#print axioms claim_30_03
alias claim_30_04 := RepulsiveCoulomb.PaperRoute.paper_spatial_partition_uniform
#check @claim_30_04
#print axioms claim_30_04
alias claim_30_05 := RepulsiveCoulomb.PaperRoute.paper_reference_partition_lower_polynomial
#check @claim_30_05
#print axioms claim_30_05
alias claim_31_01 := RepulsiveCoulomb.PaperRoute.paper_entropy_factorization_disk
#check @claim_31_01
#print axioms claim_31_01
alias claim_31_02 := RepulsiveCoulomb.PaperRoute.paper_finite_defect_nonneg_disk
#check @claim_31_02
#print axioms claim_31_02
alias claim_31_03 := RepulsiveCoulomb.PaperRoute.paper_uniform_defectAt_compact_disk
#check @claim_31_03
#print axioms claim_31_03
alias claim_31_04 := RepulsiveCoulomb.PaperRoute.paper_uniform_defectAt_finite_disk
#check @claim_31_04
#print axioms claim_31_04
alias claim_31_05 := RepulsiveCoulomb.PaperRoute.paper_gibbs_defect_moment_product_power
#check @claim_31_05
#print axioms claim_31_05
alias claim_31_06 := RepulsiveCoulomb.PaperRoute.paper_exp_integral_inverse_power_concavity
#check @claim_31_06
#print axioms claim_31_06
alias claim_31_07 := RepulsiveCoulomb.PaperRoute.paper_thermal_B_gibbs_integrable_positive_log
#check @claim_31_07
#print axioms claim_31_07
alias claim_32_01 := RepulsiveCoulomb.PaperRoute.paper_full_defective_of_reference_bounds_of_exp_integrable
#check @claim_32_01
#print axioms claim_32_01
alias claim_32_02 := RepulsiveCoulomb.PaperRoute.paper_full_defective_compact_via_disk_reference_family
#check @claim_32_02
#print axioms claim_32_02
alias claim_32_03 := RepulsiveCoulomb.PaperRoute.paper_full_labeled_lsi_original
#check @claim_32_03
#print axioms claim_32_03
alias claim_33_01 := RepulsiveCoulomb.PaperRoute.paperLabeledRateFromReference
#check @claim_33_01
#print axioms claim_33_01
alias claim_33_02 := RepulsiveCoulomb.PaperRoute.paperCompactLabeledRateFromReferenceFamily
#check @claim_33_02
#print axioms claim_33_02
alias claim_33_03 := RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate
#check @claim_33_03
#print axioms claim_33_03
alias claim_33_04 := RepulsiveCoulomb.PaperRoute.paperOriginalCompactLabeledRate
#check @claim_33_04
#print axioms claim_33_04
alias claim_33_05 := RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate_le_optimal
#check @claim_33_05
#print axioms claim_33_05
alias claim_33_06 := RepulsiveCoulomb.PaperRoute.paperOriginalCompactLabeledRate_le_optimal
#check @claim_33_06
#print axioms claim_33_06

end IntegratedMappedClaims

namespace IntegratedScope01

/- Scoped semantic consumer; namespace/import-context adaptations are recorded in generation-manifest.json. -/


open Set MeasureTheory ProbabilityTheory
open PeriodicAttractiveLogGas
open scoped BigOperators
open RepulsiveCoulomb.PaperRoute

example (Q : ℝ) : 0 < paperWeightedP1 Q := paperWeightedP1_pos Q
example (Q : ℝ) : 0 < paperWeightedK1 Q := paperWeightedK1_pos Q
example {γ : ℝ} (hγ : 0 < γ) (Q : ℝ) : 0 < paperCwt γ Q := paperCwt_pos hγ Q
example {γ : ℝ} (hγ : 0 < γ) (Q : ℝ) : 0 < paperRhoWt γ Q := paperRhoWt_pos hγ Q
example (γ Q : ℝ) : paperCwt γ Q = paperCwt 1 Q / γ := paperCwt_scaling γ Q
example (γ Q : ℝ) : paperRhoWt γ Q = γ * paperRhoWt 1 Q := paperRhoWt_scaling γ Q

example (Q : ℝ) {γ : ℝ} (hγ : 0 < γ)
    (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hQ : ∑ j, a j ≤ Q) (u : RepulsiveCoulomb.PointFormDomain hγ ha y) :
    variance (RepulsiveCoulomb.pointFormValueL hγ ha y u : ℂ → ℝ)
        (RepulsiveCoulomb.pointMeasure γ a y) ≤
      paperCwt γ Q * RepulsiveCoulomb.pointFormEnergy hγ ha y u ∧
    entropy (RepulsiveCoulomb.pointMeasure γ a y)
        (fun x => (RepulsiveCoulomb.pointFormValueL hγ ha y u x) ^ 2) ≤
      (((2 / paperRhoWt γ Q) * RepulsiveCoulomb.pointFormEnergy hγ ha y u : ℝ) : EReal) :=
  paper_weighted_named_inequalities Q hγ m a ha y hQ u

#check @RepulsiveCoulomb.PaperRoute.original_weighted_full_domain_of_moment
#print axioms RepulsiveCoulomb.PaperRoute.original_weighted_full_domain_of_moment
#check @RepulsiveCoulomb.PaperRoute.original_weighted_full_domain
#print axioms RepulsiveCoulomb.PaperRoute.original_weighted_full_domain
#check @RepulsiveCoulomb.PaperRoute.paperWeightedP1
#print axioms RepulsiveCoulomb.PaperRoute.paperWeightedP1
#check @RepulsiveCoulomb.PaperRoute.paperWeightedK1
#print axioms RepulsiveCoulomb.PaperRoute.paperWeightedK1
#check @RepulsiveCoulomb.PaperRoute.paper_weighted_named_spec
#print axioms RepulsiveCoulomb.PaperRoute.paper_weighted_named_spec
#check @RepulsiveCoulomb.PaperRoute.paperWeightedP1_pos
#print axioms RepulsiveCoulomb.PaperRoute.paperWeightedP1_pos
#check @RepulsiveCoulomb.PaperRoute.paperWeightedK1_pos
#print axioms RepulsiveCoulomb.PaperRoute.paperWeightedK1_pos
#check @RepulsiveCoulomb.PaperRoute.paperCwt
#print axioms RepulsiveCoulomb.PaperRoute.paperCwt
#check @RepulsiveCoulomb.PaperRoute.paperRhoWt
#print axioms RepulsiveCoulomb.PaperRoute.paperRhoWt
#check @RepulsiveCoulomb.PaperRoute.paperCwt_pos
#print axioms RepulsiveCoulomb.PaperRoute.paperCwt_pos
#check @RepulsiveCoulomb.PaperRoute.paperRhoWt_pos
#print axioms RepulsiveCoulomb.PaperRoute.paperRhoWt_pos
#check @RepulsiveCoulomb.PaperRoute.paperCwt_scaling
#print axioms RepulsiveCoulomb.PaperRoute.paperCwt_scaling
#check @RepulsiveCoulomb.PaperRoute.paperRhoWt_scaling
#print axioms RepulsiveCoulomb.PaperRoute.paperRhoWt_scaling
#check @RepulsiveCoulomb.PaperRoute.paper_two_div_RhoWt
#print axioms RepulsiveCoulomb.PaperRoute.paper_two_div_RhoWt
#check @RepulsiveCoulomb.PaperRoute.paper_weighted_named_inequalities
#print axioms RepulsiveCoulomb.PaperRoute.paper_weighted_named_inequalities
#check @RepulsiveCoulomb.PaperRoute.paper_weighted_named_core
#print axioms RepulsiveCoulomb.PaperRoute.paper_weighted_named_core
#check @RepulsiveCoulomb.PaperRoute.paper_weighted_named_full_above
#print axioms RepulsiveCoulomb.PaperRoute.paper_weighted_named_full_above
#check @RepulsiveCoulomb.PaperRoute.paper_weighted_named_core_above
#print axioms RepulsiveCoulomb.PaperRoute.paper_weighted_named_core_above

open Lean Elab Command in
private partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env d
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env d

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := #[``RepulsiveCoulomb.PaperRoute.original_weighted_full_domain_of_moment,
    ``RepulsiveCoulomb.PaperRoute.original_weighted_full_domain,
    ``RepulsiveCoulomb.PaperRoute.paperWeightedP1,
    ``RepulsiveCoulomb.PaperRoute.paperWeightedK1,
    ``RepulsiveCoulomb.PaperRoute.paper_weighted_named_spec,
    ``RepulsiveCoulomb.PaperRoute.paperWeightedP1_pos,
    ``RepulsiveCoulomb.PaperRoute.paperWeightedK1_pos,
    ``RepulsiveCoulomb.PaperRoute.paperCwt,
    ``RepulsiveCoulomb.PaperRoute.paperRhoWt,
    ``RepulsiveCoulomb.PaperRoute.paperCwt_pos,
    ``RepulsiveCoulomb.PaperRoute.paperRhoWt_pos,
    ``RepulsiveCoulomb.PaperRoute.paperCwt_scaling,
    ``RepulsiveCoulomb.PaperRoute.paperRhoWt_scaling,
    ``RepulsiveCoulomb.PaperRoute.paper_two_div_RhoWt,
    ``RepulsiveCoulomb.PaperRoute.paper_weighted_named_inequalities,
    ``RepulsiveCoulomb.PaperRoute.paper_weighted_named_core,
    ``RepulsiveCoulomb.PaperRoute.paper_weighted_named_full_above,
    ``RepulsiveCoulomb.PaperRoute.paper_weighted_named_core_above]
  let (_, deps) := (roots.forM (visit env)).run ({} : NameSet)
  for n in #[`RepulsiveCoulomb.pointSobolevKappa,
      `RepulsiveCoulomb.rawPointMeasure_strong_sobolev_squared_norm,
      `RepulsiveCoulomb.rawPoint_uniform_local_sobolev_poincare,
      `RepulsiveCoulomb.pointGaussian_uniform_local_geometry,
      `RepulsiveCoulomb.pointCore_uniform_poincare,
      `RepulsiveCoulomb.pointForm_uniform_poincare,
      `RepulsiveCoulomb.pointCore_local_superPoincare,
      `RepulsiveCoulomb.pointCore_global_superPoincare,
      `RepulsiveCoulomb.pointCore_uniform_defective_lsi,
      `RepulsiveCoulomb.pointForm_uniform_defective_lsi,
      `RepulsiveCoulomb.pointCore_uniform_tight_lsi,
      `RepulsiveCoulomb.pointMeasure_half_mass_ball,
      `RepulsiveCoulomb.pointCore_weighted_moment_bound,
      `RepulsiveCoulomb.pointForm_weighted_moment_bound,
      `RepulsiveCoulomb.pointForm_uniform_quadratic_moment,
      `RepulsiveCoulomb.pointCore_uniform_exterior_mass,
      `RepulsiveCoulomb.pointScore_uncertainty,
      `RepulsiveCoulomb.pointScore_finite_moment_bound,
      `RepulsiveCoulomb.pointScore_annular_uniform_bound,
      `RepulsiveCoulomb.pointScoreBadAnnulus_volume_le,
      `RepulsiveCoulomb.pointScoreBadAnnulus_real_volume_le,
      `RepulsiveCoulomb.pointScore_small_region_measure,
      `RepulsiveCoulomb.pointLogForce_weak_l2,
      `RepulsiveCoulomb.pointLogForce_weak_l2_of_total_le,
      `RepulsiveCoulomb.pointDilationBranchP1, `RepulsiveCoulomb.pointDilationBranchK1,
      `RepulsiveCoulomb.pointDilationBranchCwt, `RepulsiveCoulomb.pointDilationBranchRhoWt,
      `RepulsiveCoulomb.pointDilationBranch_uniform_core,
      `RepulsiveCoulomb.pointDilationBranch_uniform_full_domain,
      `sorryAx] do
    if deps.contains n then throwError "Forbidden actual transitive dependency: {n}"
  for n in deps do
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
  let (_, endpointDeps) := (visit env ``paper_weighted_named_inequalities).run ({} : NameSet)
  for n in #[``original_weighted_full_domain,
      ``original_point_localGeometry, ``original_uniform_raw_strong_sobolev,
      ``strong_sobolev_squared_norm_of_dilation_two,
      ``gaussian_local_sobolev, ``gaussian_local_poincare,
      ``disk_half_mass_ball, ``RepulsiveCoulomb.unitDisk_raw_weight_jensen,
      ``atomic_pointForm_weighted_moment_bound,
      ``planarMeasureMaximal_weak_measure,
      ``finite_inverse_sum_le_of_ball_growth,
      ``core_exterior_mass_of_moment, ``core_global_superPoincare,
      ``core_defective_lsi_of_gaussian_spi,
      ``RepulsiveCoulomb.pointCore_normalized_entropy_of_spi,
      ``RepulsiveCoulomb.pointForm_defective_lsi_of_core,
      ``RepulsiveCoulomb.pointForm_poincare_of_core,
      ``RepulsiveCoulomb.bounded_defective_lsi_tightening,
      ``RepulsiveCoulomb.pointDilationBranch_core_energy] do
    unless endpointDeps.contains n do throwError "Required actual producer missing: {n}"
  logInfo m!"PASS: {roots.size} declarations; actual original-input route and new named witnesses use new same-map Sobolev, disk Jensen, atomic-maximal confinement, Gaussian SPI, Wang, Rothaus and dilation."


end IntegratedScope01

namespace IntegratedScope02

/- Scoped semantic consumer; namespace/import-context adaptations are recorded in generation-manifest.json. -/


open MeasureTheory Real Set Metric TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff
open RepulsiveCoulomb RepulsiveCoulomb.PaperRoute PeriodicAttractiveLogGas

example {β : ℝ} (hβ : 0 < β) (μ : ProbabilityMeasure ℂ)
    (hmin : ∀ ν : ProbabilityMeasure ℂ, equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) :
    ∃ R : EquilibriumConstructedReference β, R.measure = μ :=
  thermal_physicalReference_from_minimizer hβ μ hmin

example {β : ℝ} (hβ : 0 < β) :
    (∫ x : ℂ, ‖x‖^2 * (thermalConstructedReference β hβ).density x) = 1/2+2/β :=
  (thermalConstructedReference β hβ).secondMoment

example {β : ℝ} (hβ : 0 < β) :
    ContDiff ℝ (⊤ : ℕ∞) (thermalConstructedReference β hβ).density ∧
      ∀ x, 0 < (thermalConstructedReference β hβ).density x ∧
        (thermalConstructedReference β hβ).density x ≤ Real.pi⁻¹ :=
  ⟨(thermalConstructedReference β hβ).smooth, fun x =>
    ⟨(thermalConstructedReference β hβ).positive x, (thermalConstructedReference β hβ).cap x⟩⟩

example {β : ℝ} (hβ : 0 < β) (ν : ProbabilityMeasure ℂ)
    (hmin : ∀ ξ : ProbabilityMeasure ℂ, equilibriumCanonicalFreeEnergy β ν ≤ equilibriumCanonicalFreeEnergy β ξ) :
    (thermalConstructedReference β hβ).measure = ν :=
  thermalConstructedReference_measure_unique hβ ν hmin

example {β : ℝ} (hβ : 0 < β) : 0 < paperOriginalLabeledRate hβ := paperOriginalLabeledRate_pos hβ

example {β : ℝ} (hβ : 0 < β) (u : CoulombFormDomain 2 hβ) :
    entropy (coulombMeasure 2 β) (fun z => (coulombFormValueL 2 hβ u z)^2) ≤
      (((2 / paperOriginalLabeledRate hβ) * coulombFormEnergy 2 hβ u : ℝ) : EReal) :=
  paper_full_labeled_lsi_original hβ 2 (by norm_num) u

example {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (β : Set.Icc a b) (N : ℕ) (hN : 2 ≤ N)
    (u : CoulombFormDomain N (ha.trans_le β.2.1)) :
    entropy (coulombMeasure N β.1) (fun z => (coulombFormValueL N (ha.trans_le β.2.1) u z)^2) ≤
      (((2 / paperOriginalCompactLabeledRate (b := b) ha) *
        coulombFormEnergy N (ha.trans_le β.2.1) u : ℝ) : EReal) :=
  (paper_uniform_labeled_lsi_original ha hab).2 β N hN u

example : 0 < paperOriginalCompactLabeledRate (a := 1) (b := 2) (by norm_num) :=
  paperOriginalCompactLabeledRate_pos (by norm_num) (by norm_num)
#check thermal_physicalReference_from_minimizer
#check thermalConstructedReference_nonempty
#check thermalConstructedReference
#check thermalConstructedReference_measure_unique
#check paperOriginalLabeledRate
#check paperOriginalLabeledRate_pos
#check paper_full_labeled_lsi_original
#check paperOriginalReferenceFamily
#check paperOriginalCompactLabeledRate
#check paperOriginalCompactLabeledRate_pos
#check paper_uniform_labeled_lsi_original
#print axioms thermal_physicalReference_from_minimizer
#print axioms thermalConstructedReference_nonempty
#print axioms thermalConstructedReference
#print axioms thermalConstructedReference_measure_unique
#print axioms paperOriginalLabeledRate
#print axioms paperOriginalLabeledRate_pos
#print axioms paper_full_labeled_lsi_original
#print axioms paperOriginalReferenceFamily
#print axioms paperOriginalCompactLabeledRate
#print axioms paperOriginalCompactLabeledRate_pos
#print axioms paper_uniform_labeled_lsi_original
namespace OriginalInputLSIAudit
open Lean Elab Command
partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env d
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env d
/-- The cited DG instance retains a valid older internal envelope. Its
full proof is still audited for axioms and forbidden producers above; only
the authored-normalizer exclusion stops at this explicitly named boundary. -/
partial def visitAuthored (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visitAuthored env d
    if n == ``paper_dg_fixed_coupling then return
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visitAuthored env d
run_cmd do
  let env ← getEnv
  let (_, deps) := (visit env ``paper_uniform_labeled_lsi_original).run ({} : NameSet)
  let allNew := #[``thermal_physicalReference_from_minimizer, ``thermalConstructedReference_nonempty, ``thermalConstructedReference, ``thermalConstructedReference_measure_unique, ``paperOriginalLabeledRate, ``paperOriginalLabeledRate_pos, ``paper_full_labeled_lsi_original, ``paperOriginalReferenceFamily, ``paperOriginalCompactLabeledRate, ``paperOriginalCompactLabeledRate_pos, ``paper_uniform_labeled_lsi_original]
  let (_, allDeps) := (do for n in allNew do visit env n).run ({} : NameSet)
  for n in allDeps do
    if n == `sorryAx then throwError "Incomplete proof in new bounded radial EL representative"
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
    for forbidden in #["equilibriumConstructedReference", "equilibriumConstructedReference_nonempty",
        "equilibriumConstructedReference_measure_unique", "equilibrium_pointwise_EL_densities_unique",
        "equilibriumCanonicalMinimizers_unique", "equilibrium_pointwise_EL_radial",
        "equilibriumObjective_lowerSemicontinuous", "equilibriumExtendedInteraction_lowerSemicontinuous",
        "equilibriumObjective_exists_global_minimizer", "equilibriumCanonical_exists_global_minimizer",
        "equilibrium_exists_bounded_EL_minimizer", "equilibrium_pointwise_EL_sharp_cap", "equilibrium_EL_circle_log_increment",
        "equilibrium_pointwise_EL_contDiff",
        "equilibrium_pointwise_EL_contDiff_one", "equilibriumThermalReference"] do
      if n.toString == "RepulsiveCoulomb." ++ forbidden then
        throwError "Forbidden old selected-reference/minimizer/radiality shortcut: {n}"
  logInfo "PASS: original-input declarations have standard axioms and exclude old minimizer/reference/uniqueness/smoothness/circle-cap shortcuts"
  for n in #[``thermalCanonical_exists_global_minimizer,
      ``thermalCanonical_global_minimizer_finite_domain,
      ``equilibriumCanonicalMinimizer_exists_bounded_EL_density,
      ``equilibriumCanonicalMinimizer_density_positive_ae,
      ``equilibriumCanonicalMinimizer_eulerLagrange_ae,
      ``equilibriumELRepresentative_pointwise_properties,
      ``thermalBoundedDensity_pointPotential_integrable,
      ``thermalBoundedDensity_extendedPotential_eq_potential,
      ``thermalCanonical_bounded_density_potential_radial,
      ``thermalCanonical_minimizer_extendedPotential_eq_of_norm_eq,
      ``thermalCanonical_minimizer_map_isometry,
      ``thermalCanonical_global_minimizers_unique,
      ``thermalDensityMixture_entropy_strict,
      ``log_green_zero_mass,
      ``boundedDensityPotential_weak_poisson,
      ``boundedDensity_kernel_compact_test_integrable,
      ``translated_log_fundamental_solution,
      ``log_fundamental_solution,
      ``thermal_radial_weak_regularity,
      ``cumulativeMass_increment_le_of_density_bound,
      ``thermalNewtonGradient_lipschitz,
      ``RepulsiveCoulomb.PaperRoute.plane_hasWeakFDerivOn_of_lipschitzOn_closedBall,
      ``RepulsiveCoulomb.PaperRoute.plane_ae_differentiableAt_of_lipschitzOn_closedBall,
      ``RepulsiveCoulomb.PaperRoute.scalar_integral_lineDeriv_mul_of_lipschitzOn_closedBall,
      ``LipschitzWith.integral_lineDeriv_mul_eq,
      ``LipschitzOnWith.ae_differentiableWithinAt_of_mem,
      ``thermal_radial_potential_fderiv_hasWeakFDerivOn,
      ``thermalWeakHessian_memLp_isCompact,
      ``thermal_radial_potential_fderiv_holder_closedBall,
      ``thermal_EL_contDiff_one_of_potential,
      ``thermal_radial_EL_smooth_of_potential_contDiff_one,
      ``equilibriumCumulativeMass_eq_radialAverage,
      ``equilibriumRadialAverage_contDiff,
      ``thermalDensityPotential_fderiv_eq_newtonGradient,
      ``thermalNewtonGradient_riesz,
      ``thermal_sharp_cap_of_smooth_bounded_EL,
      ``thermal_logDensity_laplacian_of_smooth_EL,
      ``boundedDensityPotential_classical_poisson,
      ``ae_eq_of_integral_contDiff_smul_eq,
      ``Measure.eq_of_ae_eq,
      ``integral_mul_laplacian_eq,
      ``thermal_gaussian_envelope_attains_max,
      ``laplacian_nonpos_at_globalMax,
      ``second_fderiv_nonpos_at_globalMax,
      ``deriv_deriv_nonpos_at_globalMax_zero,
      ``strictConvexOn_of_deriv2_pos,
      ``thermal_physicalReference_from_minimizer,
      ``thermalConstructedReference_nonempty,
      ``thermalConstructedReference,
      ``equilibriumDensityMinimizer_secondMoment,
      ``equilibrium_hasDerivAt_scale_freeEnergy,
      ``equilibriumDensityScale_freeEnergy,
      ``paper_uniform_labeled_lsi_via_disk_reference_family,
      ``paperCompactEntropyDefect,
      ``paper_core_one_site_sum_compact,
      ``paper_full_labeled_poincare_compact_via_resolvent,
      ``paper_full_defective_compact_of_integrable,
      ``paper_reference_EL_normalizer_inverse,
      ``paper_reference_EL_normalizer_unitDisk_lower,
      ``paper_reference_uniform_envelope_disk,
      ``paper_reference_potential_exponential_bound_disk,
      ``paper_gibbs_defect_moment_of_oneBody,
      ``paper_physical_gibbs_defect_moment_of_oneBody,
      ``paper_normalized_core_defective_of_exp_integrable,
      ``paper_compact_reference_integral_bounds_disk,
      ``paper_reference_modulated_exp_integrable_polynomial,
      ``paper_reference_modulated_polynomial_lower,
      ``paper_reference_partition_lower_polynomial,
      ``paper_thermal_B_gibbs_integrable_polynomial,
      ``paper_spatial_partition_uniform,
      ``paper_reference_spatial_bridge,
      ``paper_dg_fixed_coupling,
      ``exponential_integral_holder,
      ``RepulsiveCoulomb.conditionalEntropyBranch_factorization_defect_of_exp_integrable,
      ``RepulsiveCoulomb.coulomb_form_tightening,
      ``RepulsiveCoulomb.PaperRoute.original_weighted_full_domain,
      ``RepulsiveCoulomb.PaperRoute.paper_resolvent_form_residual] do
    unless deps.contains n do throwError "Required actual producer not load-bearing: {n}"
  logInfo "PASS: NEW physical thermal reference and exact normalized-dilation moment, latest disk/spatial/form/resolvent and literal compact supremum are load-bearing"
  for n in #[`RepulsiveCoulomb.equilibriumReference_gibbs_defect_moment,
      `RepulsiveCoulomb.equilibriumReference_physical_gibbs_defect_moment,
      `RepulsiveCoulomb.conditionalEntropyBranch_defect_exp_integrable,
      `RepulsiveCoulomb.conditionalEntropyBranch_defect_nonneg,
      `RepulsiveCoulomb.equilibriumReferencePartition_uniform,
      `RepulsiveCoulomb.equilibriumConstructedReference_partition_uniform,
      `RepulsiveCoulomb.PaperRoute.paper_full_labeled_lsi_via_spatial_reference,
      `RepulsiveCoulomb.PaperRoute.paper_normalized_core_defective,
      `RepulsiveCoulomb.PaperRoute.paper_uniform_defect_nonneg,
      `RepulsiveCoulomb.PaperRoute.paper_full_defective_of_reference_bounds,
      `RepulsiveCoulomb.pointDilationBranchCwt,
      `RepulsiveCoulomb.pointDilationBranchRhoWt,
      `RepulsiveCoulomb.pointDilationBranchCrel] do
    if allDeps.contains n then throwError "Forbidden older entropy/normalizer/weighted producer: {n}"
  for n in allDeps do
    if n.toString.startsWith "RepulsiveCoulomb.coulomb_named_" ||
        n.toString.startsWith "RepulsiveCoulomb.pointDilationBranch_named_" then
      throwError "Forbidden older named endpoint: {n}"
  let (_, authored) := (do for n in allNew do visitAuthored env n).run ({} : NameSet)
  for n in #[`RepulsiveCoulomb.equilibriumLogKernel_zeroMass_nonneg,
      `RepulsiveCoulomb.equilibriumReference_modulated_exp_integrable,
      `RepulsiveCoulomb.equilibriumReferencePartition_lower,
      `RepulsiveCoulomb.equilibriumReferencePartition_pos,
      `RepulsiveCoulomb.conditionalEntropyBranch_B_gibbs_integrable,
      `RepulsiveCoulomb.conditionalEntropyBranch_B_core_integrable,
      `RepulsiveCoulomb.equilibriumReference_exp_elConstant_le,
      `RepulsiveCoulomb.equilibriumReference_tail_prefactor_bound,
      `RepulsiveCoulomb.equilibriumReference_uniform_envelope,
      `RepulsiveCoulomb.equilibriumReference_potential_exponential_bound,
      `RepulsiveCoulomb.equilibriumReference_polynomial_moment_bound] do
    if authored.contains n then throwError "Old normalizer outside the explicit cited-DG boundary: {n}"
  for root in #[``paper_full_labeled_lsi_original, ``paper_uniform_labeled_lsi_original] do
    let (_, used) := (visitAuthored env root).run ({} : NameSet)
    for n in #[``paper_gibbs_defect_moment_product_power,
        ``paper_gibbs_defect_moment_via_concavity,
        ``paper_product_exp_average_power,
        ``paper_exp_integral_inverse_power_concavity,
        ``Real.concaveOn_rpow, ``ConcaveOn.le_map_integral,
        ``paper_thermal_B_gibbs_integrable_positive_log,
        ``paper_coulomb_positive_log_density_gaussian_bound,
        ``paper_rpow_positive_log_bound,
        ``RepulsiveCoulomb.coulombDensity_le_gaussian_collision_power] do
      unless used.contains n do throwError "Latest authored product-power/concavity/positive-log producer absent from {root}: {n}"
  for n in #[`RepulsiveCoulomb.equilibriumProduct_exp_average,
      `RepulsiveCoulomb.PaperRoute.paper_reference_gibbs_energy_exp_integrable_polynomial,
      `RepulsiveCoulomb.PaperRoute.paper_reference_gibbs_energy_integrable_polynomial] do
    if authored.contains n then throwError "Superseded product or Gibbs-energy producer outside DG: {n}"
  let (_, thermal) := (visit env ``thermalConstructedReference).run ({} : NameSet)
  if thermal.contains `RepulsiveCoulomb.equilibriumLogKernel_zeroMass_nonneg then
    throwError "Old Green leaked into the authored NEW physical thermal constructor"
  for n in thermal do
    if n.toString.startsWith "RepulsiveCoulomb.pointMetricMap" then
      throwError "Point-map regularity substituted for actual potential regularity in the thermal constructor: {n}"
  unless thermal.contains ``log_green_zero_mass do
    throwError "NEW Green positivity is not load-bearing in the actual thermal constructor"
  logInfo m!"EXPLICIT_DG_POSITIVITY_BOUNDARY old zero-mass positivity is internal to the cited DG instance = {allDeps.contains `RepulsiveCoulomb.equilibriumLogKernel_zeroMass_nonneg}; the authored NEW thermal constructor is old-Green-free."
  logInfo m!"EXPLICIT_DG_BOUNDARY full closure contains old valid auxiliary envelope = {allDeps.contains `RepulsiveCoulomb.equilibriumReference_exp_elConstant_le}; authored thermal/disk/entropy route excludes it."
  for n in deps do
    if n.toString.startsWith "RepulsiveCoulomb." then logInfo m!"PROJECT_DEP {n}"
end OriginalInputLSIAudit


end IntegratedScope02

namespace IntegratedScope03

/- Scoped semantic consumer; namespace/import-context adaptations are recorded in generation-manifest.json. -/


open MeasureTheory Real Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff
open RepulsiveCoulomb RepulsiveCoulomb.PaperRoute

example {q : ℝ → ℝ} (hq : Continuous q) (r : ℝ) :
    HasDerivAt (thermalMassProfile q) (2*Real.pi*(r*q r)) r :=
  thermalMassProfile_hasDerivAt hq r

example {ρ : ℂ → ℝ} (hm : Measurable ρ) (h0 : ∀ x, 0 ≤ ρ x)
    (hi : Integrable ρ) (hmass : (∫ x, ρ x)=1)
    (hrad : ∀ ⦃x y : ℂ⦄, ‖x‖=‖y‖ → ρ x=ρ y) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ thermalMassProfile (thermalDensityProfile ρ) r ∧ thermalMassProfile (thermalDensityProfile ρ) r ≤ 1 :=
  thermalMassProfile_mem_unitInterval hm h0 hi hmass hrad hr

example {q u : ℝ → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hN : EqOn (fun r => r*deriv u r) (fun r => -thermalMassProfile q r) (Ioi 0))
    (n : ℕ) {r : ℝ} (hr : 0 < r) :
    r*iteratedDeriv (n+2) u r + (n+1 : ℕ)*iteratedDeriv (n+1) u r =
      -(2*Real.pi*(r*iteratedDeriv n q r + (n : ℝ)*iteratedDeriv (n-1) q r)) :=
  thermal_potential_profile_derivative_recurrence hq hu hN n hr

example {q u : ℝ → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hN : EqOn (fun r => r*deriv u r) (fun r => -thermalMassProfile q r) (Ioi 0))
    (hmass : ∀ r : ℝ, 1 ≤ r → 0 ≤ thermalMassProfile q r ∧ thermalMassProfile q r ≤ 1)
    (n : ℕ) (hb : ∀ j : ℕ, j < n → ThermalExteriorDerivativeBound q j) :
    ThermalExteriorDerivativeBound u (n+1) :=
  thermal_exterior_potential_derivatives_bounded hq hu hN hmass n hb

example {q u : ℝ → ℝ} {β : ℝ} (hβ : 0 < β)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hN : EqOn (fun r => r*deriv u r) (fun r => -thermalMassProfile q r) (Ioi 0))
    (hmass : ∀ r : ℝ, 1 ≤ r → 0 ≤ thermalMassProfile q r ∧ thermalMassProfile q r ≤ 1)
    (hscore : deriv q = fun r => -β*(thermalRadialScore u r*q r))
    (hzero : ThermalExteriorTail q β 0) : ∀ n : ℕ, ThermalExteriorTail q β n :=
  thermal_exterior_density_tails hβ hq hu hN hmass hscore hzero

example (n : ℕ) : ∃ A : ℝ, 0 < A ∧ ∀ (ρ : ℂ → ℝ) (q : ℝ → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) ρ → ContDiff ℝ (⊤ : ℕ∞) q →
    (∀ x, ρ x = q ‖x‖) → ∀ x : ℂ, x ≠ 0 →
    ‖x‖^n * ‖iteratedFDeriv ℝ n ρ x‖ ≤
      A * ∑ j ∈ Finset.range (n+1), ‖x‖^j * |iteratedDeriv j q ‖x‖| :=
  thermal_radial_cartesian_scaled_bound n

example {β : ℝ} (hβ : 0 < β) (R : EquilibriumConstructedReference β) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℂ, ‖iteratedFDeriv ℝ n R.density x‖ ≤
      C*(1+‖x‖)^(β+(n : ℝ))*Real.exp (-β*‖x‖^2/2) :=
  thermalReference_iteratedFDeriv_tail hβ R n

example {β : ℝ} (hβ : 0 < β) (R : EquilibriumConstructedReference β) (α : Fin 2 → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℂ, |equilibriumMultiIndexDerivative α R.density x| ≤
      C*(1+‖x‖)^(β+((α 0+α 1 : ℕ) : ℝ))*Real.exp (-β*‖x‖^2/2) :=
  thermalReference_multiIndex_tail hβ R α

example {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℂ, ‖iteratedFDeriv ℝ n (thermalConstructedReference β hβ).density x‖ ≤
      C*(1+‖x‖)^(β+(n : ℝ))*Real.exp (-β*‖x‖^2/2) :=
  thermalConstructedReference_iteratedFDeriv_tail hβ n

example {β : ℝ} (hβ : 0 < β) (α : Fin 2 → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℂ, |equilibriumMultiIndexDerivative α (thermalConstructedReference β hβ).density x| ≤
      C*(1+‖x‖)^(β+((α 0+α 1 : ℕ) : ℝ))*Real.exp (-β*‖x‖^2/2) :=
  thermalConstructedReference_multiIndex_tail hβ α

example {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℂ, |(thermalConstructedReference β hβ).density x| ≤
      C*(1+‖x‖)^β*Real.exp (-β*‖x‖^2/2) := by
  simpa only [equilibriumMultiIndexDerivative, equilibriumOrderedDirectionalDerivative,
    Nat.zero_add, Nat.cast_zero, add_zero] using
    thermalConstructedReference_multiIndex_tail hβ (fun _ => 0)
#check RepulsiveCoulomb.PaperRoute.thermalDensityProfile
#check RepulsiveCoulomb.PaperRoute.thermalPotentialProfile
#check RepulsiveCoulomb.PaperRoute.thermalMassProfile
#check RepulsiveCoulomb.PaperRoute.thermalConfinementProfile
#check RepulsiveCoulomb.PaperRoute.thermalDensityProfile_contDiff
#check RepulsiveCoulomb.PaperRoute.thermalPotentialProfile_contDiff
#check RepulsiveCoulomb.PaperRoute.thermalConfinementProfile_contDiff
#check RepulsiveCoulomb.PaperRoute.thermalMassProfile_hasDerivAt
#check RepulsiveCoulomb.PaperRoute.thermalMassProfile_deriv
#check RepulsiveCoulomb.PaperRoute.thermalMassProfile_contDiff
#check RepulsiveCoulomb.PaperRoute.thermalMassProfile_eq_cumulative
#check RepulsiveCoulomb.PaperRoute.thermalMassProfile_mem_unitInterval
#check RepulsiveCoulomb.PaperRoute.thermalPotentialProfile_hasDerivAt
#check RepulsiveCoulomb.PaperRoute.thermalPotentialProfile_mul_deriv
#check RepulsiveCoulomb.PaperRoute.thermalDensityProfile_eq_exp
#check RepulsiveCoulomb.PaperRoute.thermalDensityProfile_deriv_score
#check RepulsiveCoulomb.PaperRoute.thermal_hasDerivAt_iteratedDeriv
#check RepulsiveCoulomb.PaperRoute.thermal_iteratedDeriv_radius_mul_succ
#check RepulsiveCoulomb.PaperRoute.thermal_iteratedDeriv_radius_mul
#check RepulsiveCoulomb.PaperRoute.thermalMassProfile_iteratedDeriv
#check RepulsiveCoulomb.PaperRoute.thermal_potential_profile_derivative_recurrence
#check RepulsiveCoulomb.PaperRoute.ThermalExteriorDerivativeBound
#check RepulsiveCoulomb.PaperRoute.thermal_exterior_potential_derivatives_bounded
#check RepulsiveCoulomb.PaperRoute.thermalExteriorWeight
#check RepulsiveCoulomb.PaperRoute.ThermalExteriorTail
#check RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_pos
#check RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_mono
#check RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_succ
#check RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_eq_polynomialGaussian
#check RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_uniform_bound
#check RepulsiveCoulomb.PaperRoute.ThermalExteriorTail.derivativeBound
#check RepulsiveCoulomb.PaperRoute.thermalRadialScore
#check RepulsiveCoulomb.PaperRoute.thermalRadialScore_contDiff
#check RepulsiveCoulomb.PaperRoute.thermalConfinementProfile_deriv
#check RepulsiveCoulomb.PaperRoute.thermalRadialScore_abs_le
#check RepulsiveCoulomb.PaperRoute.thermalRadialScore_derivative_bound
#check RepulsiveCoulomb.PaperRoute.thermalRadialScore_derivative_linear_bound
#check RepulsiveCoulomb.PaperRoute.thermal_exterior_density_tail_step
#check RepulsiveCoulomb.PaperRoute.thermal_exterior_density_tails
#check RepulsiveCoulomb.PaperRoute.thermal_actual_density_profile_tails
#check RepulsiveCoulomb.PaperRoute.thermal_norm_derivatives_sphere_bound
#check RepulsiveCoulomb.PaperRoute.thermal_radial_cartesian_scaled_bound
#check RepulsiveCoulomb.PaperRoute.thermal_radial_cartesian_bound
#check RepulsiveCoulomb.PaperRoute.thermal_cartesian_exterior_tails_of_profile
#check RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_lower_on_unitBall
#check RepulsiveCoulomb.PaperRoute.thermal_cartesian_tails_of_profile
#check RepulsiveCoulomb.PaperRoute.thermal_actual_density_cartesian_tails
#check RepulsiveCoulomb.PaperRoute.thermalReference_potential_contDiff
#check RepulsiveCoulomb.PaperRoute.thermalReference_iteratedFDeriv_tail
#check RepulsiveCoulomb.PaperRoute.thermalReference_multiIndex_tail
#check RepulsiveCoulomb.PaperRoute.thermalConstructedReference_iteratedFDeriv_tail
#check RepulsiveCoulomb.PaperRoute.thermalConstructedReference_multiIndex_tail
#print axioms RepulsiveCoulomb.PaperRoute.thermalDensityProfile
#print axioms RepulsiveCoulomb.PaperRoute.thermalPotentialProfile
#print axioms RepulsiveCoulomb.PaperRoute.thermalMassProfile
#print axioms RepulsiveCoulomb.PaperRoute.thermalConfinementProfile
#print axioms RepulsiveCoulomb.PaperRoute.thermalDensityProfile_contDiff
#print axioms RepulsiveCoulomb.PaperRoute.thermalPotentialProfile_contDiff
#print axioms RepulsiveCoulomb.PaperRoute.thermalConfinementProfile_contDiff
#print axioms RepulsiveCoulomb.PaperRoute.thermalMassProfile_hasDerivAt
#print axioms RepulsiveCoulomb.PaperRoute.thermalMassProfile_deriv
#print axioms RepulsiveCoulomb.PaperRoute.thermalMassProfile_contDiff
#print axioms RepulsiveCoulomb.PaperRoute.thermalMassProfile_eq_cumulative
#print axioms RepulsiveCoulomb.PaperRoute.thermalMassProfile_mem_unitInterval
#print axioms RepulsiveCoulomb.PaperRoute.thermalPotentialProfile_hasDerivAt
#print axioms RepulsiveCoulomb.PaperRoute.thermalPotentialProfile_mul_deriv
#print axioms RepulsiveCoulomb.PaperRoute.thermalDensityProfile_eq_exp
#print axioms RepulsiveCoulomb.PaperRoute.thermalDensityProfile_deriv_score
#print axioms RepulsiveCoulomb.PaperRoute.thermal_hasDerivAt_iteratedDeriv
#print axioms RepulsiveCoulomb.PaperRoute.thermal_iteratedDeriv_radius_mul_succ
#print axioms RepulsiveCoulomb.PaperRoute.thermal_iteratedDeriv_radius_mul
#print axioms RepulsiveCoulomb.PaperRoute.thermalMassProfile_iteratedDeriv
#print axioms RepulsiveCoulomb.PaperRoute.thermal_potential_profile_derivative_recurrence
#print axioms RepulsiveCoulomb.PaperRoute.ThermalExteriorDerivativeBound
#print axioms RepulsiveCoulomb.PaperRoute.thermal_exterior_potential_derivatives_bounded
#print axioms RepulsiveCoulomb.PaperRoute.thermalExteriorWeight
#print axioms RepulsiveCoulomb.PaperRoute.ThermalExteriorTail
#print axioms RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_pos
#print axioms RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_mono
#print axioms RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_succ
#print axioms RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_eq_polynomialGaussian
#print axioms RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_uniform_bound
#print axioms RepulsiveCoulomb.PaperRoute.ThermalExteriorTail.derivativeBound
#print axioms RepulsiveCoulomb.PaperRoute.thermalRadialScore
#print axioms RepulsiveCoulomb.PaperRoute.thermalRadialScore_contDiff
#print axioms RepulsiveCoulomb.PaperRoute.thermalConfinementProfile_deriv
#print axioms RepulsiveCoulomb.PaperRoute.thermalRadialScore_abs_le
#print axioms RepulsiveCoulomb.PaperRoute.thermalRadialScore_derivative_bound
#print axioms RepulsiveCoulomb.PaperRoute.thermalRadialScore_derivative_linear_bound
#print axioms RepulsiveCoulomb.PaperRoute.thermal_exterior_density_tail_step
#print axioms RepulsiveCoulomb.PaperRoute.thermal_exterior_density_tails
#print axioms RepulsiveCoulomb.PaperRoute.thermal_actual_density_profile_tails
#print axioms RepulsiveCoulomb.PaperRoute.thermal_norm_derivatives_sphere_bound
#print axioms RepulsiveCoulomb.PaperRoute.thermal_radial_cartesian_scaled_bound
#print axioms RepulsiveCoulomb.PaperRoute.thermal_radial_cartesian_bound
#print axioms RepulsiveCoulomb.PaperRoute.thermal_cartesian_exterior_tails_of_profile
#print axioms RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_lower_on_unitBall
#print axioms RepulsiveCoulomb.PaperRoute.thermal_cartesian_tails_of_profile
#print axioms RepulsiveCoulomb.PaperRoute.thermal_actual_density_cartesian_tails
#print axioms RepulsiveCoulomb.PaperRoute.thermalReference_potential_contDiff
#print axioms RepulsiveCoulomb.PaperRoute.thermalReference_iteratedFDeriv_tail
#print axioms RepulsiveCoulomb.PaperRoute.thermalReference_multiIndex_tail
#print axioms RepulsiveCoulomb.PaperRoute.thermalConstructedReference_iteratedFDeriv_tail
#print axioms RepulsiveCoulomb.PaperRoute.thermalConstructedReference_multiIndex_tail
namespace ThermalExteriorTailAudit
open Lean Elab Command
partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env d
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env d
run_cmd do
  let env ← getEnv
  let (_, deps) := (visit env ``thermalConstructedReference_multiIndex_tail).run ({} : NameSet)
  let allNew := #[``RepulsiveCoulomb.PaperRoute.thermalDensityProfile, ``RepulsiveCoulomb.PaperRoute.thermalPotentialProfile, ``RepulsiveCoulomb.PaperRoute.thermalMassProfile, ``RepulsiveCoulomb.PaperRoute.thermalConfinementProfile, ``RepulsiveCoulomb.PaperRoute.thermalDensityProfile_contDiff, ``RepulsiveCoulomb.PaperRoute.thermalPotentialProfile_contDiff, ``RepulsiveCoulomb.PaperRoute.thermalConfinementProfile_contDiff, ``RepulsiveCoulomb.PaperRoute.thermalMassProfile_hasDerivAt, ``RepulsiveCoulomb.PaperRoute.thermalMassProfile_deriv, ``RepulsiveCoulomb.PaperRoute.thermalMassProfile_contDiff, ``RepulsiveCoulomb.PaperRoute.thermalMassProfile_eq_cumulative, ``RepulsiveCoulomb.PaperRoute.thermalMassProfile_mem_unitInterval, ``RepulsiveCoulomb.PaperRoute.thermalPotentialProfile_hasDerivAt, ``RepulsiveCoulomb.PaperRoute.thermalPotentialProfile_mul_deriv, ``RepulsiveCoulomb.PaperRoute.thermalDensityProfile_eq_exp, ``RepulsiveCoulomb.PaperRoute.thermalDensityProfile_deriv_score, ``RepulsiveCoulomb.PaperRoute.thermal_hasDerivAt_iteratedDeriv, ``RepulsiveCoulomb.PaperRoute.thermal_iteratedDeriv_radius_mul_succ, ``RepulsiveCoulomb.PaperRoute.thermal_iteratedDeriv_radius_mul, ``RepulsiveCoulomb.PaperRoute.thermalMassProfile_iteratedDeriv, ``RepulsiveCoulomb.PaperRoute.thermal_potential_profile_derivative_recurrence, ``RepulsiveCoulomb.PaperRoute.ThermalExteriorDerivativeBound, ``RepulsiveCoulomb.PaperRoute.thermal_exterior_potential_derivatives_bounded, ``RepulsiveCoulomb.PaperRoute.thermalExteriorWeight, ``RepulsiveCoulomb.PaperRoute.ThermalExteriorTail, ``RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_pos, ``RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_mono, ``RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_succ, ``RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_eq_polynomialGaussian, ``RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_uniform_bound, ``RepulsiveCoulomb.PaperRoute.ThermalExteriorTail.derivativeBound, ``RepulsiveCoulomb.PaperRoute.thermalRadialScore, ``RepulsiveCoulomb.PaperRoute.thermalRadialScore_contDiff, ``RepulsiveCoulomb.PaperRoute.thermalConfinementProfile_deriv, ``RepulsiveCoulomb.PaperRoute.thermalRadialScore_abs_le, ``RepulsiveCoulomb.PaperRoute.thermalRadialScore_derivative_bound, ``RepulsiveCoulomb.PaperRoute.thermalRadialScore_derivative_linear_bound, ``RepulsiveCoulomb.PaperRoute.thermal_exterior_density_tail_step, ``RepulsiveCoulomb.PaperRoute.thermal_exterior_density_tails, ``RepulsiveCoulomb.PaperRoute.thermal_actual_density_profile_tails, ``RepulsiveCoulomb.PaperRoute.thermal_norm_derivatives_sphere_bound, ``RepulsiveCoulomb.PaperRoute.thermal_radial_cartesian_scaled_bound, ``RepulsiveCoulomb.PaperRoute.thermal_radial_cartesian_bound, ``RepulsiveCoulomb.PaperRoute.thermal_cartesian_exterior_tails_of_profile, ``RepulsiveCoulomb.PaperRoute.thermalExteriorWeight_lower_on_unitBall, ``RepulsiveCoulomb.PaperRoute.thermal_cartesian_tails_of_profile, ``RepulsiveCoulomb.PaperRoute.thermal_actual_density_cartesian_tails, ``RepulsiveCoulomb.PaperRoute.thermalReference_potential_contDiff, ``RepulsiveCoulomb.PaperRoute.thermalReference_iteratedFDeriv_tail, ``RepulsiveCoulomb.PaperRoute.thermalReference_multiIndex_tail, ``RepulsiveCoulomb.PaperRoute.thermalConstructedReference_iteratedFDeriv_tail, ``RepulsiveCoulomb.PaperRoute.thermalConstructedReference_multiIndex_tail]
  let (_, allDeps) := (do for n in allNew do visit env n).run ({} : NameSet)
  for n in allDeps do
    if n == `sorryAx then throwError "Incomplete proof in new bounded radial EL representative"
    if n.toString.startsWith "RepulsiveCoulomb.equilibriumReference_" then
      throwError "Frozen supplied-reference producer appears in thermal tail closure: {n}"
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
    for forbidden in #["equilibriumConstructedReference", "equilibriumConstructedReference_nonempty",
        "equilibriumReference_derivative_tail_step", "equilibriumReference_allDerivative_tails",
        "equilibriumReference_firstDerivative_tail", "equilibriumReference_fderiv_globally_bounded",
        "equilibriumReference_fderiv_norm_le", "equilibriumReference_radialAverage_bounds",
        "equilibriumReference_scoreFactor_bounds",
        "equilibriumWeightedRadialOperator_iteratedFDeriv_norm_le",
        "equilibriumRadialAverage_iteratedFDeriv_norm_le",
        "equilibriumReference_iteratedFDeriv_tail", "equilibriumReference_multiIndex_tail",
        "equilibriumConstructedReference_multiIndex_tail", "equilibriumLogKernel_zeroMass_nonneg", "equilibrium_pointwise_EL_densities_unique",
        "equilibriumCanonicalMinimizers_unique", "equilibrium_pointwise_EL_radial",
        "equilibriumObjective_lowerSemicontinuous", "equilibriumExtendedInteraction_lowerSemicontinuous",
        "equilibriumObjective_exists_global_minimizer", "equilibriumCanonical_exists_global_minimizer",
        "equilibrium_exists_bounded_EL_minimizer", "equilibrium_pointwise_EL_sharp_cap", "equilibrium_EL_circle_log_increment",
        "equilibrium_pointwise_EL_contDiff",
        "equilibrium_pointwise_EL_contDiff_one", "pointMetricMap_hasWeakFDerivOn",
        "pointMetricMap_memW1pLoc_of_lipschitzOn_closedBall", "equilibriumThermalReference"] do
      if n.toString == "RepulsiveCoulomb." ++ forbidden then
        throwError "Forbidden old selected-reference/minimizer/radiality shortcut: {n}"
  logInfo "PASS: all new profile/conversion/tail declaration types and opaque proofs have standard axioms and exclude every old higher-tail or selected-reference producer"
  for n in #[``thermalCanonical_exists_global_minimizer,
      ``thermalCanonical_global_minimizer_finite_domain,
      ``equilibriumCanonicalMinimizer_exists_bounded_EL_density,
      ``equilibriumCanonicalMinimizer_density_positive_ae,
      ``equilibriumCanonicalMinimizer_eulerLagrange_ae,
      ``equilibriumELRepresentative_pointwise_properties,
      ``thermalBoundedDensity_pointPotential_integrable,
      ``thermalBoundedDensity_extendedPotential_eq_potential,
      ``thermalCanonical_bounded_density_potential_radial,
      ``thermalCanonical_minimizer_extendedPotential_eq_of_norm_eq,
      ``thermalCanonical_minimizer_map_isometry,
      ``thermalCanonical_global_minimizers_unique,
      ``thermalDensityMixture_entropy_strict,
      ``log_green_zero_mass,
      ``boundedDensityPotential_weak_poisson,
      ``boundedDensity_kernel_compact_test_integrable,
      ``translated_log_fundamental_solution,
      ``log_fundamental_solution,
      ``thermal_radial_weak_regularity,
      ``cumulativeMass_increment_le_of_density_bound,
      ``thermalNewtonGradient_lipschitz,
      ``RepulsiveCoulomb.PaperRoute.plane_hasWeakFDerivOn_of_lipschitzOn_closedBall,
      ``RepulsiveCoulomb.PaperRoute.plane_ae_differentiableAt_of_lipschitzOn_closedBall,
      ``RepulsiveCoulomb.PaperRoute.scalar_integral_lineDeriv_mul_of_lipschitzOn_closedBall,
      ``LipschitzWith.integral_lineDeriv_mul_eq,
      ``LipschitzOnWith.ae_differentiableWithinAt_of_mem,
      ``thermal_radial_potential_fderiv_hasWeakFDerivOn,
      ``thermalWeakHessian_memLp_isCompact,
      ``thermal_radial_potential_fderiv_holder_closedBall,
      ``thermal_EL_contDiff_one_of_potential,
      ``thermal_radial_EL_smooth_of_potential_contDiff_one,
      ``equilibriumCumulativeMass_eq_radialAverage,
      ``equilibriumRadialAverage_contDiff,
      ``thermalDensityPotential_fderiv_eq_newtonGradient,
      ``thermalNewtonGradient_riesz,
      ``thermal_sharp_cap_of_smooth_bounded_EL,
      ``thermal_logDensity_laplacian_of_smooth_EL,
      ``boundedDensityPotential_classical_poisson,
      ``ae_eq_of_integral_contDiff_smul_eq,
      ``Measure.eq_of_ae_eq,
      ``integral_mul_laplacian_eq,
      ``thermal_gaussian_envelope_attains_max,
      ``laplacian_nonpos_at_globalMax,
      ``second_fderiv_nonpos_at_globalMax,
      ``deriv_deriv_nonpos_at_globalMax_zero,
      ``strictConvexOn_of_deriv2_pos,
      ``thermalConstructedReference,
      ``thermal_physicalReference_from_minimizer,
      ``thermalReference_potential_contDiff,
      ``thermalReference_iteratedFDeriv_tail,
      ``thermal_actual_density_cartesian_tails,
      ``thermal_cartesian_tails_of_profile,
      ``thermal_cartesian_exterior_tails_of_profile,
      ``thermal_radial_cartesian_bound,
      ``thermal_radial_cartesian_scaled_bound,
      ``thermal_norm_derivatives_sphere_bound,
      ``norm_iteratedFDerivWithin_comp_le,
      ``iteratedFDeriv_comp_const_smul,
      ``thermal_actual_density_profile_tails,
      ``thermal_exterior_density_tails,
      ``thermal_exterior_density_tail_step,
      ``thermalRadialScore_derivative_bound,
      ``thermal_exterior_potential_derivatives_bounded,
      ``thermal_potential_profile_derivative_recurrence,
      ``thermalMassProfile_iteratedDeriv,
      ``thermalMassProfile_hasDerivAt,
      ``thermalPotentialProfile_mul_deriv,
      ``thermalDensityProfile_deriv_score,
      ``thermalExteriorWeight_uniform_bound,
      ``equilibriumMultiIndexDerivative_norm_le] do
    unless deps.contains n do throwError "Required actual producer not load-bearing: {n}"
  logInfo "PASS: NEW original reference, physical profile/FTC/Newton recurrence, exact beta+n induction, radius-power sphere conversion, compact disk and literal multi-index comparison are load-bearing"
  for n in deps do
    if n.toString.startsWith "RepulsiveCoulomb." then logInfo m!"PROJECT_DEP {n}"
end ThermalExteriorTailAudit


end IntegratedScope03

namespace IntegratedScope04

/- Scoped semantic consumer; namespace/import-context adaptations are recorded in generation-manifest.json. -/


open Set MeasureTheory RepulsiveCoulomb RepulsiveCoulomb.PaperRoute
open scoped BigOperators

example {r α : ℝ} (hr : 0 ≤ r) (hα : 0 < α) :
    r ^ α * max (-Real.log r) 0 ≤ 1 / α :=
  paper_rpow_positive_log_bound hr hα

example {β : ℝ} (hβ : 0 < β) :
    Integrable (fun z : CoulombConfig 2 => equilibriumLogPositive (z 0 - z 1))
      (coulombMeasure 2 β) := paper_coulomb_pair_positive_log_integrable hβ 0 1

example {μ : Measure ℂ} [IsProbabilityMeasure μ] {f : ℂ → ℝ}
    (hm : Measurable f) (hi : Integrable (fun x => Real.exp (f x)) μ) :
    (∫ x, Real.exp (f x / 2) ∂μ) ≤ (∫ x, Real.exp (f x) ∂μ) ^ (1 / 2 : ℝ) := by
  simpa using paper_exp_integral_inverse_power_concavity hm hi (by norm_num : 0 < 2)

#check @paper_exp_div_nat_integrable
#print axioms paper_exp_div_nat_integrable
#check @paper_product_exp_average_power
#print axioms paper_product_exp_average_power
#check @paper_exp_integral_inverse_power_concavity
#print axioms paper_exp_integral_inverse_power_concavity
#check @paper_exp_integral_power_le
#print axioms paper_exp_integral_power_le
#check @paper_exp_integral_half_power_le
#print axioms paper_exp_integral_half_power_le
#check @paper_gibbs_defect_moment_product_power
#print axioms paper_gibbs_defect_moment_product_power
#check @paper_physical_gibbs_defect_moment_product_power
#print axioms paper_physical_gibbs_defect_moment_product_power
#check @paper_gibbs_defect_moment_via_concavity
#print axioms paper_gibbs_defect_moment_via_concavity
#check @paper_rpow_positive_log_bound
#print axioms paper_rpow_positive_log_bound
#check @paper_coulomb_positive_log_density_gaussian_bound
#print axioms paper_coulomb_positive_log_density_gaussian_bound
#check @paper_coulomb_positive_log_integrable_of_pair
#print axioms paper_coulomb_positive_log_integrable_of_pair
#check @paper_coulomb_pair_positive_log_integrable
#print axioms paper_coulomb_pair_positive_log_integrable
#check @paper_coulomb_pair_log_integrable
#print axioms paper_coulomb_pair_log_integrable
#check @paper_thermal_B_gibbs_integrable_positive_log
#print axioms paper_thermal_B_gibbs_integrable_positive_log
#check @paper_gibbs_defect_moment_of_oneBody
#print axioms paper_gibbs_defect_moment_of_oneBody
#check @paper_thermal_B_gibbs_integrable_polynomial
#print axioms paper_thermal_B_gibbs_integrable_polynomial
#check @paper_full_labeled_lsi_via_disk_reference
#print axioms paper_full_labeled_lsi_via_disk_reference
#check @paper_full_labeled_lsi_compact_via_disk_reference_family
#print axioms paper_full_labeled_lsi_compact_via_disk_reference_family
#check @paper_uniform_defectAt_compact_disk
#print axioms paper_uniform_defectAt_compact_disk

open Lean Elab Command in
private partial def visit (env : Environment) (n : Name) (authored : Bool := false) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env d authored
    if authored && n == ``RepulsiveCoulomb.PaperRoute.paper_dg_fixed_coupling then return
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env d authored

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := #[``RepulsiveCoulomb.PaperRoute.paper_exp_div_nat_integrable, ``RepulsiveCoulomb.PaperRoute.paper_product_exp_average_power, ``RepulsiveCoulomb.PaperRoute.paper_exp_integral_inverse_power_concavity, ``RepulsiveCoulomb.PaperRoute.paper_exp_integral_power_le, ``RepulsiveCoulomb.PaperRoute.paper_exp_integral_half_power_le, ``RepulsiveCoulomb.PaperRoute.paper_gibbs_defect_moment_product_power, ``RepulsiveCoulomb.PaperRoute.paper_physical_gibbs_defect_moment_product_power, ``RepulsiveCoulomb.PaperRoute.paper_gibbs_defect_moment_via_concavity, ``RepulsiveCoulomb.PaperRoute.paper_rpow_positive_log_bound, ``RepulsiveCoulomb.PaperRoute.paper_coulomb_positive_log_density_gaussian_bound, ``RepulsiveCoulomb.PaperRoute.paper_coulomb_positive_log_integrable_of_pair, ``RepulsiveCoulomb.PaperRoute.paper_coulomb_pair_positive_log_integrable, ``RepulsiveCoulomb.PaperRoute.paper_coulomb_pair_log_integrable, ``RepulsiveCoulomb.PaperRoute.paper_thermal_B_gibbs_integrable_positive_log, ``RepulsiveCoulomb.PaperRoute.paper_gibbs_defect_moment_of_oneBody, ``RepulsiveCoulomb.PaperRoute.paper_thermal_B_gibbs_integrable_polynomial, ``RepulsiveCoulomb.PaperRoute.paper_full_labeled_lsi_via_disk_reference, ``RepulsiveCoulomb.PaperRoute.paper_full_labeled_lsi_compact_via_disk_reference_family, ``RepulsiveCoulomb.PaperRoute.paper_uniform_defectAt_compact_disk]
  let (_, deps) := (roots.forM (fun n => visit env n)).run ({} : NameSet)
  for n in deps do
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
  for n in #[`RepulsiveCoulomb.equilibriumConstructedReference,
      `RepulsiveCoulomb.equilibriumConstructedReference_nonempty,
      `RepulsiveCoulomb.equilibriumCanonical_exists_global_minimizer,
      `RepulsiveCoulomb.equilibrium_pointwise_EL_contDiff,
      `RepulsiveCoulomb.equilibriumReference_gibbs_defect_moment,
      `RepulsiveCoulomb.equilibriumReference_physical_gibbs_defect_moment,
      `RepulsiveCoulomb.conditionalEntropyBranch_defect_exp_integrable,
      `RepulsiveCoulomb.conditionalEntropyBranch_defect_nonneg,
      `RepulsiveCoulomb.equilibriumReferencePartition_uniform,
      `RepulsiveCoulomb.equilibriumConstructedReference_partition_uniform,
      `RepulsiveCoulomb.PaperRoute.paper_full_labeled_lsi_via_spatial_reference,
      `RepulsiveCoulomb.PaperRoute.paper_normalized_core_defective,
      `RepulsiveCoulomb.PaperRoute.paper_uniform_defect_nonneg,
      `RepulsiveCoulomb.PaperRoute.paper_full_defective_of_reference_bounds,
      `RepulsiveCoulomb.pointDilationBranchCwt,
      `RepulsiveCoulomb.pointDilationBranchRhoWt,
      `RepulsiveCoulomb.pointDilationBranchCrel] do
    if deps.contains n then throwError "Forbidden selected old producer in full closure: {n}"
  for n in deps do
    if n.toString.startsWith "RepulsiveCoulomb.coulomb_named_" ||
        n.toString.startsWith "RepulsiveCoulomb.pointDilationBranch_named_" then
      throwError "Forbidden old named endpoint: {n}"
  let (_, authored) := (roots.forM (fun n => visit env n true)).run ({} : NameSet)
  for n in #[`RepulsiveCoulomb.equilibriumConstructedReference,
      `RepulsiveCoulomb.equilibriumConstructedReference_nonempty,
      `RepulsiveCoulomb.equilibriumCanonical_exists_global_minimizer,
      `RepulsiveCoulomb.equilibriumReference_physical_gibbs_defect_moment,
      `RepulsiveCoulomb.equilibriumReference_gibbs_defect_moment,
      `RepulsiveCoulomb.equilibriumProduct_exp_average,
      `RepulsiveCoulomb.equilibriumLogKernel_zeroMass_nonneg,
      `RepulsiveCoulomb.equilibriumReference_modulated_exp_integrable,
      `RepulsiveCoulomb.equilibriumReferencePartition_lower,
      `RepulsiveCoulomb.equilibriumReferencePartition_pos,
      `RepulsiveCoulomb.conditionalEntropyBranch_B_gibbs_integrable,
      `RepulsiveCoulomb.conditionalEntropyBranch_B_core_integrable,
      `RepulsiveCoulomb.conditionalEntropyBranch_defect_exp_integrable,
      `RepulsiveCoulomb.equilibriumReference_exp_elConstant_le,
      `RepulsiveCoulomb.equilibriumReference_tail_prefactor_bound,
      `RepulsiveCoulomb.equilibriumReference_uniform_envelope,
      `RepulsiveCoulomb.equilibriumReference_potential_exponential_bound,
      `RepulsiveCoulomb.equilibriumReference_polynomial_moment_bound,
      `RepulsiveCoulomb.PaperRoute.paper_reference_gibbs_energy_exp_integrable_polynomial,
      `RepulsiveCoulomb.PaperRoute.paper_reference_gibbs_energy_integrable_polynomial] do
    if authored.contains n then throwError "Forbidden old or alternate authored producer: {n}"
  for root in #[``paper_full_labeled_lsi_via_disk_reference,
      ``paper_full_labeled_lsi_compact_via_disk_reference_family,
      ``paper_uniform_defectAt_compact_disk] do
    let (_, used) := (visit env root true).run ({} : NameSet)
    for n in #[``paper_gibbs_defect_moment_product_power,
        ``paper_gibbs_defect_moment_via_concavity,
        ``paper_product_exp_average_power,
        ``paper_exp_integral_inverse_power_concavity,
        ``Real.concaveOn_rpow,
        ``ConcaveOn.le_map_integral,
        ``paper_thermal_B_gibbs_integrable_positive_log,
        ``paper_coulomb_positive_log_density_gaussian_bound,
        ``paper_rpow_positive_log_bound,
        ``RepulsiveCoulomb.coulombDensity_le_gaussian_collision_power] do
      unless used.contains n do throwError "Required authored producer absent from {root}: {n}"
  logInfo m!"PASS: {roots.size} declaration roots; exact product-power and concavity and retained collision-power log proofs selected by fixed/compact LSI and all-ell defect; type/opaque-body audit; standard axioms only."


end IntegratedScope04

namespace IntegratedScope05

/- Scoped semantic consumer; namespace/import-context adaptations are recorded in generation-manifest.json. -/

open Set MeasureTheory RepulsiveCoulomb RepulsiveCoulomb.PaperRoute

example {β : ℝ} (hβ : 0 < β) :
    0 < poleBranchOptimalLSIParticleRealInf hβ := paper_original_particle_optimal_inf_pos hβ

example {a : ℝ} (ha : 0 < a) :
    0 < poleBranchOptimalLSIRealInfOn (Set.Icc a a) (fun _ hβ => ha.trans_le hβ.1) :=
  (paper_original_compact_optimal_double_inf_pos ha le_rfl).2

example {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (β : Set.Icc a b) :
    paperOriginalCompactLabeledRate (b := b) ha ≤
      poleBranchOptimalLSIRate 2 (ha.trans_le β.2.1) :=
  paperOriginalCompactLabeledRate_le_optimal ha hab β 2 le_rfl

#check @paperOriginalLabeledRate_le_optimal
#print axioms paperOriginalLabeledRate_le_optimal
#check @paperOriginalLabeledRate_le_particle_inf
#print axioms paperOriginalLabeledRate_le_particle_inf
#check @paper_original_particle_optimal_inf_pos
#print axioms paper_original_particle_optimal_inf_pos
#check @paperOriginalCompactLabeledRate_le_optimal
#print axioms paperOriginalCompactLabeledRate_le_optimal
#check @paper_original_compact_optimal_double_inf_lower
#print axioms paper_original_compact_optimal_double_inf_lower
#check @paper_original_compact_optimal_real_double_inf_lower
#print axioms paper_original_compact_optimal_real_double_inf_lower
#check @paper_original_compact_optimal_double_inf_pos
#print axioms paper_original_compact_optimal_double_inf_pos
open Lean Elab Command in
private partial def visit (env : Environment) (n : Name) (authored : Bool := false) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env d authored
    if authored && n == ``RepulsiveCoulomb.PaperRoute.paper_dg_fixed_coupling then return
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env d authored

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := #[``RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate_le_optimal, ``RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate_le_particle_inf, ``RepulsiveCoulomb.PaperRoute.paper_original_particle_optimal_inf_pos, ``RepulsiveCoulomb.PaperRoute.paperOriginalCompactLabeledRate_le_optimal, ``RepulsiveCoulomb.PaperRoute.paper_original_compact_optimal_double_inf_lower, ``RepulsiveCoulomb.PaperRoute.paper_original_compact_optimal_real_double_inf_lower, ``RepulsiveCoulomb.PaperRoute.paper_original_compact_optimal_double_inf_pos]
  let (_, deps) := (roots.forM (fun n => visit env n)).run ({} : NameSet)
  for n in deps do
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
  for n in #[`RepulsiveCoulomb.equilibriumConstructedReference,
      `RepulsiveCoulomb.equilibriumConstructedReference_nonempty,
      `RepulsiveCoulomb.equilibriumCanonical_exists_global_minimizer,
      `RepulsiveCoulomb.equilibrium_pointwise_EL_contDiff,
      `RepulsiveCoulomb.equilibriumReference_gibbs_defect_moment,
      `RepulsiveCoulomb.equilibriumReference_physical_gibbs_defect_moment,
      `RepulsiveCoulomb.conditionalEntropyBranch_defect_exp_integrable,
      `RepulsiveCoulomb.conditionalEntropyBranch_defect_nonneg,
      `RepulsiveCoulomb.equilibriumReferencePartition_uniform,
      `RepulsiveCoulomb.equilibriumConstructedReference_partition_uniform,
      `RepulsiveCoulomb.PaperRoute.paper_full_labeled_lsi_via_spatial_reference,
      `RepulsiveCoulomb.PaperRoute.paper_normalized_core_defective,
      `RepulsiveCoulomb.PaperRoute.paper_uniform_defect_nonneg,
      `RepulsiveCoulomb.PaperRoute.paper_full_defective_of_reference_bounds,
      `RepulsiveCoulomb.pointDilationBranchCwt,
      `RepulsiveCoulomb.pointDilationBranchRhoWt,
      `RepulsiveCoulomb.pointDilationBranchCrel] do
    if deps.contains n then throwError "Forbidden selected old producer in full closure: {n}"
  for n in deps do
    if n.toString.startsWith "RepulsiveCoulomb.coulomb_named_" ||
        n.toString.startsWith "RepulsiveCoulomb.pointDilationBranch_named_" then
      throwError "Forbidden old named endpoint: {n}"
  let (_, authored) := (roots.forM (fun n => visit env n true)).run ({} : NameSet)
  for n in #[`RepulsiveCoulomb.equilibriumConstructedReference,
      `RepulsiveCoulomb.equilibriumConstructedReference_nonempty,
      `RepulsiveCoulomb.equilibriumCanonical_exists_global_minimizer,
      `RepulsiveCoulomb.equilibriumReference_physical_gibbs_defect_moment,
      `RepulsiveCoulomb.equilibriumReference_gibbs_defect_moment,
      `RepulsiveCoulomb.equilibriumProduct_exp_average,
      `RepulsiveCoulomb.equilibriumLogKernel_zeroMass_nonneg,
      `RepulsiveCoulomb.equilibriumReference_modulated_exp_integrable,
      `RepulsiveCoulomb.equilibriumReferencePartition_lower,
      `RepulsiveCoulomb.equilibriumReferencePartition_pos,
      `RepulsiveCoulomb.conditionalEntropyBranch_B_gibbs_integrable,
      `RepulsiveCoulomb.conditionalEntropyBranch_B_core_integrable,
      `RepulsiveCoulomb.conditionalEntropyBranch_defect_exp_integrable,
      `RepulsiveCoulomb.equilibriumReference_exp_elConstant_le,
      `RepulsiveCoulomb.equilibriumReference_tail_prefactor_bound,
      `RepulsiveCoulomb.equilibriumReference_uniform_envelope,
      `RepulsiveCoulomb.equilibriumReference_potential_exponential_bound,
      `RepulsiveCoulomb.equilibriumReference_polynomial_moment_bound,
      `RepulsiveCoulomb.PaperRoute.paper_reference_gibbs_energy_exp_integrable_polynomial,
      `RepulsiveCoulomb.PaperRoute.paper_reference_gibbs_energy_integrable_polynomial] do
    if authored.contains n then throwError "Forbidden old or alternate authored producer: {n}"
  for root in #[``paper_original_particle_optimal_inf_pos,
      ``paper_original_compact_optimal_double_inf_pos] do
    let (_, used) := (visit env root true).run ({} : NameSet)
    for n in #[``paper_gibbs_defect_moment_product_power,
        ``paper_exp_integral_inverse_power_concavity,
        ``paper_thermal_B_gibbs_integrable_positive_log,
        ``thermalConstructedReference,
        ``RepulsiveCoulomb.poleBranch_admissible_le_optimalLSIRate,
        ``RepulsiveCoulomb.poleBranchLSIRates_bddAbove] do
      unless used.contains n do throwError "Required original-input/actual-optimum producer absent: {root}: {n}"
  let (_, compact) := (visit env ``paper_original_compact_optimal_double_inf_pos true).run ({} : NameSet)
  for n in #[``paper_uniform_labeled_lsi_original,
      ``paper_full_labeled_lsi_compact_via_disk_reference_family,
      ``RepulsiveCoulomb.poleBranchOptimalLSIInfOn_ge_common_rate,
      ``RepulsiveCoulomb.poleBranchOptimalLSIInfOn_eq_real,
      ``paperCompactEntropyDefect] do
    unless compact.contains n do throwError "Required literal compact-infimum producer absent: {n}"
  logInfo m!"PASS: {roots.size} actual-optimal-rate roots; three examples; original-input physical LSI and exact real/extended double infima; type/opaque-body audit and standard axioms."


end IntegratedScope05

namespace IntegratedScope06

/- Scoped semantic consumer; namespace/import-context adaptations are recorded in generation-manifest.json. -/

open Set MeasureTheory RepulsiveCoulomb RepulsiveCoulomb.PaperRoute

example {β : ℝ} (hβ : 0 < β) :
    coulombVariationalOneCapacity 0 hβ (coulombCollisionSet 0) = 0 :=
  paper_original_collision_capacity 0 hβ
example {β : ℝ} (hβ : 0 < β) :
    coulombVariationalOneCapacity 1 hβ (coulombCollisionSet 1) = 0 :=
  paper_original_collision_capacity 1 hβ
example {β : ℝ} (hβ : 0 < β) :
    coulombVariationalOneCapacity 2 hβ (coulombCollisionSet 2) = 0 :=
  paper_original_collision_capacity 2 hβ
example {β : ℝ} (hβ : 0 < β) :
    poleBranchOptimalLSIRate 2 hβ = min β (coulombHelmertRelativeOptimalLSIRateReal 0 hβ) := by
  simpa using paper_original_center_mass_optimal_rate 2 le_rfl hβ

#check @paper_original_collision_capacity
#print axioms paper_original_collision_capacity
#check @paper_original_collision_capacity_and_common_core
#print axioms paper_original_collision_capacity_and_common_core
#check @paper_original_capacity_open_neighborhood
#print axioms paper_original_capacity_open_neighborhood
#check @paper_original_capacity_physical_cost
#print axioms paper_original_capacity_physical_cost
#check @paper_original_center_mass
#print axioms paper_original_center_mass
#check @paper_original_center_mass_optimal_rate
#print axioms paper_original_center_mass_optimal_rate
#check @paper_original_helmert_center
#print axioms paper_original_helmert_center
#check @paper_original_helmert_relative
#print axioms paper_original_helmert_relative
#check @paper_original_helmert_unitary
#print axioms paper_original_helmert_unitary

open Lean Elab Command in
private partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env d
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env d

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := #[``RepulsiveCoulomb.PaperRoute.paper_original_collision_capacity, ``RepulsiveCoulomb.PaperRoute.paper_original_collision_capacity_and_common_core, ``RepulsiveCoulomb.PaperRoute.paper_original_capacity_open_neighborhood, ``RepulsiveCoulomb.PaperRoute.paper_original_capacity_physical_cost, ``RepulsiveCoulomb.PaperRoute.paper_original_center_mass, ``RepulsiveCoulomb.PaperRoute.paper_original_center_mass_optimal_rate, ``RepulsiveCoulomb.PaperRoute.paper_original_helmert_center, ``RepulsiveCoulomb.PaperRoute.paper_original_helmert_relative, ``RepulsiveCoulomb.PaperRoute.paper_original_helmert_unitary]
  let (_, deps) := (roots.forM (visit env)).run ({} : NameSet)
  for n in deps do
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
    if n.toString.startsWith "RepulsiveCoulomb.coulomb_named_" ||
        n.toString.startsWith "RepulsiveCoulomb.pointDilationBranch_named_" then
      throwError "Forbidden old named endpoint: {n}"
  for n in #[`RepulsiveCoulomb.equilibriumConstructedReference,
      `RepulsiveCoulomb.equilibriumConstructedReference_nonempty,
      `RepulsiveCoulomb.equilibriumCanonical_exists_global_minimizer,
      `RepulsiveCoulomb.equilibriumReference_gibbs_defect_moment,
      `RepulsiveCoulomb.equilibriumReferencePartition_uniform,
      `RepulsiveCoulomb.equilibriumLogKernel_zeroMass_nonneg,
      `RepulsiveCoulomb.pointDilationBranchCwt,
      `RepulsiveCoulomb.pointDilationBranchRhoWt,
      `RepulsiveCoulomb.pointDilationBranchCrel] do
    if deps.contains n then throwError "Forbidden selected old route: {n}"
  let (_, capacity) := (visit env ``paper_original_collision_capacity_and_common_core).run ({} : NameSet)
  for n in #[``coulombVariationalOneCapacity,
      ``coulombCapacityAdmissible,
      ``coulombVariationalOneCapacity_zero_of_tendsto,
      ``coulomb_constant_sub_core_capacity_admissible,
      ``coulomb_common_core] do
    unless capacity.contains n do throwError "Required physical capacity/common-core producer absent: {n}"
  let (_, com) := (visit env ``paper_original_center_mass).run ({} : NameSet)
  for n in #[``coulombCenter_factorization_explicit,
      ``coulombCenter_relative_common_core,
      ``coulombCenter_admissible_iff_factor_cores,
      ``coulombCenterGaussian_core_lsi_iff,
      ``coulombCenterRelative_full_iff_core,
      ``coulombCenterRelativeRates_bddAbove,
      ``coulombCenterRelativeOptimalRate_eq_ofReal,
      ``coulombCenter_optimal_rate_min,
      ``poleBranchLSIRates_bddAbove] do
    unless com.contains n do throwError "Required actual COM factorization/optimality producer absent: {n}"
  logInfo m!"PASS: {roots.size} standalone declaration roots, four edge-case consumers, full type/opaque-body traversal, standard axioms, genuine physical capacity/common-core and COM/optimal LSI factorization."


end IntegratedScope06

namespace IntegratedScope07

/- Scoped semantic consumer; namespace/import-context adaptations are recorded in generation-manifest.json. -/

open Set MeasureTheory ProbabilityTheory RepulsiveCoulomb RepulsiveCoulomb.PaperRoute

-- N=2, unit-droplet beta=4: literal attained real center mode.
example : ∃ u : CoulombFormDomain 2 (by norm_num : (0 : ℝ) < 4),
    coulombFormValueL 2 (by norm_num : (0 : ℝ) < 4) u =ᵐ[coulombMeasure 2 4]
      (fun z => (paperCenterOfMass 0 z).re) ∧
    (∀ σ : Equiv.Perm (Fin 2),
      coulombValuePermuteL 2 (by norm_num : (0 : ℝ) < 4) σ (coulombFormValueL 2 (by norm_num : (0 : ℝ) < 4) u) =
        coulombFormValueL 2 (by norm_num : (0 : ℝ) < 4) u) ∧
    (∫ z, coulombFormValueL 2 (by norm_num : (0 : ℝ) < 4) u z ∂coulombMeasure 2 4) = 0 ∧
    variance (coulombFormValueL 2 (by norm_num : (0 : ℝ) < 4) u : CoulombConfig 2 → ℝ)
      (coulombMeasure 2 4) = 1 / 4 ∧ coulombFormEnergy 2 (by norm_num : (0 : ℝ) < 4) u = 1 :=
  paper_center_real_form_witness 0 (by norm_num : (0 : ℝ) < 4)

-- Both actual symmetric modes are attained at every Ginibre particle count.
example (m : ℕ) := paper_ginibre_center_equality_witnesses m

-- The arbitrary-N sharpness endpoint specializes to two particles.
example (C : ℝ) :
    (∀ u : CoulombFormDomain 2 (by norm_num : (0 : ℝ) < 2 * (2 : ℝ)),
      (∀ σ : Equiv.Perm (Fin 2),
        coulombValuePermuteL 2 (by norm_num : (0 : ℝ) < 2 * (2 : ℝ)) σ (coulombFormValueL 2 (by norm_num : (0 : ℝ) < 2 * (2 : ℝ)) u) =
          coulombFormValueL 2 (by norm_num : (0 : ℝ) < 2 * (2 : ℝ)) u) →
      variance (coulombFormValueL 2 (by norm_num : (0 : ℝ) < 2 * (2 : ℝ)) u : CoulombConfig 2 → ℝ)
        (coulombMeasure 2 (2 * (2 : ℝ))) ≤ C * coulombFormEnergy 2 (by norm_num : (0 : ℝ) < 2 * (2 : ℝ)) u) ↔ 1 / (2 * (2 : ℝ)) ≤ C := by
  exact paper_ginibre_symmetric_poincare_sharp_all_N 2 le_rfl C

-- Exact one-coordinate second moments at beta=4, independently of any LSI.
example : (∫ c : ℂ, c.re ^ 2 ∂coulombCenterGaussian 4) = 1 / 4 := by
  simpa [Complex.inner] using paper_gaussian_linear_second_moment (by norm_num : (0 : ℝ) < 4) (1 : ℂ)
example : (∫ c : ℂ, c.im ^ 2 ∂coulombCenterGaussian 4) = 1 / 4 := by
  simpa [Complex.inner, Complex.mul_re] using
    paper_gaussian_linear_second_moment (by norm_num : (0 : ℝ) < 4) Complex.I

#check @paper_gaussian_linear_memLp
#print axioms paper_gaussian_linear_memLp
#check @paper_gaussian_linear_mean
#print axioms paper_gaussian_linear_mean
#check @paper_gaussian_linear_second_moment
#print axioms paper_gaussian_linear_second_moment
#check @paper_smooth_L2_cutoff_value
#print axioms paper_smooth_L2_cutoff_value
#check @paper_smooth_L2_cutoff_gradient
#print axioms paper_smooth_L2_cutoff_gradient
#check @paper_smooth_L2_bounded_gradient_lift
#print axioms paper_smooth_L2_bounded_gradient_lift
#check @paperCenterOfMass_formula
#print axioms paperCenterOfMass_formula
#check @paperCenterOfMass_permute
#print axioms paperCenterOfMass_permute
#check @paperCenterLinearObservable_contDiff
#print axioms paperCenterLinearObservable_contDiff
#check @paper_linear_gradient
#print axioms paper_linear_gradient
#check @paperCenterLinearObservable_gradient
#print axioms paperCenterLinearObservable_gradient
#check @paperCenterLinearObservable_gradient_norm
#print axioms paperCenterLinearObservable_gradient_norm
#check @paperCenterLinearObservable_memLp
#print axioms paperCenterLinearObservable_memLp
#check @paperCenterLinearObservable_mean
#print axioms paperCenterLinearObservable_mean
#check @paperCenterLinearObservable_second_moment
#print axioms paperCenterLinearObservable_second_moment
#check @paper_center_linear_form_witness
#print axioms paper_center_linear_form_witness
#check @paper_center_real_form_witness
#print axioms paper_center_real_form_witness
#check @paper_center_imaginary_form_witness
#print axioms paper_center_imaginary_form_witness
#check @paper_symmetric_poincare_coefficient_lower_bound
#print axioms paper_symmetric_poincare_coefficient_lower_bound
#check @paper_ginibre_symmetric_poincare
#print axioms paper_ginibre_symmetric_poincare
#check @paper_ginibre_symmetric_poincare_iff
#print axioms paper_ginibre_symmetric_poincare_iff
#check @paper_ginibre_symmetric_poincare_sharp_all_N
#print axioms paper_ginibre_symmetric_poincare_sharp_all_N
#check @paper_ginibre_center_equality_witnesses
#print axioms paper_ginibre_center_equality_witnesses

open Lean Elab Command in
private partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env d
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env d

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := #[``RepulsiveCoulomb.PaperRoute.paper_gaussian_linear_memLp, ``RepulsiveCoulomb.PaperRoute.paper_gaussian_linear_mean, ``RepulsiveCoulomb.PaperRoute.paper_gaussian_linear_second_moment, ``RepulsiveCoulomb.PaperRoute.paper_smooth_L2_cutoff_value, ``RepulsiveCoulomb.PaperRoute.paper_smooth_L2_cutoff_gradient, ``RepulsiveCoulomb.PaperRoute.paper_smooth_L2_bounded_gradient_lift, ``RepulsiveCoulomb.PaperRoute.paperCenterOfMass_formula, ``RepulsiveCoulomb.PaperRoute.paperCenterOfMass_permute, ``RepulsiveCoulomb.PaperRoute.paperCenterLinearObservable_contDiff, ``RepulsiveCoulomb.PaperRoute.paper_linear_gradient, ``RepulsiveCoulomb.PaperRoute.paperCenterLinearObservable_gradient, ``RepulsiveCoulomb.PaperRoute.paperCenterLinearObservable_gradient_norm, ``RepulsiveCoulomb.PaperRoute.paperCenterLinearObservable_memLp, ``RepulsiveCoulomb.PaperRoute.paperCenterLinearObservable_mean, ``RepulsiveCoulomb.PaperRoute.paperCenterLinearObservable_second_moment, ``RepulsiveCoulomb.PaperRoute.paper_center_linear_form_witness, ``RepulsiveCoulomb.PaperRoute.paper_center_real_form_witness, ``RepulsiveCoulomb.PaperRoute.paper_center_imaginary_form_witness, ``RepulsiveCoulomb.PaperRoute.paper_symmetric_poincare_coefficient_lower_bound, ``RepulsiveCoulomb.PaperRoute.paper_ginibre_symmetric_poincare, ``RepulsiveCoulomb.PaperRoute.paper_ginibre_symmetric_poincare_iff, ``RepulsiveCoulomb.PaperRoute.paper_ginibre_symmetric_poincare_sharp_all_N, ``RepulsiveCoulomb.PaperRoute.paper_ginibre_center_equality_witnesses]
  let (_, deps) := (roots.forM (visit env)).run ({} : NameSet)
  for n in deps do
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
    if n.toString.startsWith "RepulsiveCoulomb.coulomb_named_" ||
        n.toString.startsWith "RepulsiveCoulomb.pointDilationBranch_named_" then
      throwError "Forbidden old named endpoint: {n}"
  for n in #[`RepulsiveCoulomb.pointDilationBranchP1,
      `RepulsiveCoulomb.pointDilationBranchK1,
      `RepulsiveCoulomb.pointDilationBranchCwt,
      `RepulsiveCoulomb.pointDilationBranchRhoWt,
      `RepulsiveCoulomb.pointDilationBranchCrel,
      `RepulsiveCoulomb.equilibriumConstructedReference,
      `RepulsiveCoulomb.equilibriumCanonical_exists_global_minimizer] do
    if deps.contains n then throwError "Forbidden selected old route: {n}"
  let (_, witness) := (visit env ``paper_ginibre_center_equality_witnesses).run ({} : NameSet)
  for n in #[``paper_center_real_form_witness,
      ``paper_center_imaginary_form_witness,
      ``paper_center_linear_form_witness,
      ``paper_smooth_L2_bounded_gradient_lift,
      ``paper_smooth_L2_cutoff_value,
      ``paper_smooth_L2_cutoff_gradient,
      ``paper_gaussian_linear_second_moment,
      ``coulombAmbientJet_mem_closedCore,
      ``coulombCenterProjection_measurePreserving,
      ``paperCenterOfMass_permute,
      ``coulombGaussianDensity_fderiv,
      ``integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable,
      ``paperCenterLinearObservable_gradient] do
    unless witness.contains n do throwError "Required actual center-witness producer absent: {n}"
  for n in #[`RepulsiveCoulomb.coulombCenterGaussian_core_lsi,
      `RepulsiveCoulomb.coulombCenterGaussian_core_lsi_iff,
      `RepulsiveCoulomb.coulombCenterGaussian_core_lsi_rate_le,
      `RepulsiveCoulomb.coulombGaussian_core_lsi_of_positive_fisher,
      `RepulsiveCoulomb.poleBranchOptimalLSIRate,
      `RepulsiveCoulomb.coulombCenter_optimal_rate_min,
      `RepulsiveCoulomb.coulombGaussianExponentialWitness_rate_le,
      `RepulsiveCoulomb.coulombGaussianExponentialWitness_energy,
      `RepulsiveCoulomb.coulombGaussianExponentialWitness_entropy] do
    if deps.contains n then throwError "Gaussian LSI/optimal-rate route substituted in Ginibre proof: {n}"
  let (_, sharp) := (visit env ``paper_ginibre_symmetric_poincare_sharp_all_N).run ({} : NameSet)
  for n in #[``paper_symmetric_poincare_small_exponent,
      ``paper_symmetric_poincare_coefficient_lower_bound,
      ``paper_center_real_form_witness,
      ``coulombFormValueL,
      ``coulombFormEnergy,
      ``coulombFormEnergy_eq_integral,
      ``coulombFormSubmodule] do
    unless sharp.contains n do throwError "Sharp symmetric PI lost a required upper/lower producer: {n}"
  logInfo m!"PASS: {roots.size} Ginibre roots, five concrete consumers, full type/opaque-body audit, standard axioms, literal real/imaginary closed-form witnesses, exact symmetric coefficient 1/(2N)."


end IntegratedScope07

namespace IntegratedScope08

/- Scoped semantic consumer; namespace/import-context adaptations are recorded in generation-manifest.json. -/


open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology ContDiff Convolution
open RepulsiveCoulomb RepulsiveCoulomb.PaperRoute

example {f : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (n : ℕ) (x : ℂ) :
    fderiv ℝ (lipschitzMollify f n) x =
      ((lipschitzSmoothingKernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ f) x) :=
  lipschitzMollify_fderiv hf n x

example {f : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    ∀ᵐ x : ℂ, Tendsto (fun n => fderiv ℝ (lipschitzMollify f n) x) atTop (𝓝 (fderiv ℝ f x)) :=
  lipschitzMollify_fderiv_ae_tendsto hf

example {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ν ≪ volume)
    {f : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    Tendsto (fun n => ⨍ x, ‖fderiv ℝ (lipschitzMollify f n) x‖ ^ 2 ∂ν)
      atTop (𝓝 (⨍ x, ‖fderiv ℝ f x‖ ^ 2 ∂ν)) :=
  lipschitzMollify_energy_tendsto hν hf

example {Q : ℝ} {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {f : ℂ → ℝ} (hf : LocallyLipschitz f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ^
      (2 * originalGaussianKappa Q) ∂rawPointMeasure a y) ^ (1 / (2 * originalGaussianKappa Q)) ≤
      Real.sqrt (originalRawSobolevConstant Q) * R *
        Real.sqrt (⨍ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y) :=
  original_raw_local_sobolev_locallyLipschitz ha hQ y hf c hR

example {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {f : ℂ → ℝ} (hf : LocallyLipschitz f) {R : ℝ} (hR : 1 ≤ R) :
    (⨍ x in ball (0 : ℂ) R,
      ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^
        (2 * originalGaussianKappa Q) ∂pointMeasure γ a y) ^ (1 / (2 * originalGaussianKappa Q)) ≤
      gaussianLocalConstant γ (originalGaussianKappa Q) (originalRawSobolevConstant Q) *
        Real.exp (gaussianLocalConstant γ (originalGaussianKappa Q) (originalRawSobolevConstant Q) * R ^ 2) * R *
        Real.sqrt (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y) :=
  original_gaussian_local_sobolev_locallyLipschitz hγ ha hQ y hf hR

example {Q : ℝ} {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball c R, ‖‖x‖ - (⨍ z in ball c R, ‖z‖ ∂rawPointMeasure a y)‖ ^
      (2 * originalGaussianKappa Q) ∂rawPointMeasure a y) ^ (1 / (2 * originalGaussianKappa Q)) ≤
      Real.sqrt (originalRawSobolevConstant Q) * R *
        Real.sqrt (⨍ x in ball c (11 * R), ‖gradient (fun z : ℂ => ‖z‖) x‖ ^ 2 ∂rawPointMeasure a y) :=
  original_raw_local_sobolev_locallyLipschitz ha hQ y lipschitzWith_one_norm.locallyLipschitz c hR
example {Q : ℝ} {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {f : ℂ → ℝ} (hf : LocallyLipschitz f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ^
      (2 * originalGaussianKappa Q) ∂rawPointMeasure a y) ^ (1 / originalGaussianKappa Q) ≤
      originalRawSobolevConstant Q * R ^ 2 *
        (⨍ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y) :=
  original_raw_strong_sobolev_locallyLipschitz ha hQ y hf c hR

#check RepulsiveCoulomb.PaperRoute.lipschitzSmoothingScale
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzSmoothingScale
#check RepulsiveCoulomb.PaperRoute.lipschitzSmoothingScale_pos
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzSmoothingScale_pos
#check RepulsiveCoulomb.PaperRoute.lipschitzSmoothingScale_le_one
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzSmoothingScale_le_one
#check RepulsiveCoulomb.PaperRoute.lipschitzSmoothingScale_tendsto
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzSmoothingScale_tendsto
#check RepulsiveCoulomb.PaperRoute.lipschitzSmoothingBump
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzSmoothingBump
#check RepulsiveCoulomb.PaperRoute.lipschitzSmoothingKernel
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzSmoothingKernel
#check RepulsiveCoulomb.PaperRoute.lipschitzMollify
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzMollify
#check RepulsiveCoulomb.PaperRoute.lipschitzMollify_contDiff
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzMollify_contDiff
#check RepulsiveCoulomb.PaperRoute.lipschitzMollify_tendsto
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzMollify_tendsto
#check RepulsiveCoulomb.PaperRoute.lipschitzMollify_dist_le
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzMollify_dist_le
#check RepulsiveCoulomb.PaperRoute.lipschitz_fderiv_locallyIntegrable
#print axioms RepulsiveCoulomb.PaperRoute.lipschitz_fderiv_locallyIntegrable
#check RepulsiveCoulomb.PaperRoute.lipschitzMollify_hasFDerivAt
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzMollify_hasFDerivAt
#check RepulsiveCoulomb.PaperRoute.lipschitzMollify_fderiv
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzMollify_fderiv
#check RepulsiveCoulomb.PaperRoute.lipschitzMollify_fderiv_norm_le
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzMollify_fderiv_norm_le
#check RepulsiveCoulomb.PaperRoute.lipschitzMollify_fderiv_ae_tendsto
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzMollify_fderiv_ae_tendsto
#check RepulsiveCoulomb.PaperRoute.lipschitzMollify_norm_le
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzMollify_norm_le
#check RepulsiveCoulomb.PaperRoute.lipschitzMollify_mean_tendsto
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzMollify_mean_tendsto
#check RepulsiveCoulomb.PaperRoute.lipschitzMollify_centered_moment_tendsto
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzMollify_centered_moment_tendsto
#check RepulsiveCoulomb.PaperRoute.lipschitzMollify_energy_tendsto
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzMollify_energy_tendsto
#check RepulsiveCoulomb.PaperRoute.strong_sobolev_of_lipschitz
#print axioms RepulsiveCoulomb.PaperRoute.strong_sobolev_of_lipschitz
#check RepulsiveCoulomb.PaperRoute.strong_sobolev_on_balls_of_lipschitzOn
#print axioms RepulsiveCoulomb.PaperRoute.strong_sobolev_on_balls_of_lipschitzOn
#check RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_c1_center
#print axioms RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_c1_center
#check RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_closedBall
#print axioms RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_closedBall
#check RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_locallyLipschitz
#print axioms RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_locallyLipschitz
#check RepulsiveCoulomb.PaperRoute.original_raw_local_sobolev_locallyLipschitz
#print axioms RepulsiveCoulomb.PaperRoute.original_raw_local_sobolev_locallyLipschitz
#check RepulsiveCoulomb.PaperRoute.original_gaussian_strong_sobolev_closedBall
#print axioms RepulsiveCoulomb.PaperRoute.original_gaussian_strong_sobolev_closedBall
#check RepulsiveCoulomb.PaperRoute.original_gaussian_local_sobolev_locallyLipschitz
#print axioms RepulsiveCoulomb.PaperRoute.original_gaussian_local_sobolev_locallyLipschitz
namespace LipschitzSobolevAudit
open Lean Elab Command
partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env d
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env d
run_cmd do
  let env ← getEnv
  let roots := #[``RepulsiveCoulomb.PaperRoute.lipschitzSmoothingScale, ``RepulsiveCoulomb.PaperRoute.lipschitzSmoothingScale_pos, ``RepulsiveCoulomb.PaperRoute.lipschitzSmoothingScale_le_one, ``RepulsiveCoulomb.PaperRoute.lipschitzSmoothingScale_tendsto, ``RepulsiveCoulomb.PaperRoute.lipschitzSmoothingBump, ``RepulsiveCoulomb.PaperRoute.lipschitzSmoothingKernel, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_contDiff, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_tendsto, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_dist_le, ``RepulsiveCoulomb.PaperRoute.lipschitz_fderiv_locallyIntegrable, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_hasFDerivAt, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_fderiv, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_fderiv_norm_le, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_fderiv_ae_tendsto, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_norm_le, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_mean_tendsto, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_centered_moment_tendsto, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_energy_tendsto, ``RepulsiveCoulomb.PaperRoute.strong_sobolev_of_lipschitz, ``RepulsiveCoulomb.PaperRoute.strong_sobolev_on_balls_of_lipschitzOn, ``RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_c1_center, ``RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_closedBall, ``RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_locallyLipschitz, ``RepulsiveCoulomb.PaperRoute.original_raw_local_sobolev_locallyLipschitz, ``RepulsiveCoulomb.PaperRoute.original_gaussian_strong_sobolev_closedBall, ``RepulsiveCoulomb.PaperRoute.original_gaussian_local_sobolev_locallyLipschitz]
  let (_, allDeps) := (roots.forM (visit env)).run ({} : NameSet)
  for n in allDeps do
    if n == `sorryAx then throwError "Incomplete locally-Lipschitz proof: {n}"
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
  for n in #[`RepulsiveCoulomb.pointSobolevKappa,
      `RepulsiveCoulomb.rawPointMeasure_strong_sobolev_squared_norm,
      `RepulsiveCoulomb.rawPoint_uniform_local_sobolev_poincare,
      `RepulsiveCoulomb.pointGaussian_uniform_local_geometry,
      `RepulsiveCoulomb.pointCore_uniform_poincare,
      `RepulsiveCoulomb.pointCore_local_superPoincare,
      `RepulsiveCoulomb.pointCore_global_superPoincare,
      `RepulsiveCoulomb.pointCore_uniform_defective_lsi,
      `RepulsiveCoulomb.pointCore_uniform_tight_lsi,
      `RepulsiveCoulomb.pointMeasure_half_mass_ball,
      `RepulsiveCoulomb.pointCore_weighted_moment_bound,
      `RepulsiveCoulomb.pointDilationBranchP1, `RepulsiveCoulomb.pointDilationBranchK1,
      `RepulsiveCoulomb.equilibriumLogKernel_zeroMass_nonneg,
      `RepulsiveCoulomb.equilibriumConstructedReference] do
    if allDeps.contains n then throwError "Forbidden old local Sobolev/weighted/reference producer: {n}"
  logInfo m!"PASS: {roots.size} locally-Lipschitz declarations, full type and opaque proof traversal, standard axioms, no old local-Sobolev producer."
  for root in #[``original_raw_local_sobolev_locallyLipschitz,
      ``original_gaussian_local_sobolev_locallyLipschitz] do
    let (_, deps) := (visit env root).run ({} : NameSet)
    for n in #[``lipschitzMollify_hasFDerivAt, ``lipschitzMollify_fderiv,
        ``lipschitzMollify_fderiv_norm_le, ``lipschitzMollify_fderiv_ae_tendsto,
        ``lipschitzMollify_mean_tendsto, ``lipschitzMollify_centered_moment_tendsto,
        ``lipschitzMollify_energy_tendsto, ``strong_sobolev_of_lipschitz,
        ``strong_sobolev_on_balls_of_lipschitzOn,
        ``hasFDerivAt_integral_of_dominated_loc_of_lip,
        ``LipschitzWith.ae_differentiableAt,
        ``ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable,
        ``tendsto_integral_of_dominated_convergence,
        ``LipschitzOnWith.extend_real,
        ``original_point_localGeometry,
        ``strong_sobolev_squared_norm_of_dilation_two] do
      unless deps.contains n do throwError "Required actual approximation/geometry producer absent from {root}: {n}"
    for n in deps do
      if n.toString.startsWith "RepulsiveCoulomb." then logInfo m!"PROJECT_DEP {root}: {n}"
  logInfo "PASS: both original displays use actual derivative mollification, varying means, weighted energy convergence and exact closed-11-ball germ transfer, preserving constants and exponent."
end LipschitzSobolevAudit


end IntegratedScope08

namespace IntegratedScope09

/- Scoped semantic consumer; namespace/import-context adaptations are recorded in generation-manifest.json. -/

open Set MeasureTheory InformationTheory RepulsiveCoulomb RepulsiveCoulomb.PaperRoute

example {β : ℝ} (R : EquilibriumConstructedReference β) :
    paperUniformEntropyDefectAt R 2 = paperUniformEntropyDefect R := rfl

example {a b ℓ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hℓ : 1 < ℓ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ β : ℝ, a ≤ β → β ≤ b →
      ∀ R : EquilibriumConstructedReference β,
        0 ≤ paperUniformEntropyDefectAt R ℓ ∧
          paperUniformEntropyDefectAt R ℓ ≤ D ∧
          ∀ N : ℕ, 2 ≤ N → conditionalEntropyBranchDefect (N := N) R ℓ ≤
            paperUniformEntropyDefectAt R ℓ :=
  paper_uniform_defectAt_compact_disk ha hab hℓ

example {β : ℝ} (hβ : 0 < β) (R : EquilibriumConstructedReference β) :
    Integrable (fun z : CoulombConfig 2 => Real.exp
      (-(3 : ℝ) * β * conditionalEntropyBranchThermalB R z)) (coulombMeasure 2 β) :=
  paper_defect_exp_integrable_disk (by norm_num) hβ (by norm_num) R

#check @RepulsiveCoulomb.PaperRoute.paper_reference_partition_pair_compact_ell_via_spatial
#print axioms RepulsiveCoulomb.PaperRoute.paper_reference_partition_pair_compact_ell_via_spatial
#check @RepulsiveCoulomb.PaperRoute.paper_compact_reference_integral_bounds_ell_disk
#print axioms RepulsiveCoulomb.PaperRoute.paper_compact_reference_integral_bounds_ell_disk
#check @RepulsiveCoulomb.PaperRoute.paper_defect_exp_integrable_disk
#print axioms RepulsiveCoulomb.PaperRoute.paper_defect_exp_integrable_disk
#check @RepulsiveCoulomb.PaperRoute.paper_entropy_factorization_disk
#print axioms RepulsiveCoulomb.PaperRoute.paper_entropy_factorization_disk
#check @RepulsiveCoulomb.PaperRoute.paper_finite_defect_nonneg_disk
#print axioms RepulsiveCoulomb.PaperRoute.paper_finite_defect_nonneg_disk
#check @RepulsiveCoulomb.PaperRoute.paper_finite_defect_compact_uniform_disk
#print axioms RepulsiveCoulomb.PaperRoute.paper_finite_defect_compact_uniform_disk
#check @RepulsiveCoulomb.PaperRoute.paperUniformEntropyDefectAt
#print axioms RepulsiveCoulomb.PaperRoute.paperUniformEntropyDefectAt
#check @RepulsiveCoulomb.PaperRoute.paperUniformEntropyDefectAt_two
#print axioms RepulsiveCoulomb.PaperRoute.paperUniformEntropyDefectAt_two
#check @RepulsiveCoulomb.PaperRoute.paper_uniform_defectAt_compact_disk
#print axioms RepulsiveCoulomb.PaperRoute.paper_uniform_defectAt_compact_disk
#check @RepulsiveCoulomb.PaperRoute.paper_uniform_defectAt_finite_disk
#print axioms RepulsiveCoulomb.PaperRoute.paper_uniform_defectAt_finite_disk
open Lean Elab Command in
private partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env d
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env d

-- The exact supplied-reference DG theorem is a verified cited instance.
-- Its internal proof may reuse a valid older auxiliary envelope. The authored
-- thermal disk and entropy application are audited below this explicit boundary.
open Lean Elab Command in
private partial def visitAuthored (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visitAuthored env d
    if n == ``RepulsiveCoulomb.PaperRoute.paper_dg_fixed_coupling then return
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visitAuthored env d

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := #[``RepulsiveCoulomb.PaperRoute.paper_reference_partition_pair_compact_ell_via_spatial, ``RepulsiveCoulomb.PaperRoute.paper_compact_reference_integral_bounds_ell_disk, ``RepulsiveCoulomb.PaperRoute.paper_defect_exp_integrable_disk, ``RepulsiveCoulomb.PaperRoute.paper_entropy_factorization_disk, ``RepulsiveCoulomb.PaperRoute.paper_finite_defect_nonneg_disk, ``RepulsiveCoulomb.PaperRoute.paper_finite_defect_compact_uniform_disk, ``RepulsiveCoulomb.PaperRoute.paperUniformEntropyDefectAt, ``RepulsiveCoulomb.PaperRoute.paperUniformEntropyDefectAt_two, ``RepulsiveCoulomb.PaperRoute.paper_uniform_defectAt_compact_disk, ``RepulsiveCoulomb.PaperRoute.paper_uniform_defectAt_finite_disk]
  let (_, deps) := (roots.forM (visit env)).run ({} : NameSet)
  for n in #[`sorryAx,
      `RepulsiveCoulomb.equilibriumConstructedReference,
      `RepulsiveCoulomb.equilibriumConstructedReference_nonempty,
      `RepulsiveCoulomb.equilibriumCanonical_exists_global_minimizer,
      `RepulsiveCoulomb.equilibrium_pointwise_EL_contDiff,
      `RepulsiveCoulomb.equilibriumReference_gibbs_defect_moment,
      `RepulsiveCoulomb.equilibriumReference_physical_gibbs_defect_moment,
      `RepulsiveCoulomb.conditionalEntropyBranch_defect_exp_integrable,
      `RepulsiveCoulomb.conditionalEntropyBranch_defect_nonneg,
      `RepulsiveCoulomb.equilibriumReferencePartition_uniform,
      `RepulsiveCoulomb.equilibriumConstructedReference_partition_uniform,
      `RepulsiveCoulomb.PaperRoute.paper_full_labeled_lsi_via_spatial_reference,
      `RepulsiveCoulomb.PaperRoute.paper_normalized_core_defective,
      `RepulsiveCoulomb.PaperRoute.paper_uniform_defect_nonneg,
      `RepulsiveCoulomb.PaperRoute.paper_full_defective_of_reference_bounds,
      `RepulsiveCoulomb.pointDilationBranchCwt,
      `RepulsiveCoulomb.pointDilationBranchRhoWt,
      `RepulsiveCoulomb.pointDilationBranchCrel] do
    if deps.contains n then throwError "Forbidden selected old producer: {n}"
  let (_, authored) := (roots.forM (visitAuthored env)).run ({} : NameSet)
  for n in #[`RepulsiveCoulomb.equilibriumReference_exp_elConstant_le,
      `RepulsiveCoulomb.equilibriumReference_tail_prefactor_bound,
      `RepulsiveCoulomb.equilibriumReference_uniform_envelope,
      `RepulsiveCoulomb.equilibriumReference_potential_exponential_bound,
      `RepulsiveCoulomb.equilibriumReference_polynomial_moment_bound] do
    if authored.contains n then throwError "Old normalizer in authored route outside DG instance: {n}"
  logInfo m!"Citation boundary: full transitive closure contains the valid old auxiliary normalizer inside DG = {deps.contains `RepulsiveCoulomb.equilibriumReference_exp_elConstant_le}; authored disk/entropy route excludes it."
  for n in deps do
    if n.toString.startsWith "RepulsiveCoulomb.coulomb_named_" ||
        n.toString.startsWith "RepulsiveCoulomb.pointDilationBranch_named_" then
      throwError "Forbidden old named endpoint: {n}"
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
  let (_, main) := (visit env ``paper_uniform_defectAt_compact_disk).run ({} : NameSet)
  for n in #[``paper_reference_partition_pair_compact_ell_via_spatial,
      ``paper_compact_reference_integral_bounds_ell_disk,
      ``paper_reference_EL_normalizer_unitDisk_lower,
      ``paper_reference_potential_exponential_bound_disk,
      ``paper_gibbs_defect_moment_of_oneBody,
      ``paper_spatial_partition_uniform, ``exponential_integral_holder,
      ``paper_finite_defect_nonneg_disk] do
    unless main.contains n do throwError "Required all-parameter producer absent: {n}"
  logInfo m!"PASS: {roots.size} declarations; exact all-ell original defect and compact uniform supremum bounds."


end IntegratedScope09

namespace IntegratedScope10

/- Scoped semantic consumer; namespace/import-context adaptations are recorded in generation-manifest.json. -/

open Set MeasureTheory InnerProductSpace RepulsiveCoulomb RepulsiveCoulomb.PaperRoute
open scoped BigOperators

example {N : ℕ} (i j : Fin (N + 2)) (hij : i ≠ j)
    {φ : CoulombConfig (N + 2) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z : CoulombConfig (N + 2) => Real.log ‖z i - z j‖ * Laplacian.laplacian φ z) ∧
    Integrable φ (paperPairNormalDirac i j hij) ∧
    (∫ z : CoulombConfig (N + 2), Real.log ‖z i - z j‖ * Laplacian.laplacian φ z) =
      (2 * Real.pi) * ∫ z, φ z ∂paperPairNormalDirac i j hij :=
  paper_pair_collision_dirac i j hij hφ hφc

example {φ : CoulombConfig 2 → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ z : CoulombConfig 2, Real.log ‖z 0 - z 1‖ * Laplacian.laplacian φ z) =
      (2 * Real.pi) * ∫ z, φ z ∂paperPairNormalDirac 0 1 (by decide) :=
  (paper_pair_collision_dirac 0 1 (by decide) hφ hφc).2.2

example {φ : CoulombConfig 1 → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ z : CoulombConfig 1, planarLogKernel (z 0) * Laplacian.laplacian φ z) =
      (-2 * Real.pi) * ∫ y : CoulombConfig 0, φ (coulombInsertZero 0 y) :=
  (cylindrical_log_fundamental_solution hφ hφc).2

example {N : ℕ} (β : ℝ) {φ : CoulombConfig (N + 2) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z : CoulombConfig (N + 2) => coulombPotential β z * Laplacian.laplacian φ z) ∧
    -(1 / 2 : ℝ) * (∫ z : CoulombConfig (N + 2), coulombPotential β z * Laplacian.laplacian φ z) =
      -β * (N + 2 : ℕ) * (∫ z, φ z) + (Real.pi * (β / (N + 2 : ℕ))) *
        ∑ p ∈ coulombPairs (N + 2), ∫ z, φ z ∂paperPairCollisionMeasure p.1 p.2 :=
  paper_coulomb_potential_distribution β hφ hφc

example {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {φ : CoulombConfig (N + 2) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ z, 0 ≤ φ z) :
    0 ≤ -(1 / 2 : ℝ) * (∫ z : CoulombConfig (N + 2),
      (coulombPotential β z - (β / 2) * ‖z‖ ^ 2) * Laplacian.laplacian φ z) :=
  paper_coulomb_singular_nonnegative hβ hφ hφc hφ0

example {N : ℕ} {φ : CoulombConfig (N + 2) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    -(1 / 2 : ℝ) * (∫ z : CoulombConfig (N + 2), coulombPotential 0 z * Laplacian.laplacian φ z) = 0 := by
  simpa using (paper_coulomb_potential_distribution 0 hφ hφc).2

example (z : CoulombConfig 0) : Laplacian.laplacian (fun x : CoulombConfig 0 => ‖x‖ ^ 2) z = 0 := by
  simpa using collision_norm_sq_laplacian 0 z

example {N : ℕ} (i j : Fin (N + 2)) (hij : i ≠ j) (z : CoulombConfig (N + 2)) :
    ‖paperPairNormalChart i j hij z‖ = ‖z‖ := (paperPairNormalChart i j hij).norm_map z

example {N : ℕ} (i j : Fin (N + 2)) (hij : i ≠ j) (z : CoulombConfig (N + 2)) :
    paperPairNormalChart i j hij z 0 = (Real.sqrt 2)⁻¹ • (z i - z j) :=
  paperPairNormalChart_zero i j hij z

example {N : ℕ} (i j : Fin (N + 2)) (hij : i ≠ j)
    {φ : CoulombConfig (N + 2) → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable φ (paperPairNormalDirac i j hij) :=
  paperPairNormalDirac_test_integrable i j hij hφ hφc

#check @RepulsiveCoulomb.PaperRoute.CollisionCalculus.laplacian_comp_linearIsometryEquiv
#print axioms RepulsiveCoulomb.PaperRoute.CollisionCalculus.laplacian_comp_linearIsometryEquiv

#check @RepulsiveCoulomb.PaperRoute.CollisionCalculus.second_fderiv_apply_eq_iterated
#print axioms RepulsiveCoulomb.PaperRoute.CollisionCalculus.second_fderiv_apply_eq_iterated

#check @RepulsiveCoulomb.PaperRoute.CollisionCalculus.laplacian_eq_second_fderiv_basis
#print axioms RepulsiveCoulomb.PaperRoute.CollisionCalculus.laplacian_eq_second_fderiv_basis

#check @RepulsiveCoulomb.PaperRoute.CollisionCalculus.continuous_second_fderiv_apply
#print axioms RepulsiveCoulomb.PaperRoute.CollisionCalculus.continuous_second_fderiv_apply

#check @RepulsiveCoulomb.PaperRoute.CollisionCalculus.continuous_laplacian
#print axioms RepulsiveCoulomb.PaperRoute.CollisionCalculus.continuous_laplacian

#check @RepulsiveCoulomb.PaperRoute.CollisionCalculus.hasCompactSupport_laplacian
#print axioms RepulsiveCoulomb.PaperRoute.CollisionCalculus.hasCompactSupport_laplacian

#check @RepulsiveCoulomb.PaperRoute.CollisionCalculus.integrable_second_fderiv_apply
#print axioms RepulsiveCoulomb.PaperRoute.CollisionCalculus.integrable_second_fderiv_apply

#check @RepulsiveCoulomb.PaperRoute.CollisionCalculus.integral_second_fderiv_eq_zero
#print axioms RepulsiveCoulomb.PaperRoute.CollisionCalculus.integral_second_fderiv_eq_zero

#check @RepulsiveCoulomb.PaperRoute.CollisionCalculus.integrable_laplacian
#print axioms RepulsiveCoulomb.PaperRoute.CollisionCalculus.integrable_laplacian

#check @RepulsiveCoulomb.PaperRoute.CollisionCalculus.integral_laplacian_eq_zero
#print axioms RepulsiveCoulomb.PaperRoute.CollisionCalculus.integral_laplacian_eq_zero

#check @RepulsiveCoulomb.PaperRoute.CollisionCalculus.integral_mul_second_fderiv_eq
#print axioms RepulsiveCoulomb.PaperRoute.CollisionCalculus.integral_mul_second_fderiv_eq

#check @RepulsiveCoulomb.PaperRoute.collision_split_symm
#print axioms RepulsiveCoulomb.PaperRoute.collision_split_symm

#check @RepulsiveCoulomb.PaperRoute.cylindrical_local_integrable_test_prod
#print axioms RepulsiveCoulomb.PaperRoute.cylindrical_local_integrable_test_prod

#check @RepulsiveCoulomb.PaperRoute.cylindrical_local_integrable_test
#print axioms RepulsiveCoulomb.PaperRoute.cylindrical_local_integrable_test

#check @RepulsiveCoulomb.PaperRoute.cylindrical_log_test_integrable
#print axioms RepulsiveCoulomb.PaperRoute.cylindrical_log_test_integrable

#check @RepulsiveCoulomb.PaperRoute.cylindrical_log_test_integrable_prod
#print axioms RepulsiveCoulomb.PaperRoute.cylindrical_log_test_integrable_prod

#check @RepulsiveCoulomb.PaperRoute.cylindrical_log_test_integral_split
#print axioms RepulsiveCoulomb.PaperRoute.cylindrical_log_test_integral_split

#check @RepulsiveCoulomb.PaperRoute.cylindrical_normal_slice_test
#print axioms RepulsiveCoulomb.PaperRoute.cylindrical_normal_slice_test

#check @RepulsiveCoulomb.PaperRoute.cylindrical_normal_slice_fundamental
#print axioms RepulsiveCoulomb.PaperRoute.cylindrical_normal_slice_fundamental

#check @RepulsiveCoulomb.PaperRoute.paperPairSelection
#print axioms RepulsiveCoulomb.PaperRoute.paperPairSelection

#check @RepulsiveCoulomb.PaperRoute.paperPairSelection_spec
#print axioms RepulsiveCoulomb.PaperRoute.paperPairSelection_spec

#check @RepulsiveCoulomb.PaperRoute.paperPairNormalChart
#print axioms RepulsiveCoulomb.PaperRoute.paperPairNormalChart

#check @RepulsiveCoulomb.PaperRoute.paperPairNormalChart_zero
#print axioms RepulsiveCoulomb.PaperRoute.paperPairNormalChart_zero

#check @RepulsiveCoulomb.PaperRoute.paperPairNormalChart_measurePreserving
#print axioms RepulsiveCoulomb.PaperRoute.paperPairNormalChart_measurePreserving

#check @RepulsiveCoulomb.PaperRoute.cylindrical_tangent_insert_isometry
#print axioms RepulsiveCoulomb.PaperRoute.cylindrical_tangent_insert_isometry

#check @RepulsiveCoulomb.PaperRoute.paperPairNormalTrace
#print axioms RepulsiveCoulomb.PaperRoute.paperPairNormalTrace

#check @RepulsiveCoulomb.PaperRoute.paperPairNormalTrace_isometry
#print axioms RepulsiveCoulomb.PaperRoute.paperPairNormalTrace_isometry

#check @RepulsiveCoulomb.PaperRoute.paperPairNormalDirac
#print axioms RepulsiveCoulomb.PaperRoute.paperPairNormalDirac

#check @RepulsiveCoulomb.PaperRoute.paperPairNormalTrace_collision
#print axioms RepulsiveCoulomb.PaperRoute.paperPairNormalTrace_collision

#check @RepulsiveCoulomb.PaperRoute.paperPairNormalTrace_test_integrable
#print axioms RepulsiveCoulomb.PaperRoute.paperPairNormalTrace_test_integrable

#check @RepulsiveCoulomb.PaperRoute.paperPairNormalDirac_test_integrable
#print axioms RepulsiveCoulomb.PaperRoute.paperPairNormalDirac_test_integrable

#check @RepulsiveCoulomb.PaperRoute.paperPairNormalDirac_integral
#print axioms RepulsiveCoulomb.PaperRoute.paperPairNormalDirac_integral

#check @RepulsiveCoulomb.PaperRoute.paper_pair_log_unit_normal_ae
#print axioms RepulsiveCoulomb.PaperRoute.paper_pair_log_unit_normal_ae

#check @RepulsiveCoulomb.PaperRoute.collisionSecondDirection
#print axioms RepulsiveCoulomb.PaperRoute.collisionSecondDirection

#check @RepulsiveCoulomb.PaperRoute.collisionSecondDirection_continuous
#print axioms RepulsiveCoulomb.PaperRoute.collisionSecondDirection_continuous

#check @RepulsiveCoulomb.PaperRoute.collisionSecondDirection_compact
#print axioms RepulsiveCoulomb.PaperRoute.collisionSecondDirection_compact

#check @RepulsiveCoulomb.PaperRoute.collisionNormalLaplacian
#print axioms RepulsiveCoulomb.PaperRoute.collisionNormalLaplacian

#check @RepulsiveCoulomb.PaperRoute.collisionTangentLaplacian
#print axioms RepulsiveCoulomb.PaperRoute.collisionTangentLaplacian

#check @RepulsiveCoulomb.PaperRoute.collisionConfig_laplacian_sum
#print axioms RepulsiveCoulomb.PaperRoute.collisionConfig_laplacian_sum

#check @RepulsiveCoulomb.PaperRoute.collisionConfig_laplacian_split
#print axioms RepulsiveCoulomb.PaperRoute.collisionConfig_laplacian_split

#check @RepulsiveCoulomb.PaperRoute.collisionNormalLaplacian_continuous
#print axioms RepulsiveCoulomb.PaperRoute.collisionNormalLaplacian_continuous

#check @RepulsiveCoulomb.PaperRoute.collisionTangentLaplacian_continuous
#print axioms RepulsiveCoulomb.PaperRoute.collisionTangentLaplacian_continuous

#check @RepulsiveCoulomb.PaperRoute.collisionNormalLaplacian_compact
#print axioms RepulsiveCoulomb.PaperRoute.collisionNormalLaplacian_compact

#check @RepulsiveCoulomb.PaperRoute.collisionTangentLaplacian_compact
#print axioms RepulsiveCoulomb.PaperRoute.collisionTangentLaplacian_compact

#check @RepulsiveCoulomb.PaperRoute.collision_second_affine_chain
#print axioms RepulsiveCoulomb.PaperRoute.collision_second_affine_chain

#check @RepulsiveCoulomb.PaperRoute.collision_normal_trace_slice
#print axioms RepulsiveCoulomb.PaperRoute.collision_normal_trace_slice

#check @RepulsiveCoulomb.PaperRoute.collisionTailInjection
#print axioms RepulsiveCoulomb.PaperRoute.collisionTailInjection

#check @RepulsiveCoulomb.PaperRoute.collision_tangent_insert_affine
#print axioms RepulsiveCoulomb.PaperRoute.collision_tangent_insert_affine

#check @RepulsiveCoulomb.PaperRoute.collision_tangent_insert_contDiff
#print axioms RepulsiveCoulomb.PaperRoute.collision_tangent_insert_contDiff

#check @RepulsiveCoulomb.PaperRoute.collision_tangent_injection_direction
#print axioms RepulsiveCoulomb.PaperRoute.collision_tangent_injection_direction

#check @RepulsiveCoulomb.PaperRoute.collision_tangent_trace_slice
#print axioms RepulsiveCoulomb.PaperRoute.collision_tangent_trace_slice

#check @RepulsiveCoulomb.PaperRoute.cylindrical_normal_pairing
#print axioms RepulsiveCoulomb.PaperRoute.cylindrical_normal_pairing

#check @RepulsiveCoulomb.PaperRoute.cylindrical_tangent_pairing_zero
#print axioms RepulsiveCoulomb.PaperRoute.cylindrical_tangent_pairing_zero

#check @RepulsiveCoulomb.PaperRoute.cylindrical_log_fundamental_solution
#print axioms RepulsiveCoulomb.PaperRoute.cylindrical_log_fundamental_solution

#check @RepulsiveCoulomb.PaperRoute.paper_pair_normal_log_fundamental
#print axioms RepulsiveCoulomb.PaperRoute.paper_pair_normal_log_fundamental

#check @RepulsiveCoulomb.PaperRoute.paper_pair_collision_dirac
#print axioms RepulsiveCoulomb.PaperRoute.paper_pair_collision_dirac

#check @RepulsiveCoulomb.PaperRoute.paperPairCollisionMeasure
#print axioms RepulsiveCoulomb.PaperRoute.paperPairCollisionMeasure

#check @RepulsiveCoulomb.PaperRoute.paperPairCollisionMeasure_of_ne
#print axioms RepulsiveCoulomb.PaperRoute.paperPairCollisionMeasure_of_ne

#check @RepulsiveCoulomb.PaperRoute.paper_vandermonde_log_ae
#print axioms RepulsiveCoulomb.PaperRoute.paper_vandermonde_log_ae

#check @RepulsiveCoulomb.PaperRoute.paper_vandermonde_collision_pairing
#print axioms RepulsiveCoulomb.PaperRoute.paper_vandermonde_collision_pairing

#check @RepulsiveCoulomb.PaperRoute.paper_coulomb_singular_distribution
#print axioms RepulsiveCoulomb.PaperRoute.paper_coulomb_singular_distribution

#check @RepulsiveCoulomb.PaperRoute.paper_coulomb_singular_nonnegative
#print axioms RepulsiveCoulomb.PaperRoute.paper_coulomb_singular_nonnegative

#check @RepulsiveCoulomb.PaperRoute.collision_integral_mul_laplacian_eq
#print axioms RepulsiveCoulomb.PaperRoute.collision_integral_mul_laplacian_eq

#check @RepulsiveCoulomb.PaperRoute.collision_norm_sq_second
#print axioms RepulsiveCoulomb.PaperRoute.collision_norm_sq_second

#check @RepulsiveCoulomb.PaperRoute.collision_norm_sq_laplacian
#print axioms RepulsiveCoulomb.PaperRoute.collision_norm_sq_laplacian

#check @RepulsiveCoulomb.PaperRoute.collision_gaussian_pairing
#print axioms RepulsiveCoulomb.PaperRoute.collision_gaussian_pairing

#check @RepulsiveCoulomb.PaperRoute.paper_coulomb_potential_distribution
#print axioms RepulsiveCoulomb.PaperRoute.paper_coulomb_potential_distribution

open Lean Elab Command in
private partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env d
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env d

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := #[``RepulsiveCoulomb.PaperRoute.CollisionCalculus.laplacian_comp_linearIsometryEquiv,
    ``RepulsiveCoulomb.PaperRoute.CollisionCalculus.second_fderiv_apply_eq_iterated,
    ``RepulsiveCoulomb.PaperRoute.CollisionCalculus.laplacian_eq_second_fderiv_basis,
    ``RepulsiveCoulomb.PaperRoute.CollisionCalculus.continuous_second_fderiv_apply,
    ``RepulsiveCoulomb.PaperRoute.CollisionCalculus.continuous_laplacian,
    ``RepulsiveCoulomb.PaperRoute.CollisionCalculus.hasCompactSupport_laplacian,
    ``RepulsiveCoulomb.PaperRoute.CollisionCalculus.integrable_second_fderiv_apply,
    ``RepulsiveCoulomb.PaperRoute.CollisionCalculus.integral_second_fderiv_eq_zero,
    ``RepulsiveCoulomb.PaperRoute.CollisionCalculus.integrable_laplacian,
    ``RepulsiveCoulomb.PaperRoute.CollisionCalculus.integral_laplacian_eq_zero,
    ``RepulsiveCoulomb.PaperRoute.CollisionCalculus.integral_mul_second_fderiv_eq,
    ``RepulsiveCoulomb.PaperRoute.collision_split_symm,
    ``RepulsiveCoulomb.PaperRoute.cylindrical_local_integrable_test_prod,
    ``RepulsiveCoulomb.PaperRoute.cylindrical_local_integrable_test,
    ``RepulsiveCoulomb.PaperRoute.cylindrical_log_test_integrable,
    ``RepulsiveCoulomb.PaperRoute.cylindrical_log_test_integrable_prod,
    ``RepulsiveCoulomb.PaperRoute.cylindrical_log_test_integral_split,
    ``RepulsiveCoulomb.PaperRoute.cylindrical_normal_slice_test,
    ``RepulsiveCoulomb.PaperRoute.cylindrical_normal_slice_fundamental,
    ``RepulsiveCoulomb.PaperRoute.paperPairSelection,
    ``RepulsiveCoulomb.PaperRoute.paperPairSelection_spec,
    ``RepulsiveCoulomb.PaperRoute.paperPairNormalChart,
    ``RepulsiveCoulomb.PaperRoute.paperPairNormalChart_zero,
    ``RepulsiveCoulomb.PaperRoute.paperPairNormalChart_measurePreserving,
    ``RepulsiveCoulomb.PaperRoute.cylindrical_tangent_insert_isometry,
    ``RepulsiveCoulomb.PaperRoute.paperPairNormalTrace,
    ``RepulsiveCoulomb.PaperRoute.paperPairNormalTrace_isometry,
    ``RepulsiveCoulomb.PaperRoute.paperPairNormalDirac,
    ``RepulsiveCoulomb.PaperRoute.paperPairNormalTrace_collision,
    ``RepulsiveCoulomb.PaperRoute.paperPairNormalTrace_test_integrable,
    ``RepulsiveCoulomb.PaperRoute.paperPairNormalDirac_test_integrable,
    ``RepulsiveCoulomb.PaperRoute.paperPairNormalDirac_integral,
    ``RepulsiveCoulomb.PaperRoute.paper_pair_log_unit_normal_ae,
    ``RepulsiveCoulomb.PaperRoute.collisionSecondDirection,
    ``RepulsiveCoulomb.PaperRoute.collisionSecondDirection_continuous,
    ``RepulsiveCoulomb.PaperRoute.collisionSecondDirection_compact,
    ``RepulsiveCoulomb.PaperRoute.collisionNormalLaplacian,
    ``RepulsiveCoulomb.PaperRoute.collisionTangentLaplacian,
    ``RepulsiveCoulomb.PaperRoute.collisionConfig_laplacian_sum,
    ``RepulsiveCoulomb.PaperRoute.collisionConfig_laplacian_split,
    ``RepulsiveCoulomb.PaperRoute.collisionNormalLaplacian_continuous,
    ``RepulsiveCoulomb.PaperRoute.collisionTangentLaplacian_continuous,
    ``RepulsiveCoulomb.PaperRoute.collisionNormalLaplacian_compact,
    ``RepulsiveCoulomb.PaperRoute.collisionTangentLaplacian_compact,
    ``RepulsiveCoulomb.PaperRoute.collision_second_affine_chain,
    ``RepulsiveCoulomb.PaperRoute.collision_normal_trace_slice,
    ``RepulsiveCoulomb.PaperRoute.collisionTailInjection,
    ``RepulsiveCoulomb.PaperRoute.collision_tangent_insert_affine,
    ``RepulsiveCoulomb.PaperRoute.collision_tangent_insert_contDiff,
    ``RepulsiveCoulomb.PaperRoute.collision_tangent_injection_direction,
    ``RepulsiveCoulomb.PaperRoute.collision_tangent_trace_slice,
    ``RepulsiveCoulomb.PaperRoute.cylindrical_normal_pairing,
    ``RepulsiveCoulomb.PaperRoute.cylindrical_tangent_pairing_zero,
    ``RepulsiveCoulomb.PaperRoute.cylindrical_log_fundamental_solution,
    ``RepulsiveCoulomb.PaperRoute.paper_pair_normal_log_fundamental,
    ``RepulsiveCoulomb.PaperRoute.paper_pair_collision_dirac,
    ``RepulsiveCoulomb.PaperRoute.paperPairCollisionMeasure,
    ``RepulsiveCoulomb.PaperRoute.paperPairCollisionMeasure_of_ne,
    ``RepulsiveCoulomb.PaperRoute.paper_vandermonde_log_ae,
    ``RepulsiveCoulomb.PaperRoute.paper_vandermonde_collision_pairing,
    ``RepulsiveCoulomb.PaperRoute.paper_coulomb_singular_distribution,
    ``RepulsiveCoulomb.PaperRoute.paper_coulomb_singular_nonnegative,
    ``RepulsiveCoulomb.PaperRoute.collision_integral_mul_laplacian_eq,
    ``RepulsiveCoulomb.PaperRoute.collision_norm_sq_second,
    ``RepulsiveCoulomb.PaperRoute.collision_norm_sq_laplacian,
    ``RepulsiveCoulomb.PaperRoute.collision_gaussian_pairing,
    ``RepulsiveCoulomb.PaperRoute.paper_coulomb_potential_distribution]
  let (_, deps) := (roots.forM (visit env)).run ({} : NameSet)
  for n in deps do
    if n.toString.startsWith "RepulsiveCoulomb.pointDilationBranch_named_" ||
        n.toString.startsWith "RepulsiveCoulomb.coulomb_named_" then
      throwError "Unrelated old named endpoint selected: {n}"
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
  let (_, main) := (visit env ``paper_coulomb_potential_distribution).run ({} : NameSet)
  for n in #[`RepulsiveCoulomb.coulomb_fixed_particle_poincare,
      `RepulsiveCoulomb.coulombDbarWeakGraph_small_solution,
      `RepulsiveCoulomb.PaperRoute.paper_full_labeled_poincare,
      `RepulsiveCoulomb.PaperRoute.paper_full_labeled_poincare_via_resolvent,
      `RepulsiveCoulomb.PaperRoute.original_weighted_full_domain] do
    if main.contains n then throwError "Functional-inequality endpoint used to assert a distributional identity: {n}"
  for n in #[`RepulsiveCoulomb.PaperRoute.paper_pair_collision_dirac,
      `RepulsiveCoulomb.PaperRoute.paperPairNormalDirac,
      `RepulsiveCoulomb.PaperRoute.paperPairNormalChart_zero,
      `RepulsiveCoulomb.PaperRoute.paper_pair_log_unit_normal_ae,
      `RepulsiveCoulomb.coulombPairRotate_norm,
      `RepulsiveCoulomb.coulomb_pair_collision_volume_zero,
      `RepulsiveCoulomb.PaperRoute.cylindrical_local_integrable_test_prod,
      `RepulsiveCoulomb.PaperRoute.cylindrical_log_fundamental_solution,
      `RepulsiveCoulomb.PaperRoute.collision_normal_trace_slice,
      `RepulsiveCoulomb.PaperRoute.collision_tangent_trace_slice,
      `RepulsiveCoulomb.PaperRoute.log_fundamental_solution,
      `RepulsiveCoulomb.PaperRoute.CollisionCalculus.integral_laplacian_eq_zero,
      `RepulsiveCoulomb.PaperRoute.CollisionCalculus.laplacian_comp_linearIsometryEquiv,
      `RepulsiveCoulomb.PaperRoute.CollisionCalculus.integral_mul_second_fderiv_eq,
      `RepulsiveCoulomb.PaperRoute.paper_vandermonde_log_ae,
      `RepulsiveCoulomb.coulombDomain_ae,
      `RepulsiveCoulomb.PaperRoute.collision_gaussian_pairing,
      `RepulsiveCoulomb.PaperRoute.collision_norm_sq_laplacian] do
    unless main.contains n do throwError "Required actual physical Dirac producer missing: {n}"
  logInfo m!"PASS: {roots.size} declarations; genuine full-space C2 collision Dirac identity, actual logarithmic integrability and unit normal 2pi, literal smooth -beta*N and singular pi*beta/N terms; only standard axioms."


end IntegratedScope10

namespace IntegratedScope11

/- Scoped semantic consumer; namespace/import-context adaptations are recorded in generation-manifest.json. -/


open Set Metric Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators
open RepulsiveCoulomb RepulsiveCoulomb.PaperRoute

-- Constants are literally those of the separately preserved C1 route.
example (Q : ℝ) : originalPointWeakTwoConstant Q =
    2 * mapBackedDSConstant (1 + Q / 2) (1 + Q / 2) *
      Real.sqrt (Real.pi * mapBackedDoublingConstant (1 + Q / 2) (1 + Q / 2)) := rfl

-- No supplied homeomorphism or analytic certificate appears here.
example (Q : ℝ) : ∀ m : ℕ, ∀ a : Fin m → ℝ, (∀ j, 0 ≤ a j) →
    (∑ j, a j) ≤ Q → ∀ y : Fin m → ℂ,
    PlanarDS.WeakOneTwoLocallyLipschitz (rawPointMeasure a y) (originalPointWeakTwoConstant Q) 2 := by
  intro m a ha hQ y
  exact (original_point_doubling_and_locallyLipschitz_PI ha hQ y).2.2

example : PlanarDS.WeakOneTwoLocallyLipschitz
    (rawPointMeasure (fun _ : Fin 0 => (0 : ℝ)) (fun _ => (0 : ℂ)))
    (originalPointWeakTwoConstant 0) 2 :=
  (original_point_doubling_and_locallyLipschitz_PI
    (Q := 0) (a := fun _ : Fin 0 => (0 : ℝ)) (by simp) (by simp) (fun _ => (0 : ℂ))).2.2

example {Q : ℝ} {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : (∑ j, a j) ≤ Q) (y : Fin m → ℂ)
    {v : ℂ → ℝ} {Lv : ℝ≥0} (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hv : LipschitzOnWith Lv v (closedBall z (2 * r))) :
    (⨍ w in ball z r,
      ‖v w - (⨍ z' in ball z r, v z' ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
      originalPointWeakTwoConstant Q * r * Real.sqrt
        (⨍ w in ball z (2 * r), ‖gradient v w‖ ^ 2 ∂rawPointMeasure a y) :=
  original_point_physical_weak_one_two_closedDoubleBall ha hQ y z hr hv

#check original_point_locallyLipschitz_geometry
#check original_point_doubling_and_locallyLipschitz_PI
#check original_point_physical_weak_one_two_closedDoubleBall
#print axioms original_point_locallyLipschitz_geometry
#print axioms original_point_doubling_and_locallyLipschitz_PI
#print axioms original_point_physical_weak_one_two_closedDoubleBall

namespace OriginalPointAdmissibilityAudit
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0
partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env d
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env d
run_cmd do
  let env ← getEnv
  let roots := #[``original_point_locallyLipschitz_geometry,
    ``original_point_doubling_and_locallyLipschitz_PI,
    ``original_point_physical_weak_one_two_closedDoubleBall]
  let (_, deps) := (roots.forM (visit env)).run ({} : NameSet)
  for n in #[`RepulsiveCoulomb.rawPointMeasure_uniform_strongAInfinity,
      `RepulsiveCoulomb.pointConformalEDist_diameter_comparison,
      `RepulsiveCoulomb.rawPoint_DavidSemmes_estimate,
      `RepulsiveCoulomb.rawPoint_C1_double_oscillation_real,
      `RepulsiveCoulomb.rawPoint_physical_weak_one_two_of_DavidSemmes,
      `RepulsiveCoulomb.rawPoint_uniform_local_sobolev_poincare,
      `RepulsiveCoulomb.pointGaussian_uniform_local_geometry,
      `RepulsiveCoulomb.pointDilationBranchP1,
      `RepulsiveCoulomb.pointDilationBranchK1,
      `RepulsiveCoulomb.pointDilationBranchCwt,
      `RepulsiveCoulomb.pointDilationBranchRhoWt,
      `sorryAx] do
    if deps.contains n then throwError "Forbidden transitive declaration dependency: {n}"
  for n in #[``RepulsiveCoulomb.point_original_plane_sharp_bonk_lang,
      ``RepulsiveCoulomb.point_original_plane_finite_surgery_development,
      ``RepulsiveCoulomb.pointMetricMap_lipschitzOn_ball,
      ``original_point_exists_map_data,
      ``original_point_pathGauge_of_sameMap,
      ``pointMapInverse_locallyLipschitzOn_of_metric_lower,
      ``exists_pointConformal_analytic_flat_metric_chart,
      ``pointMap_puncture_image_finite,
      ``mapBacked_planarDS_and_weakOneTwoLocallyLipschitz,
      ``planarDSLipschitz_of_analytic_qc_finite_inverse_punctures,
      ``PlanarDS.norm_gradient_eq_norm_fderiv,
      ``weakQuasisymmetricWith_of_analytic_qc,
      ``semmes_weight_sameMap_of_analytic_qc,
      ``jacobianMeasure_gaugeComparable,
      ``jacobianMeasure_globalDoubling,
      ``image_closedBall_diam_le_of_gauge_doubling,
      ``euclideanDiameterBall_subset_doubleBall,
      ``PlanarDS.doubling_real,
      ``WeakQuasisymmetricWith.ball_subset_image_doubleBall,
      ``BufferedCover.exists_data,
      ``BufferedCover.Data.edge_overlap,
      ``BufferedCover.Data.overlap_real_volume,
      ``BufferedCover.Data.bounded_path,
      ``BufferedOscillation.integral_abs_sub_rootMean_le_of_ballPI,
      ``exists_ballMean_oscillation_le_of_finite_punctures,
      ``FinitePunctureBall.integral_abs_sub_average_le_of_finite_punctures,
      ``EuclideanBall.integral_abs_sub_average_le_of_lipschitzOn_closedBall,
      ``inverse_gradient_transport_of_lipschitz_continuous_weight,
      ``hasFDerivAt_homeomorph_symm_of_det_ne_zero,
      ``fderiv_det_mul_norm_gradient_chain_of_comp,
      ``planar_cofactor_identity,
      ``lintegral_image_ball_eq_lintegral_signedJacobian_mul_of_locallyLipschitz,
      ``integral_weighted_abs_sub_le_image_ball,
      ``lintegral_weighted_scalar_comp_le_image_ball,
      ``doubleOscillation_le_abs_sub_reference,
      ``PlanarDS.weakOneTwoLipschitz_of_planarDS,
      ``PlanarDS.mixedIntegral_le_sqrt_area_energy_measurable,
      ``PlanarDS.integrableOn_sq_norm_fderiv_ball_of_lipschitz,
      ``PlanarDS.weakOneTwo_of_lipschitzOn_closedDoubleBall,
      ``PlanarDS.weakOneTwoLocallyLipschitz_of_lipschitz,
      ``LipschitzWith.ae_differentiableAt,
      ``norm_fderiv_le_of_lipschitz,
      ``measurable_fderiv,
      ``LipschitzOnWith.extend_real,
      ``Filter.EventuallyEq.fderiv_eq,
      ``LocallyLipschitzOn.exists_lipschitzOnWith_of_compact,
      ``lintegral_norm_fderiv_scalar_comp_symm_image_ball_le_ae] do
    unless deps.contains n do throwError "Required actual producer missing: {n}"
  for n in #[``planarDSC1_of_analytic_qc_finite_inverse_punctures,
      ``mapBacked_planarDS_and_weakOneTwoC1,
      ``inverse_gradient_transport_of_contDiff_continuous_weight,
      ``PlanarDS.weakOneTwoC1_of_planarDS] do
    if deps.contains n then throwError "Unexpected C1-only proof dependency: {n}"
  if deps.contains ``original_point_localGeometry then
    throwError "Full Lipschitz endpoint incorrectly depends on the C1-only original geometry proof"
  for n in deps do
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
  logInfo "PASS: one original-input map supplies the literal physical path gauge and full Lipschitz DS/weak-PI route."
  logInfo "PASS: actual Lipschitz Rademacher, measurable-gradient energy, real extension and derivative localization are load-bearing."
  logInfo "PASS: foundational axioms and actual type/proof-route exclusions; the original scoped import census is retained in its separately bound receipt."
end OriginalPointAdmissibilityAudit


end IntegratedScope11

namespace IntegratedScope12

/- Scoped semantic consumer; namespace/import-context adaptations are recorded in generation-manifest.json. -/


open MeasureTheory Real Set Metric TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff
open RepulsiveCoulomb RepulsiveCoulomb.PaperRoute

example {ρ : ℂ → ℝ} {M s r : ℝ} (h0 : ∀ x, 0 ≤ ρ x) (hM : ∀ x, ρ x ≤ M)
    (hs : 0 ≤ s) (hsr : s ≤ r) :
    0 ≤ equilibriumCumulativeMass (equilibriumDensityMeasure ρ) r -
      equilibriumCumulativeMass (equilibriumDensityMeasure ρ) s ∧
    equilibriumCumulativeMass (equilibriumDensityMeasure ρ) r -
      equilibriumCumulativeMass (equilibriumDensityMeasure ρ) s ≤ Real.pi * M * (r^2-s^2) :=
  cumulativeMass_increment_le_of_density_bound h0 hM hs hsr

example {ρ : ℂ → ℝ} {M : ℝ} (h0 : ∀ x, 0 ≤ ρ x) (hM : ∀ x, ρ x ≤ M) :
    LipschitzWith (thermalNewtonLipschitzConstant M)
      (thermalNewtonGradient (equilibriumDensityMeasure ρ)) :=
  thermalNewtonGradient_lipschitz h0 hM

example {F : ℂ → ℂ}
    (hloc : ∀ R : ℝ, ∃ K : ℝ≥0, LipschitzOnWith K F (closedBall 0 R)) :
    TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ) F (fderiv ℝ F) :=
  RepulsiveCoulomb.PaperRoute.plane_hasWeakFDerivOn_of_lipschitzOn_closedBall hloc

section Raw
variable {ρ : ℂ → ℝ} {M : ℝ}
  (hm : Measurable ρ) (h0 : ∀ x, 0 ≤ ρ x) (hM : ∀ x, ρ x ≤ M)
  (hi : Integrable ρ) (hmass : (∫ x, ρ x)=1)
  (h2 : Integrable (fun x : ℂ => ‖x‖^2 * ρ x))
  (hrad : ∀ ⦃x y : ℂ⦄, ‖x‖=‖y‖ → equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y)
example (x : ℂ) : Integrable (fun y => equilibriumLogKernel (x-y)*ρ y) :=
  boundedDensityPotential_kernel_integrable hm h0 hM hi h2 x
example : LocallyIntegrable (equilibriumDensityPotential ρ) volume :=
  boundedDensityPotential_locallyIntegrable hm h0 hM hi hmass h2
example {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => equilibriumDensityPotential ρ x * Laplacian.laplacian φ x) ∧
    Integrable (fun x => ρ x * φ x) ∧
    (∫ x : ℂ, equilibriumDensityPotential ρ x * Laplacian.laplacian φ x) =
      (-2 * Real.pi) * (∫ x : ℂ, ρ x * φ x) :=
  boundedDensityPotential_weak_poisson hm h0 hM hi hmass h2 hφ hc
example : TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ)
    (fderiv ℝ (equilibriumDensityPotential ρ)) (thermalWeakHessian ρ) :=
  thermal_radial_potential_fderiv_hasWeakFDerivOn hm h0 hM hi hmass h2 hrad
example (p : ℝ≥0∞) {S : Set ℂ} (hS : IsCompact S) :
    MemLp (thermalWeakHessian ρ) p (volume.restrict S) :=
  thermalWeakHessian_memLp_isCompact h0 hM p hS
example (R θ : ℝ≥0) (hθ : θ ≤ 1) :
    HolderOnWith (thermalNewtonLipschitzConstant M * (2*R : ℝ≥0)^(1-(θ : ℝ))) θ
      (fderiv ℝ (equilibriumDensityPotential ρ)) (closedBall (0 : ℂ) (R : ℝ)) :=
  thermal_radial_potential_fderiv_holder_closedBall hm h0 hM hi hmass h2 hrad R θ hθ
end Raw

example {β : ℝ} (hβ : 0 < β) (μ : ProbabilityMeasure ℂ)
    (hmin : ∀ ν : ProbabilityMeasure ℂ, equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) :
    ∃ ρ : ℂ → ℝ, equilibriumDensityMeasure ρ = (μ : Measure ℂ) ∧ ContDiff ℝ 1 ρ ∧
      TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ)
        (fderiv ℝ (equilibriumDensityPotential ρ)) (thermalWeakHessian ρ) := by
  obtain ⟨ρ, C, M, K, hm, hpos, hM, hbound, hi, hmass, h2, hH, hlaw, hEL, hK, htail,
    hG, hUrad, hrad, hρC1, hUC1, hweakU, hweakDU, hLp, hHolder, hPoisson⟩ :=
    thermalCanonical_minimizer_exists_weak_regular_EL_density hβ μ hmin
  exact ⟨ρ, hlaw, hρC1, hweakDU⟩

example : ∃ (μ : ProbabilityMeasure ℂ) (ρ : ℂ → ℝ),
    equilibriumNonnegativeObjective 1 μ ≠ ⊤ ∧ equilibriumDensityMeasure ρ = (μ : Measure ℂ) ∧
    ContDiff ℝ 1 ρ ∧ (∀ p : ℝ≥0∞, MemLp (thermalWeakHessian ρ) p (volume.restrict (closedBall 0 1))) := by
  obtain ⟨μ, hF, hmin, ρ, C, M, K, hm, hpos, hM, hbound, hi, hmass, h2, hH, hlaw,
    hEL, hK, htail, hG, hUrad, hrad, hρC1, hUC1, hweakU, hweakDU, hLp, hHolder, hPoisson⟩ :=
    thermal_exists_weak_regular_EL_minimizer (by norm_num : (0 : ℝ) < 1)
  exact ⟨μ, ρ, hF, hlaw, hρC1, fun p => (hLp p _ (isCompact_closedBall 0 1)).2.2⟩
#check RepulsiveCoulomb.PaperRoute.translated_log_fundamental_solution
#check RepulsiveCoulomb.PaperRoute.boundedDensityPotential_kernel_integrable
#check RepulsiveCoulomb.PaperRoute.boundedDensityPotential_locallyIntegrable
#check RepulsiveCoulomb.PaperRoute.boundedDensity_kernel_compact_test_integrable
#check RepulsiveCoulomb.PaperRoute.boundedDensityPotential_weak_poisson
#check RepulsiveCoulomb.PaperRoute.cumulativeMass_increment_le_of_density_bound
#check RepulsiveCoulomb.PaperRoute.thermalNewtonGradient
#check RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_zero
#check RepulsiveCoulomb.PaperRoute.thermal_radial_coefficient_variation
#check RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_norm_sub_le_ordered
#check RepulsiveCoulomb.PaperRoute.thermalNewtonLipschitzConstant
#check RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_lipschitz
#check RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_riesz
#check RepulsiveCoulomb.PaperRoute.thermalDensityPotential_fderiv_eq_newtonGradient
#check RepulsiveCoulomb.PaperRoute.plane_continuous_of_lipschitzOn_closedBall
#check RepulsiveCoulomb.PaperRoute.plane_ae_differentiableAt_of_lipschitzOn_closedBall
#check RepulsiveCoulomb.PaperRoute.plane_memLp_isCompact_of_lipschitzOn_closedBall
#check RepulsiveCoulomb.PaperRoute.plane_fderiv_memLp_isCompact_of_lipschitzOn_closedBall
#check RepulsiveCoulomb.PaperRoute.plane_fderiv_locallyIntegrable_of_lipschitzOn_closedBall
#check RepulsiveCoulomb.PaperRoute.scalar_integral_lineDeriv_mul_of_lipschitzOn_closedBall
#check RepulsiveCoulomb.PaperRoute.plane_projection_integral_fderiv_mul_of_lipschitzOn_closedBall
#check RepulsiveCoulomb.PaperRoute.plane_projection_hasWeakLineDerivOn_of_lipschitzOn_closedBall
#check RepulsiveCoulomb.PaperRoute.plane_hasWeakFDerivOn_of_lipschitzOn_closedBall
#check RepulsiveCoulomb.PaperRoute.thermalWeakHessian
#check RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_ballwise_lipschitz
#check RepulsiveCoulomb.PaperRoute.thermal_radial_potential_contDiff_one
#check RepulsiveCoulomb.PaperRoute.thermal_radial_potential_fderiv_function
#check RepulsiveCoulomb.PaperRoute.thermal_radial_potential_hasWeakFDerivOn
#check RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_hasWeakFDerivOn
#check RepulsiveCoulomb.PaperRoute.thermal_radial_potential_fderiv_hasWeakFDerivOn
#check RepulsiveCoulomb.PaperRoute.thermal_radial_potential_memLp_isCompact
#check RepulsiveCoulomb.PaperRoute.thermal_radial_potential_fderiv_memLp_isCompact
#check RepulsiveCoulomb.PaperRoute.thermalWeakHessian_memLp_isCompact
#check RepulsiveCoulomb.PaperRoute.thermal_radial_potential_fderiv_lipschitz
#check RepulsiveCoulomb.PaperRoute.thermal_radial_potential_fderiv_holder_closedBall
#check RepulsiveCoulomb.PaperRoute.thermal_radial_weak_regularity
#check RepulsiveCoulomb.PaperRoute.thermal_EL_contDiff_one_of_potential
#check RepulsiveCoulomb.PaperRoute.thermalCanonical_minimizer_exists_weak_regular_EL_density
#check RepulsiveCoulomb.PaperRoute.thermal_exists_weak_regular_EL_minimizer
#print axioms RepulsiveCoulomb.PaperRoute.translated_log_fundamental_solution
#print axioms RepulsiveCoulomb.PaperRoute.boundedDensityPotential_kernel_integrable
#print axioms RepulsiveCoulomb.PaperRoute.boundedDensityPotential_locallyIntegrable
#print axioms RepulsiveCoulomb.PaperRoute.boundedDensity_kernel_compact_test_integrable
#print axioms RepulsiveCoulomb.PaperRoute.boundedDensityPotential_weak_poisson
#print axioms RepulsiveCoulomb.PaperRoute.cumulativeMass_increment_le_of_density_bound
#print axioms RepulsiveCoulomb.PaperRoute.thermalNewtonGradient
#print axioms RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_zero
#print axioms RepulsiveCoulomb.PaperRoute.thermal_radial_coefficient_variation
#print axioms RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_norm_sub_le_ordered
#print axioms RepulsiveCoulomb.PaperRoute.thermalNewtonLipschitzConstant
#print axioms RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_lipschitz
#print axioms RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_riesz
#print axioms RepulsiveCoulomb.PaperRoute.thermalDensityPotential_fderiv_eq_newtonGradient
#print axioms RepulsiveCoulomb.PaperRoute.plane_continuous_of_lipschitzOn_closedBall
#print axioms RepulsiveCoulomb.PaperRoute.plane_ae_differentiableAt_of_lipschitzOn_closedBall
#print axioms RepulsiveCoulomb.PaperRoute.plane_memLp_isCompact_of_lipschitzOn_closedBall
#print axioms RepulsiveCoulomb.PaperRoute.plane_fderiv_memLp_isCompact_of_lipschitzOn_closedBall
#print axioms RepulsiveCoulomb.PaperRoute.plane_fderiv_locallyIntegrable_of_lipschitzOn_closedBall
#print axioms RepulsiveCoulomb.PaperRoute.scalar_integral_lineDeriv_mul_of_lipschitzOn_closedBall
#print axioms RepulsiveCoulomb.PaperRoute.plane_projection_integral_fderiv_mul_of_lipschitzOn_closedBall
#print axioms RepulsiveCoulomb.PaperRoute.plane_projection_hasWeakLineDerivOn_of_lipschitzOn_closedBall
#print axioms RepulsiveCoulomb.PaperRoute.plane_hasWeakFDerivOn_of_lipschitzOn_closedBall
#print axioms RepulsiveCoulomb.PaperRoute.thermalWeakHessian
#print axioms RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_ballwise_lipschitz
#print axioms RepulsiveCoulomb.PaperRoute.thermal_radial_potential_contDiff_one
#print axioms RepulsiveCoulomb.PaperRoute.thermal_radial_potential_fderiv_function
#print axioms RepulsiveCoulomb.PaperRoute.thermal_radial_potential_hasWeakFDerivOn
#print axioms RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_hasWeakFDerivOn
#print axioms RepulsiveCoulomb.PaperRoute.thermal_radial_potential_fderiv_hasWeakFDerivOn
#print axioms RepulsiveCoulomb.PaperRoute.thermal_radial_potential_memLp_isCompact
#print axioms RepulsiveCoulomb.PaperRoute.thermal_radial_potential_fderiv_memLp_isCompact
#print axioms RepulsiveCoulomb.PaperRoute.thermalWeakHessian_memLp_isCompact
#print axioms RepulsiveCoulomb.PaperRoute.thermal_radial_potential_fderiv_lipschitz
#print axioms RepulsiveCoulomb.PaperRoute.thermal_radial_potential_fderiv_holder_closedBall
#print axioms RepulsiveCoulomb.PaperRoute.thermal_radial_weak_regularity
#print axioms RepulsiveCoulomb.PaperRoute.thermal_EL_contDiff_one_of_potential
#print axioms RepulsiveCoulomb.PaperRoute.thermalCanonical_minimizer_exists_weak_regular_EL_density
#print axioms RepulsiveCoulomb.PaperRoute.thermal_exists_weak_regular_EL_minimizer
namespace ThermalWeakRegularityAudit
open Lean Elab Command
partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env d
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env d
run_cmd do
  let env ← getEnv
  let (_, deps) := (visit env ``thermal_exists_weak_regular_EL_minimizer).run ({} : NameSet)
  let allNew := #[``RepulsiveCoulomb.PaperRoute.translated_log_fundamental_solution, ``RepulsiveCoulomb.PaperRoute.boundedDensityPotential_kernel_integrable, ``RepulsiveCoulomb.PaperRoute.boundedDensityPotential_locallyIntegrable, ``RepulsiveCoulomb.PaperRoute.boundedDensity_kernel_compact_test_integrable, ``RepulsiveCoulomb.PaperRoute.boundedDensityPotential_weak_poisson, ``RepulsiveCoulomb.PaperRoute.cumulativeMass_increment_le_of_density_bound, ``RepulsiveCoulomb.PaperRoute.thermalNewtonGradient, ``RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_zero, ``RepulsiveCoulomb.PaperRoute.thermal_radial_coefficient_variation, ``RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_norm_sub_le_ordered, ``RepulsiveCoulomb.PaperRoute.thermalNewtonLipschitzConstant, ``RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_lipschitz, ``RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_riesz, ``RepulsiveCoulomb.PaperRoute.thermalDensityPotential_fderiv_eq_newtonGradient, ``RepulsiveCoulomb.PaperRoute.plane_continuous_of_lipschitzOn_closedBall, ``RepulsiveCoulomb.PaperRoute.plane_ae_differentiableAt_of_lipschitzOn_closedBall, ``RepulsiveCoulomb.PaperRoute.plane_memLp_isCompact_of_lipschitzOn_closedBall, ``RepulsiveCoulomb.PaperRoute.plane_fderiv_memLp_isCompact_of_lipschitzOn_closedBall, ``RepulsiveCoulomb.PaperRoute.plane_fderiv_locallyIntegrable_of_lipschitzOn_closedBall, ``RepulsiveCoulomb.PaperRoute.scalar_integral_lineDeriv_mul_of_lipschitzOn_closedBall, ``RepulsiveCoulomb.PaperRoute.plane_projection_integral_fderiv_mul_of_lipschitzOn_closedBall, ``RepulsiveCoulomb.PaperRoute.plane_projection_hasWeakLineDerivOn_of_lipschitzOn_closedBall, ``RepulsiveCoulomb.PaperRoute.plane_hasWeakFDerivOn_of_lipschitzOn_closedBall, ``RepulsiveCoulomb.PaperRoute.thermalWeakHessian, ``RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_ballwise_lipschitz, ``RepulsiveCoulomb.PaperRoute.thermal_radial_potential_contDiff_one, ``RepulsiveCoulomb.PaperRoute.thermal_radial_potential_fderiv_function, ``RepulsiveCoulomb.PaperRoute.thermal_radial_potential_hasWeakFDerivOn, ``RepulsiveCoulomb.PaperRoute.thermalNewtonGradient_hasWeakFDerivOn, ``RepulsiveCoulomb.PaperRoute.thermal_radial_potential_fderiv_hasWeakFDerivOn, ``RepulsiveCoulomb.PaperRoute.thermal_radial_potential_memLp_isCompact, ``RepulsiveCoulomb.PaperRoute.thermal_radial_potential_fderiv_memLp_isCompact, ``RepulsiveCoulomb.PaperRoute.thermalWeakHessian_memLp_isCompact, ``RepulsiveCoulomb.PaperRoute.thermal_radial_potential_fderiv_lipschitz, ``RepulsiveCoulomb.PaperRoute.thermal_radial_potential_fderiv_holder_closedBall, ``RepulsiveCoulomb.PaperRoute.thermal_radial_weak_regularity, ``RepulsiveCoulomb.PaperRoute.thermal_EL_contDiff_one_of_potential, ``RepulsiveCoulomb.PaperRoute.thermalCanonical_minimizer_exists_weak_regular_EL_density, ``RepulsiveCoulomb.PaperRoute.thermal_exists_weak_regular_EL_minimizer]
  let (_, allDeps) := (do for n in allNew do visit env n).run ({} : NameSet)
  for n in allDeps do
    if n == `sorryAx then throwError "Incomplete proof in new bounded radial EL representative"
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
    for forbidden in #["equilibriumLogKernel_zeroMass_nonneg", "equilibrium_pointwise_EL_densities_unique",
        "equilibriumCanonicalMinimizers_unique", "equilibrium_pointwise_EL_radial",
        "equilibriumObjective_lowerSemicontinuous", "equilibriumExtendedInteraction_lowerSemicontinuous",
        "equilibriumObjective_exists_global_minimizer", "equilibriumCanonical_exists_global_minimizer",
        "equilibrium_exists_bounded_EL_minimizer", "equilibrium_pointwise_EL_contDiff",
        "equilibrium_pointwise_EL_contDiff_one", "pointMetricMap_hasWeakFDerivOn",
        "pointMetricMap_memW1pLoc_of_lipschitzOn_closedBall", "equilibriumThermalReference"] do
      if n.toString == "RepulsiveCoulomb." ++ forbidden then
        throwError "Forbidden old selected-reference/minimizer/radiality shortcut: {n}"
  logInfo "PASS: all new theorem types and opaque proof bodies have only standard axioms and no old minimizer, radiality, smooth-reference or point-map shortcut"
  for n in #[``thermalCanonical_exists_global_minimizer,
      ``thermalCanonical_global_minimizer_finite_domain,
      ``equilibriumCanonicalMinimizer_exists_bounded_EL_density,
      ``equilibriumCanonicalMinimizer_density_positive_ae,
      ``equilibriumCanonicalMinimizer_eulerLagrange_ae,
      ``equilibriumELRepresentative_pointwise_properties,
      ``thermalBoundedDensity_pointPotential_integrable,
      ``thermalBoundedDensity_extendedPotential_eq_potential,
      ``thermalCanonical_bounded_density_potential_radial,
      ``thermalCanonical_minimizer_extendedPotential_eq_of_norm_eq,
      ``thermalCanonical_minimizer_map_isometry,
      ``thermalCanonical_global_minimizers_unique,
      ``thermalDensityMixture_entropy_strict,
      ``log_green_zero_mass,
      ``boundedDensityPotential_weak_poisson,
      ``boundedDensity_kernel_compact_test_integrable,
      ``translated_log_fundamental_solution,
      ``log_fundamental_solution,
      ``thermal_radial_weak_regularity,
      ``cumulativeMass_increment_le_of_density_bound,
      ``thermalNewtonGradient_lipschitz,
      ``RepulsiveCoulomb.PaperRoute.plane_hasWeakFDerivOn_of_lipschitzOn_closedBall,
      ``RepulsiveCoulomb.PaperRoute.plane_ae_differentiableAt_of_lipschitzOn_closedBall,
      ``RepulsiveCoulomb.PaperRoute.scalar_integral_lineDeriv_mul_of_lipschitzOn_closedBall,
      ``LipschitzWith.integral_lineDeriv_mul_eq,
      ``LipschitzOnWith.ae_differentiableWithinAt_of_mem,
      ``thermal_radial_potential_fderiv_hasWeakFDerivOn,
      ``thermalWeakHessian_memLp_isCompact,
      ``thermal_radial_potential_fderiv_holder_closedBall,
      ``thermal_EL_contDiff_one_of_potential] do
    unless deps.contains n do throwError "Required actual producer not load-bearing: {n}"
  logInfo "PASS: NEW minimizer and chosen EL density, fundamental-solution/Fubini, annular mass, physical Lipschitz gradient, Rademacher/test identities, weak Hessian, local Lp and Holder, and exponential initial density C1 are load-bearing"
  for n in deps do
    if n.toString.startsWith "RepulsiveCoulomb." then logInfo m!"PROJECT_DEP {n}"
end ThermalWeakRegularityAudit


end IntegratedScope12

namespace IntegratedScope13

/- Scoped semantic consumer; namespace/import-context adaptations are recorded in generation-manifest.json. -/

open Set MeasureTheory ProbabilityTheory RepulsiveCoulomb RepulsiveCoulomb.PaperRoute

example {a b β : ℝ} (ha : 0 < a) (hab : a ≤ b) (hβ : 0 < β) (hlo : a ≤ β) (hhi : β ≤ b)
    (N : ℕ) (hN : 2 ≤ N) (u : CoulombFormDomain N hβ) :
    variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
      (poleBranchSymmetricIntervalSup ha b + paperCwt 1 (2 * b) / a) * coulombFormEnergy N hβ u :=
  paper_full_labeled_poincare_compact_via_resolvent ha hab hβ hlo hhi N hN u

example {a : ℝ} (ha : 0 < a) :
    0 < paperCAllInterval ha a ∧ ∀ β (hβ : 0 < β), a ≤ β → β ≤ a →
      ∀ (N : ℕ), 2 ≤ N → ∀ u : CoulombFormDomain N hβ,
      variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
        paperCAllInterval ha a * coulombFormEnergy N hβ u :=
  paper_full_labeled_poincare_uniform_via_resolvent ha le_rfl

#check @paper_full_labeled_poincare_compact_via_resolvent
#print axioms paper_full_labeled_poincare_compact_via_resolvent
#check @paper_full_labeled_poincare_uniform_via_resolvent
#print axioms paper_full_labeled_poincare_uniform_via_resolvent

open Lean Elab Command in
private partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env d
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env d

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let (_, deps) := (visit env ``paper_full_labeled_poincare_uniform_via_resolvent).run ({} : NameSet)
  for n in #[`RepulsiveCoulomb.coulomb_fixed_particle_poincare,
      `RepulsiveCoulomb.coulombForm_coercivity_of_meanZero_kernel,
      `RepulsiveCoulomb.coulombForm_poincare_of_meanZero_kernel,
      `RepulsiveCoulomb.coulombOptimalPoincare_inequality,
      `RepulsiveCoulomb.PaperRoute.paper_full_labeled_poincare_compact,
      `RepulsiveCoulomb.PaperRoute.paper_full_labeled_poincare_uniform,
      `RepulsiveCoulomb.pointDilationBranchCwt,
      `RepulsiveCoulomb.pointDilationBranchCrel] do
    if deps.contains n then throwError "Forbidden older PI producer in selected compact route: {n}"
  for n in deps do
    if n.toString.startsWith "RepulsiveCoulomb.pointDilationBranch_named_" ||
        n.toString.startsWith "RepulsiveCoulomb.coulomb_named_" then
      throwError "Forbidden old named endpoint: {n}"
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
  for n in #[`RepulsiveCoulomb.PaperRoute.compact_resolvent_mean_zero_coercivity,
      `RepulsiveCoulomb.PaperRoute.paper_resolvent_form_residual,
      `RepulsiveCoulomb.coulombFormResolvent_isCompactOperator,
      `RepulsiveCoulomb.coulombAssociatedGraph_inverse,
      `RepulsiveCoulomb.coulombAssociatedOperator_zero_constant,
      `RepulsiveCoulomb.coulomb_compact_temperature_poincare,
      `RepulsiveCoulomb.coulombTemperature_no_unit_meanZero_smallGradient,
      `RepulsiveCoulomb.PaperRoute.paper_weighted_named_full_above] do
    unless deps.contains n do throwError "Required compact-temperature/resolvent producer missing: {n}"
  logInfo "PASS: exact compact-temperature wrapper; genuine resolvent-fed symmetric PI, actual varying-temperature gap and one new exponent cap; only standard axioms."


end IntegratedScope13

namespace IntegratedScope14

/- Scoped semantic consumer; namespace/import-context adaptations are recorded in generation-manifest.json. -/

open MeasureTheory Set Real
open RepulsiveCoulomb RepulsiveCoulomb.PaperRoute
open PeriodicAttractiveLogGas

example {N : ℕ} (hN : 0 < N) (z : Fin N → ℂ) :
    IsProbabilityMeasure (paperEmpiricalMeasure z) := paper_empirical_probability hN z

example {N : ℕ} (hN : 0 < N) (μ : Measure ℂ) [IsProbabilityMeasure μ] (z : Fin N → ℂ) :
    paperFluctuationMeasure μ z Set.univ = 0 := paper_fluctuation_total_mass hN μ z

example {N : ℕ} (μ : Measure ℂ) [IsFiniteMeasure μ] (z : Fin N → ℂ) :
    (1 / 2 : ℝ) * (∫ᵛ p in paperSpatialOffDiagonal, paperSpatialLogKernel p
      ∂<•paperSignedSquare (paperFluctuationMeasure μ z)) = paperSpatialModulatedEnergy μ z :=
  paper_fluctuation_half_interaction μ z

example {β : ℝ} (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {N : ℕ} (hN : 0 < N) (z : Fin N → ℂ) (hz : Function.Injective z) :
    ((paperSignedSquare ((paperEmpiricalMeasure z).toSignedMeasure -
      (R.measure : Measure ℂ).toSignedMeasure)).restrict paperSpatialOffDiagonal).Integrable
        paperSpatialLogKernel ∧
    paperSpatialModulatedEnergy (R.measure : Measure ℂ) z = equilibriumModulatedEnergy R.density z :=
  (paper_reference_spatial_bridge hβ R hN z hz).2

example {β : ℝ} (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {N : ℕ} (hN : 0 < N) (t : ℝ) :
    paperSpatialPartition N t R = equilibriumReferencePartition N t R :=
  paper_reference_spatial_partition_eq hβ R hN t

example {β t : ℝ} (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {N : ℕ} (hN : 0 < N) (ht : 0 ≤ t) :
    Integrable (fun z : Fin N → ℂ => Real.exp (-t * paperSpatialModulatedEnergy (R.measure : Measure ℂ) z))
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) :=
  paper_reference_spatial_exponential_integrable hβ R hN ht

example {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ β (_hβ : 0 < β) (R : EquilibriumConstructedReference β),
      ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ T → paperSpatialPartition N t R ≤ C :=
  paper_spatial_partition_uniform hT

example {β : ℝ} (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    (N : ℕ) (hN : 2 ≤ N) (u : CoulombFormDomain N hβ) :
    entropy (coulombMeasure N β) (fun z => (coulombFormValueL N hβ u z) ^ 2) ≤
      (((2 / paperLabeledRateFromReference hβ R) * coulombFormEnergy N hβ u : ℝ) : EReal) :=
  paper_full_labeled_lsi_via_spatial_reference hβ R N hN u

example {β : ℝ} (hβ : 0 < β) (R : EquilibriumConstructedReference β) :
    0 < paperLabeledRateFromReference hβ R := paperLabeledRateFromReference_pos_via_spatial hβ R

example {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, a ≤ β → β ≤ b →
      ∀ R : EquilibriumConstructedReference β, ∀ N : ℕ, 2 ≤ N →
        equilibriumReferencePartition N β R ≤ C ∧ equilibriumReferencePartition N (6 * β) R ≤ C :=
  paper_reference_partition_pair_compact_via_spatial ha hab

#check @RepulsiveCoulomb.PaperRoute.paperSignedSquare
#print axioms RepulsiveCoulomb.PaperRoute.paperSignedSquare
#check @RepulsiveCoulomb.PaperRoute.paper_signed_hasProd
#print axioms RepulsiveCoulomb.PaperRoute.paper_signed_hasProd
#check @RepulsiveCoulomb.PaperRoute.paper_signed_difference_square
#print axioms RepulsiveCoulomb.PaperRoute.paper_signed_difference_square
#check @RepulsiveCoulomb.PaperRoute.paper_signed_square_smul
#print axioms RepulsiveCoulomb.PaperRoute.paper_signed_square_smul
#check @RepulsiveCoulomb.PaperRoute.paper_signed_restricted_square_integrable
#print axioms RepulsiveCoulomb.PaperRoute.paper_signed_restricted_square_integrable
#check @RepulsiveCoulomb.PaperRoute.paper_signed_restricted_square_integral
#print axioms RepulsiveCoulomb.PaperRoute.paper_signed_restricted_square_integral
#check @RepulsiveCoulomb.PaperRoute.paperCountingMeasure
#print axioms RepulsiveCoulomb.PaperRoute.paperCountingMeasure
#check @RepulsiveCoulomb.PaperRoute.paperEmpiricalMeasure
#print axioms RepulsiveCoulomb.PaperRoute.paperEmpiricalMeasure
#check @RepulsiveCoulomb.PaperRoute.paperSpatialOffDiagonal
#print axioms RepulsiveCoulomb.PaperRoute.paperSpatialOffDiagonal
#check @RepulsiveCoulomb.PaperRoute.paperSpatialOffDiagonal_measurable
#print axioms RepulsiveCoulomb.PaperRoute.paperSpatialOffDiagonal_measurable
#check @RepulsiveCoulomb.PaperRoute.paperSpatialLogKernel
#print axioms RepulsiveCoulomb.PaperRoute.paperSpatialLogKernel
#check @RepulsiveCoulomb.PaperRoute.paperSpatialModulatedF
#print axioms RepulsiveCoulomb.PaperRoute.paperSpatialModulatedF
#check @RepulsiveCoulomb.PaperRoute.paperSpatialModulatedEnergy
#print axioms RepulsiveCoulomb.PaperRoute.paperSpatialModulatedEnergy
#check @RepulsiveCoulomb.PaperRoute.paperFluctuationMeasure
#print axioms RepulsiveCoulomb.PaperRoute.paperFluctuationMeasure
#check @RepulsiveCoulomb.PaperRoute.paper_fluctuation_half_interaction
#print axioms RepulsiveCoulomb.PaperRoute.paper_fluctuation_half_interaction
#check @RepulsiveCoulomb.PaperRoute.paper_empirical_probability
#print axioms RepulsiveCoulomb.PaperRoute.paper_empirical_probability
#check @RepulsiveCoulomb.PaperRoute.paper_fluctuation_total_mass
#print axioms RepulsiveCoulomb.PaperRoute.paper_fluctuation_total_mass
#check @RepulsiveCoulomb.PaperRoute.paper_empirical_spatial_integrals
#print axioms RepulsiveCoulomb.PaperRoute.paper_empirical_spatial_integrals
#check @RepulsiveCoulomb.PaperRoute.paper_reference_spatial_bridge
#print axioms RepulsiveCoulomb.PaperRoute.paper_reference_spatial_bridge
#check @RepulsiveCoulomb.PaperRoute.paper_reference_spatial_energy_ae
#print axioms RepulsiveCoulomb.PaperRoute.paper_reference_spatial_energy_ae
#check @RepulsiveCoulomb.PaperRoute.paperSpatialPartition
#print axioms RepulsiveCoulomb.PaperRoute.paperSpatialPartition
#check @RepulsiveCoulomb.PaperRoute.paper_reference_spatial_exponential_integrable
#print axioms RepulsiveCoulomb.PaperRoute.paper_reference_spatial_exponential_integrable
#check @RepulsiveCoulomb.PaperRoute.paper_reference_spatial_partition_eq
#print axioms RepulsiveCoulomb.PaperRoute.paper_reference_spatial_partition_eq
#check @RepulsiveCoulomb.PaperRoute.paper_spatial_partition_uniform
#print axioms RepulsiveCoulomb.PaperRoute.paper_spatial_partition_uniform

#check @RepulsiveCoulomb.PaperRoute.paper_reference_partition_pair_via_spatial
#print axioms RepulsiveCoulomb.PaperRoute.paper_reference_partition_pair_via_spatial
#check @RepulsiveCoulomb.PaperRoute.paper_reference_partition_pair_compact_via_spatial
#print axioms RepulsiveCoulomb.PaperRoute.paper_reference_partition_pair_compact_via_spatial
#check @RepulsiveCoulomb.PaperRoute.paperLabeledRateFromReference_pos_via_spatial
#print axioms RepulsiveCoulomb.PaperRoute.paperLabeledRateFromReference_pos_via_spatial
#check @RepulsiveCoulomb.PaperRoute.paper_full_labeled_lsi_via_spatial_reference
#print axioms RepulsiveCoulomb.PaperRoute.paper_full_labeled_lsi_via_spatial_reference

open Lean Elab Command in
private partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env d
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env d

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := #[``RepulsiveCoulomb.PaperRoute.paper_reference_partition_pair_via_spatial, ``RepulsiveCoulomb.PaperRoute.paper_reference_partition_pair_compact_via_spatial, ``RepulsiveCoulomb.PaperRoute.paperLabeledRateFromReference_pos_via_spatial, ``RepulsiveCoulomb.PaperRoute.paper_full_labeled_lsi_via_spatial_reference, ``RepulsiveCoulomb.PaperRoute.paperSignedSquare, ``RepulsiveCoulomb.PaperRoute.paper_signed_hasProd, ``RepulsiveCoulomb.PaperRoute.paper_signed_difference_square, ``RepulsiveCoulomb.PaperRoute.paper_signed_square_smul, ``RepulsiveCoulomb.PaperRoute.paper_signed_restricted_square_integrable, ``RepulsiveCoulomb.PaperRoute.paper_signed_restricted_square_integral, ``RepulsiveCoulomb.PaperRoute.paperCountingMeasure, ``RepulsiveCoulomb.PaperRoute.paperEmpiricalMeasure, ``RepulsiveCoulomb.PaperRoute.paperSpatialOffDiagonal, ``RepulsiveCoulomb.PaperRoute.paperSpatialOffDiagonal_measurable, ``RepulsiveCoulomb.PaperRoute.paperSpatialLogKernel, ``RepulsiveCoulomb.PaperRoute.paperSpatialModulatedF, ``RepulsiveCoulomb.PaperRoute.paperSpatialModulatedEnergy, ``RepulsiveCoulomb.PaperRoute.paperFluctuationMeasure, ``RepulsiveCoulomb.PaperRoute.paper_fluctuation_half_interaction, ``RepulsiveCoulomb.PaperRoute.paper_empirical_probability, ``RepulsiveCoulomb.PaperRoute.paper_fluctuation_total_mass, ``RepulsiveCoulomb.PaperRoute.paper_empirical_spatial_integrals, ``RepulsiveCoulomb.PaperRoute.paper_reference_spatial_bridge, ``RepulsiveCoulomb.PaperRoute.paper_reference_spatial_energy_ae, ``RepulsiveCoulomb.PaperRoute.paperSpatialPartition, ``RepulsiveCoulomb.PaperRoute.paper_reference_spatial_exponential_integrable, ``RepulsiveCoulomb.PaperRoute.paper_reference_spatial_partition_eq, ``RepulsiveCoulomb.PaperRoute.paper_spatial_partition_uniform]
  let (_, deps) := (roots.forM (visit env)).run ({} : NameSet)
  for n in #[`RepulsiveCoulomb.PaperRoute.paper_full_labeled_lsi_of_reference, `sorryAx, `RepulsiveCoulomb.equilibriumConstructedReference,
      `RepulsiveCoulomb.equilibriumConstructedReference_nonempty,
      `RepulsiveCoulomb.equilibriumCanonical_exists_global_minimizer,
      `RepulsiveCoulomb.equilibriumCanonicalMinimizers_unique,
      `RepulsiveCoulomb.equilibrium_pointwise_EL_contDiff,
      `RepulsiveCoulomb.equilibriumReferencePartition_uniform,
      `RepulsiveCoulomb.equilibriumConstructedReference_partition_uniform] do
    if deps.contains n then throwError "Forbidden selected producer: {n}"
  for n in deps do
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
  let (_, endpointDeps) := (visit env ``paper_spatial_partition_uniform).run ({} : NameSet)
  for n in #[``paper_signed_difference_square,
      ``paper_signed_restricted_square_integral,
      ``paper_empirical_spatial_integrals, ``paper_reference_spatial_bridge,
      ``paper_reference_spatial_energy_ae,
      ``MeasureTheory.VectorMeasure.prod_eq_of_forall_apply_prod,
      ``MeasureTheory.VectorMeasure.integral_sub_vectorMeasure,
      ``MeasureTheory.VectorMeasure.integral_toSignedMeasure,
      ``RepulsiveCoulomb.equilibriumReference_product_injective_ae,
      ``RepulsiveCoulomb.equilibriumObjective_finite_logEnergy_integrable,
      ``paper_reference_partition_uniform, ``paper_dg_fixed_coupling,
      ``exponential_integral_holder] do
    unless endpointDeps.contains n do throwError "Required actual representation/partition producer absent: {n}"
  let (_, bridgeDeps) := (visit env ``paper_reference_spatial_bridge).run ({} : NameSet)
  for n in #[``paper_signed_hasProd, ``paper_signed_restricted_square_integrable] do
    unless bridgeDeps.contains n do throwError "Required product/integrability proof absent: {n}"
  let (_, finalDeps) := (visit env ``paper_full_labeled_lsi_via_spatial_reference).run ({} : NameSet)
  for n in #[``paper_spatial_partition_uniform, ``paper_reference_spatial_partition_eq,
      ``paper_reference_partition_pair_via_spatial, ``paper_reference_spatial_bridge,
      ``paper_full_labeled_poincare_via_resolvent, ``exponential_integral_holder] do
    unless finalDeps.contains n do throwError "Final LSI misses spatial or resolvent producer: {n}"
  logInfo m!"PASS: {roots.size} declarations; actual signed product, variation-integrable spatial restriction, injective then a.e. canonical identity."


end IntegratedScope14

namespace IntegratedScope15

/- Scoped semantic consumer; namespace/import-context adaptations are recorded in generation-manifest.json. -/


open Set Metric MeasureTheory Filter
open scoped ENNReal BigOperators Topology
open RepulsiveCoulomb RepulsiveCoulomb.PaperRoute

-- Actual bad-score area from the new maximal-route force.
example {m : ℕ} {γ Q R : ℝ} (hγ : 0 < γ) (hR : 0 < R)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hQ : ∑ j, a j ≤ Q) :
    volume (pointScoreBadAnnulus γ a y R) ≤
      ENNReal.ofReal ((256 * Real.pi * Q ^ 2 / γ ^ 2) / R ^ 2) :=
  atomic_pointScoreBadAnnulus_volume_le hγ hR ha y hQ

example (γ Q : ℝ) : atomicScoreBadAreaConstant γ Q =
    4 * (64 * Real.pi) * Q ^ 2 / γ ^ 2 := by
  unfold atomicScoreBadAreaConstant
  ring

example (γ Q : ℝ) : atomicScoreAnnularMassConstant γ Q =
    Real.sqrt (256 * Real.pi * Q ^ 2 / γ ^ 2) * (planarLadyzhenskayaConstant : ℝ) := rfl

example (γ : ℝ) : atomicScoreAnnularMassConstant γ 0 = 0 := by
  simp [atomicScoreAnnularMassConstant, atomicScoreBadAreaConstant]

-- The new score uncertainty is produced, not supplied as an external premise.
example {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ U : ℝ, 0 < U ∧ ∀ (m : ℕ) (a : Fin m → ℝ), (∀ j, 0 ≤ a j) →
      ∀ y : Fin m → ℂ, (∑ j, a j ≤ Q) →
      ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      (∫ x : ℂ, ‖x‖ ^ 2 * φ x ^ 2) ≤ U *
        ((∫ x : ℂ, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2) +
          (∫ x : ℂ, ‖pointScore γ a y x‖ ^ 2 * φ x ^ 2) + (∫ x : ℂ, φ x ^ 2)) :=
  atomic_pointScore_uncertainty hγ

-- The U-bound is configuration-uniform and acts on the original physical core.
example {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (a : Fin m → ℝ), (∀ j, 0 ≤ a j) →
      ∀ y : Fin m → ℂ, (∑ j, a j ≤ Q) →
      ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      (∫ x, ‖x‖ ^ 2 * φ x ^ 2 ∂pointMeasure γ a y) ≤ C *
        ((∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
          (∫ x, φ x ^ 2 ∂pointMeasure γ a y)) := atomic_pointCore_weighted_moment_bound hγ

-- Exact interface needed by the Gaussian global PI/SPI consumer.
example {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
      (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ u : PointFormDomain hγ ha y,
      Integrable (fun x : ℂ => ‖x‖ ^ 2 * (pointFormValueL hγ ha y u x) ^ 2) (pointMeasure γ a y) ∧
      (∫ x, ‖x‖ ^ 2 * (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y) ≤ C * ‖u‖ ^ 2 :=
  atomic_pointForm_weighted_moment_bound hγ

-- All three parameters, including zero total exponent, share one preconfiguration constant.
example (γ : ℝ) (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
      (y : Fin m → ℂ), (∑ j, a j ≤ 0) → ∀ u : PointFormDomain hγ ha y,
      Integrable (fun x : ℂ => ‖x‖ ^ 2 * (pointFormValueL hγ ha y u x) ^ 2) (pointMeasure γ a y) ∧
      (∫ x, ‖x‖ ^ 2 * (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y) ≤ C *
        ((∫ x, ‖pointFormGradientL hγ ha y u x‖ ^ 2 ∂pointMeasure γ a y) +
          (∫ x, (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y)) :=
  atomic_pointForm_uniform_quadratic_moment hγ

#check @atomic_pointScore_small_region_measure
#check @atomicScoreBadAreaConstant_nonneg
#check @atomic_pointScoreBadAnnulus_volume_le
#check @atomic_pointScoreBadAnnulus_volume_ne_top
#check @atomic_pointScoreBadAnnulus_real_volume_le
#check @atomicScoreAnnularMassConstant_nonneg
#check @atomic_pointScore_bad_annulus_mass_cutoff
#check @atomic_pointScore_bad_annulus_mass_young
#check @atomic_pointScore_bad_annulus_localized
#check @atomic_pointScore_annular_uniform_bound
#check @atomic_pointScore_finite_moment_bound
#check @atomic_pointScore_uncertainty
#check @atomic_pointCore_weighted_moment_bound
#check @atomic_pointForm_weighted_moment_bound
#check @atomic_pointForm_uniform_quadratic_moment

#print axioms atomic_pointScore_small_region_measure
#print axioms atomicScoreBadAreaConstant_nonneg
#print axioms atomic_pointScoreBadAnnulus_volume_le
#print axioms atomic_pointScoreBadAnnulus_volume_ne_top
#print axioms atomic_pointScoreBadAnnulus_real_volume_le
#print axioms atomicScoreAnnularMassConstant_nonneg
#print axioms atomic_pointScore_bad_annulus_mass_cutoff
#print axioms atomic_pointScore_bad_annulus_mass_young
#print axioms atomic_pointScore_bad_annulus_localized
#print axioms atomic_pointScore_annular_uniform_bound
#print axioms atomic_pointScore_finite_moment_bound
#print axioms atomic_pointScore_uncertainty
#print axioms atomic_pointCore_weighted_moment_bound
#print axioms atomic_pointForm_weighted_moment_bound
#print axioms atomic_pointForm_uniform_quadratic_moment

namespace AtomicScoreMomentAudit
open Lean Elab Command
partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env d
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env d
run_cmd do
  let env ← getEnv
  let roots := #[``atomic_pointScore_small_region_measure,
    ``atomicScoreBadAreaConstant_nonneg,
    ``atomic_pointScoreBadAnnulus_volume_le,
    ``atomic_pointScoreBadAnnulus_volume_ne_top,
    ``atomic_pointScoreBadAnnulus_real_volume_le,
    ``atomicScoreAnnularMassConstant_nonneg,
    ``atomic_pointScore_bad_annulus_mass_cutoff,
    ``atomic_pointScore_bad_annulus_mass_young,
    ``atomic_pointScore_bad_annulus_localized,
    ``atomic_pointScore_annular_uniform_bound,
    ``atomic_pointScore_finite_moment_bound,
    ``atomic_pointScore_uncertainty,
    ``atomic_pointCore_weighted_moment_bound,
    ``atomic_pointForm_weighted_moment_bound,
    ``atomic_pointForm_uniform_quadratic_moment]
  let (_, deps) := (roots.forM (visit env)).run ({} : NameSet)
  for n in #[`RepulsiveCoulomb.pointLogForce_weak_l2,
    `RepulsiveCoulomb.pointLogForce_weak_l2_of_total_le,
    `RepulsiveCoulomb.truncatedLogKernel,
    `RepulsiveCoulomb.pointTruncatedPotential,
    `RepulsiveCoulomb.pointLogForce_le_truncated,
    `RepulsiveCoulomb.inverseNorm_le_truncated,
    `RepulsiveCoulomb.integral_pointTruncatedPotential,
    `RepulsiveCoulomb.pointScore_small_region_measure,
    `RepulsiveCoulomb.pointScoreBadAreaConstant,
    `RepulsiveCoulomb.pointScoreBadAnnulus_volume_le,
    `RepulsiveCoulomb.pointScoreBadAnnulus_volume_ne_top,
    `RepulsiveCoulomb.pointScoreBadAnnulus_real_volume_le,
    `RepulsiveCoulomb.pointScoreAnnularMassConstant,
    `RepulsiveCoulomb.pointScore_bad_annulus_mass_cutoff,
    `RepulsiveCoulomb.pointScore_bad_annulus_mass_young,
    `RepulsiveCoulomb.pointScore_bad_annulus_localized,
    `RepulsiveCoulomb.pointScore_annular_uniform_bound,
    `RepulsiveCoulomb.pointScore_finite_moment_bound,
    `RepulsiveCoulomb.pointScore_uncertainty,
    `RepulsiveCoulomb.pointCore_weighted_moment_bound,
    `RepulsiveCoulomb.pointForm_weighted_moment_bound,
    `RepulsiveCoulomb.pointForm_uniform_quadratic_moment,
    `RepulsiveCoulomb.pointCore_uniform_exterior_mass, `sorryAx] do
    if deps.contains n then throwError "Forbidden transitive producer or chosen constant: {n}"
  for n in deps do
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
  let (_, endpointDeps) := (visit env ``atomic_pointForm_uniform_quadratic_moment).run ({} : NameSet)
  for n in #[``planar_vitali_two_measure_bound,
    ``Vitali.exists_disjoint_subfamily_covering_enlargement_ball,
    ``positiveDistanceLayer_integrable,
    ``finite_inverse_sum_le_of_ball_growth,
    ``pointLogForce_weak_l2_atomic_maximal,
    ``atomic_pointScore_small_region_measure,
    ``atomic_pointScoreBadAnnulus_volume_le,
    ``atomic_pointScore_bad_annulus_mass_cutoff,
    ``atomic_pointScore_bad_annulus_mass_young,
    ``atomic_pointScore_bad_annulus_localized,
    ``atomic_pointScore_annular_uniform_bound,
    ``atomic_pointScore_finite_moment_bound,
    ``atomic_pointScore_uncertainty,
    ``atomic_pointCore_weighted_moment_bound,
    ``atomic_pointForm_weighted_moment_bound,
    ``RepulsiveCoulomb.pointScore_good_quadratic_bound,
    ``RepulsiveCoulomb.pointScore_annular_mass_decomposition,
    ``RepulsiveCoulomb.physical_gradient_mul,
    ``RepulsiveCoulomb.annularCutoff_tsupport_strict,
    ``RepulsiveCoulomb.planar_region_mass_ladyzhenskaya,
    ``RepulsiveCoulomb.sqrt_product_young,
    ``RepulsiveCoulomb.annular_product_mass_le,
    ``RepulsiveCoulomb.annular_product_energy_le,
    ``RepulsiveCoulomb.dyadicScoreAnnuli_integral_sum_le,
    ``RepulsiveCoulomb.dyadicScoreAnnuli_weighted_integral_sum_le,
    ``RepulsiveCoulomb.dyadicScoreAnnuli_moment_integral,
    ``RepulsiveCoulomb.pointCore_score_energy_integrable,
    ``RepulsiveCoulomb.pointCore_exists_dyadic_outer_radius,
    ``RepulsiveCoulomb.exists_annularCutoff_gradient_bound,
    ``RepulsiveCoulomb.pointGroundState_energy_identity,
    ``RepulsiveCoulomb.pointGroundState_mass_integral,
    ``RepulsiveCoulomb.pointGroundState_moment_integral,
    ``RepulsiveCoulomb.pointFormCore_approximation,
    ``RepulsiveCoulomb.lintegral_le_of_ae_tendsto_of_eventually_bound,
    ``RepulsiveCoulomb.pointForm_moment_bound_of_core,
    ``RepulsiveCoulomb.pointForm_norm_sq,
    ``RepulsiveCoulomb.pointFormValue_norm_sq_eq_integral,
    ``RepulsiveCoulomb.pointFormEnergy_eq_integral] do
    unless endpointDeps.contains n do throwError "Endpoint bypasses actual producer: {n}"
  logInfo "PASS: literal score-area256*pi, new K, zero-cap and configuration-uniform core/full-form consumers."
  logInfo "PASS: finite-atomic maximal force, Ladyzhenskaya, cutoff/Young/localization, finite overlap, core integrability, actual ground-state identities and Fatou are load-bearing."
  logInfo "PASS: type+opaque-value dependency closure, with original scoped import census retained separately; old weak-force, bad-area, uncertainty and unconditional moment producers/constant witnesses excluded; foundational axioms only."
end AtomicScoreMomentAudit


end IntegratedScope15

namespace IntegratedScope16

/- Scoped semantic consumer; namespace/import-context adaptations are recorded in generation-manifest.json. -/


open Set MeasureTheory Filter
open scoped ENNReal Topology BigOperators
open RepulsiveCoulomb RepulsiveCoulomb.PaperRoute

example {γ Q : ℝ} (hγ : 0 < γ) (hQ : 0 ≤ Q) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ (m : ℕ) (a : Fin m → ℝ) (y : Fin m → ℂ),
      (∀ j, 0 ≤ a j) → (∑ j, a j ≤ Q) →
      (1 / 2 : ENNReal) ≤ pointMeasure γ a y (Metric.ball (0 : ℂ) R) :=
  disk_half_mass_ball hγ hQ

example {γ : ℝ} (hγ : 0 < γ) : ∃ R : ℝ, 1 ≤ R ∧ UniformHalfMassBall γ 0 R :=
  disk_half_mass_ball hγ le_rfl

example {γ Q : ℝ} (hγ : 0 < γ) (hQ : 0 ≤ Q) : IsFiniteMeasure (diskEnvelopeMeasure γ Q) :=
  diskEnvelopeMeasure_finite hγ hQ

#check @diskEnvelopeMeasure_finite
#check @pointMeasure_le_diskEnvelopeMeasure
#check @diskEnvelopeMeasure_tail_tendsto
#check @disk_half_mass_ball
#print axioms diskEnvelopeMeasure_finite
#print axioms pointMeasure_le_diskEnvelopeMeasure
#print axioms diskEnvelopeMeasure_tail_tendsto
#print axioms disk_half_mass_ball

open Lean Elab Command in
private partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env d
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env d

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := #[``diskEnvelopeMeasure, ``diskEnvelopeMeasure_finite,
    ``pointMeasure_le_diskEnvelopeMeasure, ``diskEnvelopeMeasure_tail_tendsto,
    ``disk_half_mass_ball]
  let (_, deps) := (roots.forM (visit env)).run ({} : NameSet)
  for n in #[`RepulsiveCoulomb.pointMeasure_half_mass_ball,
      `RepulsiveCoulomb.pointPartition_lower_uniform,
      `RepulsiveCoulomb.pointLowerConstant,
      `RepulsiveCoulomb.pointMeasure_le_envelopeMeasure,
      `RepulsiveCoulomb.pointSobolevKappa,
      `RepulsiveCoulomb.pointGaussian_uniform_local_geometry,
      `RepulsiveCoulomb.pointCore_uniform_poincare,
      `RepulsiveCoulomb.pointCore_weighted_moment_bound,
      `sorryAx] do
    if deps.contains n then throwError "Forbidden actual transitive dependency: {n}"
  for n in deps do
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
  let (_, endpointDeps) := (visit env ``disk_half_mass_ball).run ({} : NameSet)
  for n in #[``RepulsiveCoulomb.pointMeasure_le_disk_envelope,
      ``RepulsiveCoulomb.pointPartition_unitDisk_lower_uniform,
      ``RepulsiveCoulomb.unitDisk_raw_weight_jensen,
      ``RepulsiveCoulomb.unitDisk_log_average_lower,
      ``diskEnvelopeMeasure_tail_tendsto] do
    unless endpointDeps.contains n do throwError "Required literal disk producer missing: {n}"
  logInfo m!"PASS: {roots.size} declarations; literal unit-disk/Jensen normalization is load-bearing; no annular witness selected."


end IntegratedScope16

namespace IntegratedOriginalReferenceInstances
open Set MeasureTheory InformationTheory Filter
open scoped ENNReal Topology BigOperators
open RepulsiveCoulomb RepulsiveCoulomb.PaperRoute

theorem original_canonical_splitting {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    Measure.map (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β) =
      (Measure.pi (fun _ : Fin N => ((thermalConstructedReference β hβ).measure : Measure ℂ))).tilted
        (fun z => -β * equilibriumModulatedEnergy (thermalConstructedReference β hβ).density z) :=
  equilibriumReference_coulombMeasure_eq_tilted hβ (thermalConstructedReference β hβ) N

theorem original_canonical_partition {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    equilibriumReferencePartition N β (thermalConstructedReference β hβ) =
      equilibriumSplittingConstant N (thermalConstructedReference β hβ) * (coulombPartition N β).toReal :=
  equilibriumReferencePartition_canonical_eq hβ (thermalConstructedReference β hβ) N

theorem original_spatial_collisionfree {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (hN : 0 < N) (z : Fin N → ℂ) (hz : Function.Injective z) :
    paperSpatialModulatedEnergy ((thermalConstructedReference β hβ).measure : Measure ℂ) z =
      equilibriumModulatedEnergy (thermalConstructedReference β hβ).density z :=
  (paper_reference_spatial_bridge hβ (thermalConstructedReference β hβ) hN z hz).2.2

theorem original_spatial_partition {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) (t : ℝ) :
    paperSpatialPartition N t (thermalConstructedReference β hβ) =
      equilibriumReferencePartition N t (thermalConstructedReference β hβ) :=
  paper_reference_spatial_partition_eq hβ (thermalConstructedReference β hβ) hN t

theorem original_partition_uniform {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ β (hβ : 0 < β), ∀ N : ℕ, 2 ≤ N →
      ∀ t : ℝ, 0 ≤ t → t ≤ T → paperSpatialPartition N t (thermalConstructedReference β hβ) ≤ C := by
  obtain ⟨C, hC, hb⟩ := paper_spatial_partition_uniform hT
  exact ⟨C, hC, fun β hβ N hN t ht htT => hb β hβ (thermalConstructedReference β hβ) N hN t ht htT⟩

/-- The original competitor Q is arbitrary labeled; its stated finite-KL
and thermal B-integrability premises are preserved verbatim. -/
theorem original_entropy_factorization {N : ℕ} {β ℓ : ℝ}
    (hβ : 0 < β) (hℓ : 1 < ℓ)
    {Q : Measure (CoulombConfig (N + 1))} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB (thermalConstructedReference β hβ)) Q) :
    (1 - 1 / ℓ) * (klDiv Q (coulombMeasure (N + 1) β)).toReal -
      conditionalEntropyBranchDefect (N := N + 1) (thermalConstructedReference β hβ) ℓ ≤
        (conditionalEntropyBranchCoulombS hβ Q).toReal :=
  paper_entropy_factorization_disk hβ hℓ (thermalConstructedReference β hβ) hKL hB

theorem original_compact_all_ell_defect {a b ℓ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hℓ : 1 < ℓ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ β : ℝ, ∀ hlo : a ≤ β, β ≤ b →
      0 ≤ paperUniformEntropyDefectAt (thermalConstructedReference β (ha.trans_le hlo)) ℓ ∧
      paperUniformEntropyDefectAt (thermalConstructedReference β (ha.trans_le hlo)) ℓ ≤ D ∧
      ∀ N : ℕ, 2 ≤ N →
        conditionalEntropyBranchDefect (N := N) (thermalConstructedReference β (ha.trans_le hlo)) ℓ ≤
          paperUniformEntropyDefectAt (thermalConstructedReference β (ha.trans_le hlo)) ℓ := by
  obtain ⟨D, hD, hb⟩ := paper_uniform_defectAt_compact_disk ha hab hℓ
  exact ⟨D, hD, fun β hlo hhi => hb β hlo hhi (thermalConstructedReference β (ha.trans_le hlo))⟩

theorem original_fixed_all_ell_defect {β ℓ : ℝ} (hβ : 0 < β) (hℓ : 1 < ℓ) :
    0 ≤ paperUniformEntropyDefectAt (thermalConstructedReference β hβ) ℓ ∧
      ∃ D : ℝ, paperUniformEntropyDefectAt (thermalConstructedReference β hβ) ℓ ≤ D ∧
        ∀ N : ℕ, 2 ≤ N →
          conditionalEntropyBranchDefect (N := N) (thermalConstructedReference β hβ) ℓ ≤
            paperUniformEntropyDefectAt (thermalConstructedReference β hβ) ℓ :=
  paper_uniform_defectAt_finite_disk hβ hℓ (thermalConstructedReference β hβ)

example {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x : ℂ => Real.log (pointConformalDensity a y x) * Laplacian.laplacian φ x) ∧
      -(∫ x : ℂ, Real.log (pointConformalDensity a y x) * Laplacian.laplacian φ x) =
        -Real.pi * ∑ j, a j * φ (y j) :=
  PointCurvature.pointConformalDensity_distributional_curvature ha y hφ hφc
end IntegratedOriginalReferenceInstances


#check @IntegratedOriginalReferenceInstances.original_canonical_splitting
#print axioms IntegratedOriginalReferenceInstances.original_canonical_splitting

#check @IntegratedOriginalReferenceInstances.original_canonical_partition
#print axioms IntegratedOriginalReferenceInstances.original_canonical_partition

#check @IntegratedOriginalReferenceInstances.original_spatial_collisionfree
#print axioms IntegratedOriginalReferenceInstances.original_spatial_collisionfree

#check @IntegratedOriginalReferenceInstances.original_spatial_partition
#print axioms IntegratedOriginalReferenceInstances.original_spatial_partition

#check @IntegratedOriginalReferenceInstances.original_partition_uniform
#print axioms IntegratedOriginalReferenceInstances.original_partition_uniform

#check @IntegratedOriginalReferenceInstances.original_entropy_factorization
#print axioms IntegratedOriginalReferenceInstances.original_entropy_factorization

#check @IntegratedOriginalReferenceInstances.original_compact_all_ell_defect
#print axioms IntegratedOriginalReferenceInstances.original_compact_all_ell_defect

#check @IntegratedOriginalReferenceInstances.original_fixed_all_ell_defect
#print axioms IntegratedOriginalReferenceInstances.original_fixed_all_ell_defect

namespace IntegratedGlobalAudit
open Lean Elab Command
open RepulsiveCoulomb RepulsiveCoulomb.PaperRoute
/-- Every physical type is traversed before the one permitted cited body cut. -/
partial def visit (env : Environment) (authored : Bool) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visit env authored d
    if authored && n == ``RepulsiveCoulomb.PaperRoute.paper_dg_fixed_coupling then return
    if let some v := ci.value? (allowOpaque := true) then
      for d in v.getUsedConstants do visit env authored d
run_cmd do
  let env ← getEnv
  let roots := #[``RepulsiveCoulomb.PaperRoute.PointCurvature.pointConformalDensity_distributional_curvature, ``RepulsiveCoulomb.PaperRoute.atomic_pointCore_weighted_moment_bound, ``RepulsiveCoulomb.PaperRoute.atomic_pointForm_uniform_quadratic_moment, ``RepulsiveCoulomb.PaperRoute.atomic_pointForm_weighted_moment_bound, ``RepulsiveCoulomb.PaperRoute.atomic_pointScore_uncertainty, ``RepulsiveCoulomb.PaperRoute.core_defective_lsi_of_gaussian_spi, ``RepulsiveCoulomb.PaperRoute.core_global_superPoincare, ``RepulsiveCoulomb.PaperRoute.core_global_superPoincare_small, ``RepulsiveCoulomb.PaperRoute.core_poincare_of_raw_sobolev, ``RepulsiveCoulomb.PaperRoute.disk_half_mass_ball, ``RepulsiveCoulomb.PaperRoute.form_global_superPoincare, ``RepulsiveCoulomb.PaperRoute.form_poincare_of_raw_sobolev, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_centered_moment_tendsto, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_energy_tendsto, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_fderiv_ae_tendsto, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_hasFDerivAt, ``RepulsiveCoulomb.PaperRoute.original_gaussian_local_geometry, ``RepulsiveCoulomb.PaperRoute.original_gaussian_local_sobolev_locallyLipschitz, ``RepulsiveCoulomb.PaperRoute.original_gaussian_strong_sobolev_closedBall, ``RepulsiveCoulomb.PaperRoute.original_point_doubling_and_locallyLipschitz_PI, ``RepulsiveCoulomb.PaperRoute.original_point_localGeometry, ``RepulsiveCoulomb.PaperRoute.original_point_physical_weak_one_two, ``RepulsiveCoulomb.PaperRoute.original_raw_local_sobolev_locallyLipschitz, ``RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_c1_center, ``RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_closedBall, ``RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_locallyLipschitz, ``RepulsiveCoulomb.PaperRoute.original_weighted_full_domain, ``RepulsiveCoulomb.PaperRoute.paperCompactLabeledRateFromReferenceFamily, ``RepulsiveCoulomb.PaperRoute.paperCwt_scaling, ``RepulsiveCoulomb.PaperRoute.paperLabeledRateFromReference, ``RepulsiveCoulomb.PaperRoute.paperOriginalCompactLabeledRate, ``RepulsiveCoulomb.PaperRoute.paperOriginalCompactLabeledRate_le_optimal, ``RepulsiveCoulomb.PaperRoute.paperOriginalCompactLabeledRate_pos, ``RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate, ``RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate_le_optimal, ``RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate_pos, ``RepulsiveCoulomb.PaperRoute.paperRhoWt_scaling, ``RepulsiveCoulomb.PaperRoute.paperTranspositionKernel_identity, ``RepulsiveCoulomb.PaperRoute.paperTranspositionKernel_row_sum, ``RepulsiveCoulomb.PaperRoute.paperTranspositionKernel_swap, ``RepulsiveCoulomb.PaperRoute.paperUniformTransposition_gap_exact, ``RepulsiveCoulomb.PaperRoute.paper_center_imaginary_form_witness, ``RepulsiveCoulomb.PaperRoute.paper_center_real_form_witness, ``RepulsiveCoulomb.PaperRoute.paper_common_phase_identity, ``RepulsiveCoulomb.PaperRoute.paper_complete_graph_relative_gradient, ``RepulsiveCoulomb.PaperRoute.paper_coulomb_potential_distribution, ``RepulsiveCoulomb.PaperRoute.paper_dbar_core_distance, ``RepulsiveCoulomb.PaperRoute.paper_dbar_graph_distance, ``RepulsiveCoulomb.PaperRoute.paper_dbar_kernel_holomorphic, ``RepulsiveCoulomb.PaperRoute.paper_dg_fixed_coupling, ``RepulsiveCoulomb.PaperRoute.paper_entropy_factorization_disk, ``RepulsiveCoulomb.PaperRoute.paper_exp_integral_inverse_power_concavity, ``RepulsiveCoulomb.PaperRoute.paper_finite_defect_nonneg_disk, ``RepulsiveCoulomb.PaperRoute.paper_fixed_particle_compact_temperature, ``RepulsiveCoulomb.PaperRoute.paper_fixed_particle_form_compact, ``RepulsiveCoulomb.PaperRoute.paper_fixed_particle_kernel_constants, ``RepulsiveCoulomb.PaperRoute.paper_fixed_particle_operator_selfAdjoint, ``RepulsiveCoulomb.PaperRoute.paper_fixed_particle_poincare_via_resolvent, ``RepulsiveCoulomb.PaperRoute.paper_fixed_particle_resolvent_compact, ``RepulsiveCoulomb.PaperRoute.paper_full_defective_compact_via_disk_reference_family, ``RepulsiveCoulomb.PaperRoute.paper_full_defective_of_reference_bounds_of_exp_integrable, ``RepulsiveCoulomb.PaperRoute.paper_full_labeled_lsi_original, ``RepulsiveCoulomb.PaperRoute.paper_full_labeled_poincare_uniform_via_resolvent, ``RepulsiveCoulomb.PaperRoute.paper_full_labeled_poincare_via_resolvent, ``RepulsiveCoulomb.PaperRoute.paper_gibbs_defect_moment_product_power, ``RepulsiveCoulomb.PaperRoute.paper_ginibre_center_equality_witnesses, ``RepulsiveCoulomb.PaperRoute.paper_ginibre_symmetric_poincare_sharp_all_N, ``RepulsiveCoulomb.PaperRoute.paper_label_fluctuation, ``RepulsiveCoulomb.PaperRoute.paper_original_capacity_open_neighborhood, ``RepulsiveCoulomb.PaperRoute.paper_original_capacity_physical_cost, ``RepulsiveCoulomb.PaperRoute.paper_original_center_mass, ``RepulsiveCoulomb.PaperRoute.paper_original_center_mass_optimal_rate, ``RepulsiveCoulomb.PaperRoute.paper_original_collision_capacity, ``RepulsiveCoulomb.PaperRoute.paper_original_collision_capacity_and_common_core, ``RepulsiveCoulomb.PaperRoute.paper_original_compact_optimal_double_inf_lower, ``RepulsiveCoulomb.PaperRoute.paper_original_compact_optimal_double_inf_pos, ``RepulsiveCoulomb.PaperRoute.paper_original_compact_optimal_real_double_inf_lower, ``RepulsiveCoulomb.PaperRoute.paper_original_helmert_center, ``RepulsiveCoulomb.PaperRoute.paper_original_helmert_relative, ``RepulsiveCoulomb.PaperRoute.paper_original_helmert_unitary, ``RepulsiveCoulomb.PaperRoute.paper_original_particle_optimal_inf_pos, ``RepulsiveCoulomb.PaperRoute.paper_random_transposition_gap, ``RepulsiveCoulomb.PaperRoute.paper_real_dbar_physical_energy, ``RepulsiveCoulomb.PaperRoute.paper_reference_EL_normalizer_disk, ``RepulsiveCoulomb.PaperRoute.paper_reference_compact_bounds_disk, ``RepulsiveCoulomb.PaperRoute.paper_reference_partition_holder, ``RepulsiveCoulomb.PaperRoute.paper_reference_partition_lower_polynomial, ``RepulsiveCoulomb.PaperRoute.paper_reference_partition_uniform, ``RepulsiveCoulomb.PaperRoute.paper_reference_spatial_bridge, ``RepulsiveCoulomb.PaperRoute.paper_reference_spatial_energy_ae, ``RepulsiveCoulomb.PaperRoute.paper_reference_spatial_partition_eq, ``RepulsiveCoulomb.PaperRoute.paper_relative_core, ``RepulsiveCoulomb.PaperRoute.paper_relative_form_swap, ``RepulsiveCoulomb.PaperRoute.paper_relative_full, ``RepulsiveCoulomb.PaperRoute.paper_resolvent_form_residual, ``RepulsiveCoulomb.PaperRoute.paper_spatial_partition_uniform, ``RepulsiveCoulomb.PaperRoute.paper_symmetric_holomorphic_removal, ``RepulsiveCoulomb.PaperRoute.paper_symmetric_poincare_small_exponent, ``RepulsiveCoulomb.PaperRoute.paper_symmetric_poincare_via_resolvent, ``RepulsiveCoulomb.PaperRoute.paper_thermal_B_gibbs_integrable_positive_log, ``RepulsiveCoulomb.PaperRoute.paper_transposition_core, ``RepulsiveCoulomb.PaperRoute.paper_uniform_defectAt_compact_disk, ``RepulsiveCoulomb.PaperRoute.paper_uniform_defectAt_finite_disk, ``RepulsiveCoulomb.PaperRoute.paper_uniform_labeled_lsi_original, ``RepulsiveCoulomb.PaperRoute.paper_variance_reduction, ``RepulsiveCoulomb.PaperRoute.paper_weighted_named_inequalities, ``RepulsiveCoulomb.PaperRoute.pointLogForce_weak_l2_atomic_maximal, ``RepulsiveCoulomb.PaperRoute.pointLogForce_weak_l2_atomic_maximal_of_total_le, ``RepulsiveCoulomb.PaperRoute.strong_sobolev_on_balls_of_lipschitzOn, ``RepulsiveCoulomb.PaperRoute.strong_sobolev_squared_norm_of_dilation_two, ``RepulsiveCoulomb.PaperRoute.thermalConstructedReference_measure_unique, ``RepulsiveCoulomb.PaperRoute.thermalConstructedReference_multiIndex_tail, ``RepulsiveCoulomb.PaperRoute.thermalConstructedReference_nonempty, ``RepulsiveCoulomb.PaperRoute.thermal_physicalReference_from_minimizer, ``RepulsiveCoulomb.coulombCollisionSet_capacity_zero, ``RepulsiveCoulomb.coulombConstantForm_energy, ``RepulsiveCoulomb.coulombConstantForm_value, ``RepulsiveCoulomb.coulombConstantJet_mem_closedCore, ``RepulsiveCoulomb.coulombCoreGraph_zero_gradient, ``RepulsiveCoulomb.coulombCoreGraph_zero_of_value_zero, ``RepulsiveCoulomb.coulombExhaustion_line_laplacian_pos, ``RepulsiveCoulomb.coulombExhaustion_strict_sublevel_relativelyCompact, ``RepulsiveCoulomb.coulombFormEnergy_eq_integral, ``RepulsiveCoulomb.coulombFormValueL_injective, ``RepulsiveCoulomb.coulombMeasure_isProbability, ``RepulsiveCoulomb.coulombPartition_lt_top, ``RepulsiveCoulomb.coulombPartition_pos, ``RepulsiveCoulomb.coulombPotential_mixedWirtinger_contraction, ``RepulsiveCoulomb.coulombPotential_mixedWirtinger_entry, ``RepulsiveCoulomb.coulombWeight_integrable, ``RepulsiveCoulomb.coulomb_center_mass_manuscript, ``RepulsiveCoulomb.coulomb_center_mass_optimal_lsi_rate_all_N, ``RepulsiveCoulomb.coulomb_collision_capacity_and_common_core, ``RepulsiveCoulomb.equilibriumReferencePartition_canonical_eq, ``RepulsiveCoulomb.equilibriumReference_coulombMeasure_eq_tilted, ``RepulsiveCoulomb.planar_ladyzhenskaya, ``RepulsiveCoulomb.pointConstantForm_energy, ``RepulsiveCoulomb.pointConstantForm_value, ``RepulsiveCoulomb.pointConstantJet_mem_closedCore, ``RepulsiveCoulomb.pointGroundState_energy_identity, ``RepulsiveCoulomb.pointMeasure_disk_tail_le, ``RepulsiveCoulomb.pointMeasure_disk_tail_real_le, ``RepulsiveCoulomb.pointPartition_integral_unitDisk_lower, ``RepulsiveCoulomb.pointPartition_unitDisk_lower_uniform, ``IntegratedOriginalReferenceInstances.original_canonical_splitting, ``IntegratedOriginalReferenceInstances.original_canonical_partition, ``IntegratedOriginalReferenceInstances.original_spatial_collisionfree, ``IntegratedOriginalReferenceInstances.original_spatial_partition, ``IntegratedOriginalReferenceInstances.original_partition_uniform, ``IntegratedOriginalReferenceInstances.original_entropy_factorization, ``IntegratedOriginalReferenceInstances.original_compact_all_ell_defect, ``IntegratedOriginalReferenceInstances.original_fixed_all_ell_defect]
  let (_, full) := (roots.forM (visit env false)).run ({} : NameSet)
  let (_, authored) := (roots.forM (visit env true)).run ({} : NameSet)
  for n in full do
    if n == `sorryAx then throwError "Incomplete integrated proof: {n}"
    if let some (.axiomInfo _) := env.find? n then
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Nonstandard axiom in integrated closure: {n}"
    if n.toString.startsWith "RepulsiveCoulomb.coulomb_named_" ||
        n.toString.startsWith "RepulsiveCoulomb.pointDilationBranch_named_" then
      throwError "Old named final endpoint in integrated closure: {n}"
  for n in #[`RepulsiveCoulomb.equilibriumConstructedReference,
      `RepulsiveCoulomb.equilibriumConstructedReference_nonempty,
      `RepulsiveCoulomb.equilibriumCanonical_exists_global_minimizer,
      `RepulsiveCoulomb.equilibriumObjective_exists_global_minimizer,
      `RepulsiveCoulomb.equilibriumCanonicalMinimizers_unique,
      `RepulsiveCoulomb.equilibrium_pointwise_EL_densities_unique,
      `RepulsiveCoulomb.equilibrium_pointwise_EL_radial,
      `RepulsiveCoulomb.equilibrium_pointwise_EL_contDiff,
      `RepulsiveCoulomb.equilibrium_pointwise_EL_contDiff_one,
      `RepulsiveCoulomb.equilibrium_pointwise_EL_sharp_cap,
      `RepulsiveCoulomb.equilibrium_EL_circle_log_increment,
      `RepulsiveCoulomb.equilibriumReference_gibbs_defect_moment,
      `RepulsiveCoulomb.equilibriumReference_physical_gibbs_defect_moment,
      `RepulsiveCoulomb.equilibriumReferencePartition_uniform,
      `RepulsiveCoulomb.equilibriumConstructedReference_partition_uniform,
      `RepulsiveCoulomb.pointDilationBranchCwt,
      `RepulsiveCoulomb.pointDilationBranchRhoWt,
      `RepulsiveCoulomb.pointDilationBranchCrel,
      `RepulsiveCoulomb.pointDilationBranchP1,
      `RepulsiveCoulomb.pointDilationBranchK1,
      `RepulsiveCoulomb.pointSobolevKappa,
      `RepulsiveCoulomb.rawPointMeasure_strong_sobolev_squared_norm,
      `RepulsiveCoulomb.rawPoint_uniform_local_sobolev_poincare,
      `RepulsiveCoulomb.pointGaussian_uniform_local_geometry] do
    if full.contains n then throwError "Forbidden selected old producer in integrated closure: {n}"
  for n in #[`RepulsiveCoulomb.equilibriumLogKernel_zeroMass_nonneg,
      `RepulsiveCoulomb.equilibriumReference_modulated_exp_integrable,
      `RepulsiveCoulomb.equilibriumReferencePartition_lower,
      `RepulsiveCoulomb.equilibriumReferencePartition_pos,
      `RepulsiveCoulomb.conditionalEntropyBranch_B_gibbs_integrable,
      `RepulsiveCoulomb.conditionalEntropyBranch_B_core_integrable,
      `RepulsiveCoulomb.equilibriumReference_exp_elConstant_le,
      `RepulsiveCoulomb.equilibriumReference_tail_prefactor_bound,
      `RepulsiveCoulomb.equilibriumReference_uniform_envelope,
      `RepulsiveCoulomb.equilibriumReference_potential_exponential_bound,
      `RepulsiveCoulomb.equilibriumReference_polynomial_moment_bound,
      `RepulsiveCoulomb.equilibriumProduct_exp_average,
      `RepulsiveCoulomb.PaperRoute.paper_reference_gibbs_energy_exp_integrable_polynomial,
      `RepulsiveCoulomb.PaperRoute.paper_reference_gibbs_energy_integrable_polynomial] do
    if authored.contains n then throwError "Forbidden old or superseded producer outside exact DG proof body: {n}"
  unless full.contains `RepulsiveCoulomb.equilibriumLogKernel_zeroMass_nonneg do
    throwError "Expected disclosed DG-internal old Green dependency disappeared; re-audit boundary"
  unless full.contains `RepulsiveCoulomb.equilibriumReference_exp_elConstant_le do
    throwError "Expected disclosed DG-internal auxiliary envelope disappeared; re-audit boundary"
  for root in #[``thermalConstructedReference, ``thermalConstructedReference_multiIndex_tail] do
    let (_, thermal) := (visit env false root).run ({} : NameSet)
    for n in #[`RepulsiveCoulomb.equilibriumLogKernel_zeroMass_nonneg,
        `RepulsiveCoulomb.equilibriumConstructedReference,
        `RepulsiveCoulomb.equilibriumReference_derivative_tail_step,
        `RepulsiveCoulomb.equilibriumReference_allDerivative_tails,
        `RepulsiveCoulomb.equilibriumReference_iteratedFDeriv_tail,
        `RepulsiveCoulomb.equilibriumReference_multiIndex_tail] do
      if thermal.contains n then throwError "Old Green/reference/tail leaked into independent thermal branch: {n}"
    unless thermal.contains ``log_green_zero_mass do
      throwError "New Green not load-bearing in same actual thermal reference"
  for root in #[``IntegratedOriginalReferenceInstances.original_canonical_splitting,
      ``IntegratedOriginalReferenceInstances.original_canonical_partition,
      ``IntegratedOriginalReferenceInstances.original_spatial_collisionfree,
      ``IntegratedOriginalReferenceInstances.original_spatial_partition,
      ``IntegratedOriginalReferenceInstances.original_partition_uniform,
      ``IntegratedOriginalReferenceInstances.original_entropy_factorization,
      ``IntegratedOriginalReferenceInstances.original_compact_all_ell_defect,
      ``IntegratedOriginalReferenceInstances.original_fixed_all_ell_defect] do
    let (_, used) := (visit env true root).run ({} : NameSet)
    for n in #[``thermalConstructedReference, ``thermal_physicalReference_from_minimizer,
        ``thermalCanonical_exists_global_minimizer, ``log_green_zero_mass] do
      unless used.contains n do throwError "Original-reference application silently lost actual new constructor: {root}, {n}"
  for root in #[``IntegratedOriginalReferenceInstances.original_entropy_factorization,
      ``IntegratedOriginalReferenceInstances.original_compact_all_ell_defect,
      ``IntegratedOriginalReferenceInstances.original_fixed_all_ell_defect] do
    let (_, used) := (visit env true root).run ({} : NameSet)
    for n in #[``paper_gibbs_defect_moment_product_power,
        ``paper_gibbs_defect_moment_via_concavity,
        ``paper_product_exp_average_power,
        ``paper_exp_integral_inverse_power_concavity,
        ``Real.concaveOn_rpow, ``ConcaveOn.le_map_integral] do
      unless used.contains n do throwError "Exact entropy step absent in original-reference application: {root}, {n}"
  for root in #[``IntegratedOriginalReferenceInstances.original_compact_all_ell_defect,
      ``IntegratedOriginalReferenceInstances.original_fixed_all_ell_defect] do
    let (_, used) := (visit env true root).run ({} : NameSet)
    for n in #[``paper_thermal_B_gibbs_integrable_positive_log,
        ``paper_coulomb_positive_log_density_gaussian_bound,
        ``paper_rpow_positive_log_bound,
        ``RepulsiveCoulomb.coulombDensity_le_gaussian_collision_power] do
      unless used.contains n do throwError "Positive-log proof absent in original defect finiteness: {root}, {n}"
  let (_, curvature) := (visit env false ``PointCurvature.pointConformalDensity_distributional_curvature).run ({} : NameSet)
  for n in #[``PointCurvature.negative_log_pointConformalDensity_pairing,
      ``PointCurvature.translated_negative_log_pairing, ``log_fundamental_solution] do
    unless curvature.contains n do throwError "Literal finite-point curvature lost test-function producer: {n}"
  logInfo m!"PASS: INTEGRATED 33 named-claim mapping, {roots.size} global roots; full types/opaque proofs; exact DG body-only cut with old Green/envelope disclosed; actual original-reference partition and all-ell entropy applications."
  logInfo "BOUNDARY: the thermal regularity theorem is the actual radial-potential specialization; locally-Lipschitz local Sobolev is proved, arbitrary weighted W1,2 is not asserted; capacity/COM/curvature/tails/Ginibre are separate physical roots. No independent-kernel or Nanoda claim."
  for n in full do
    if n.toString.startsWith "RepulsiveCoulomb." then logInfo m!"INTEGRATED_FULL_DEP {n}"
  for n in authored do
    if n.toString.startsWith "RepulsiveCoulomb." then logInfo m!"INTEGRATED_AUTHORED_DEP {n}"
end IntegratedGlobalAudit

end
