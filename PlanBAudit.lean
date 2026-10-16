module

public import RetainedReload

@[expose] public section

-- Generated source adapter; fresh compilation and checking are still required.

namespace PlanBVerifierAudit
open Lean Elab Command
-- This is the comparator's fixed-definition closure only. Full solution
-- proof/kernel/audit closure remains uncut in unchanged imported consumers.
partial def visitFixed (env : Environment) (holes : Array Name) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for d in ci.type.getUsedConstants do visitFixed env holes d
    if holes.contains n then return
    if let some value := ci.value? (allowOpaque := true) then
      for d in value.getUsedConstants do visitFixed env holes d
run_cmd do
  let env ← getEnv
  let holes := #[``IntegratedOriginalReferenceInstances.original_canonical_partition, ``IntegratedOriginalReferenceInstances.original_canonical_splitting, ``IntegratedOriginalReferenceInstances.original_compact_all_ell_defect, ``IntegratedOriginalReferenceInstances.original_entropy_factorization, ``IntegratedOriginalReferenceInstances.original_fixed_all_ell_defect, ``IntegratedOriginalReferenceInstances.original_partition_uniform, ``IntegratedOriginalReferenceInstances.original_spatial_collisionfree, ``IntegratedOriginalReferenceInstances.original_spatial_partition, ``RepulsiveCoulomb.PaperRoute.PointCurvature.pointConformalDensity_distributional_curvature, ``RepulsiveCoulomb.PaperRoute.atomic_pointCore_weighted_moment_bound, ``RepulsiveCoulomb.PaperRoute.atomic_pointForm_uniform_quadratic_moment, ``RepulsiveCoulomb.PaperRoute.atomic_pointForm_weighted_moment_bound, ``RepulsiveCoulomb.PaperRoute.atomic_pointScore_uncertainty, ``RepulsiveCoulomb.PaperRoute.core_defective_lsi_of_gaussian_spi, ``RepulsiveCoulomb.PaperRoute.core_global_superPoincare, ``RepulsiveCoulomb.PaperRoute.core_global_superPoincare_small, ``RepulsiveCoulomb.PaperRoute.core_poincare_of_raw_sobolev, ``RepulsiveCoulomb.PaperRoute.disk_half_mass_ball, ``RepulsiveCoulomb.PaperRoute.form_global_superPoincare, ``RepulsiveCoulomb.PaperRoute.form_poincare_of_raw_sobolev, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_centered_moment_tendsto, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_energy_tendsto, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_fderiv_ae_tendsto, ``RepulsiveCoulomb.PaperRoute.lipschitzMollify_hasFDerivAt, ``RepulsiveCoulomb.PaperRoute.original_gaussian_local_geometry, ``RepulsiveCoulomb.PaperRoute.original_gaussian_local_sobolev_locallyLipschitz, ``RepulsiveCoulomb.PaperRoute.original_gaussian_strong_sobolev_closedBall, ``RepulsiveCoulomb.PaperRoute.original_point_doubling_and_locallyLipschitz_PI, ``RepulsiveCoulomb.PaperRoute.original_point_localGeometry, ``RepulsiveCoulomb.PaperRoute.original_point_physical_weak_one_two, ``RepulsiveCoulomb.PaperRoute.original_raw_local_sobolev_locallyLipschitz, ``RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_c1_center, ``RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_closedBall, ``RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_locallyLipschitz, ``RepulsiveCoulomb.PaperRoute.original_weighted_full_domain, ``RepulsiveCoulomb.PaperRoute.paperCwt_scaling, ``RepulsiveCoulomb.PaperRoute.paperOriginalCompactLabeledRate_le_optimal, ``RepulsiveCoulomb.PaperRoute.paperOriginalCompactLabeledRate_pos, ``RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate_le_optimal, ``RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate_pos, ``RepulsiveCoulomb.PaperRoute.paperRhoWt_scaling, ``RepulsiveCoulomb.PaperRoute.paperTranspositionKernel_identity, ``RepulsiveCoulomb.PaperRoute.paperTranspositionKernel_row_sum, ``RepulsiveCoulomb.PaperRoute.paperTranspositionKernel_swap, ``RepulsiveCoulomb.PaperRoute.paperUniformTransposition_gap_exact, ``RepulsiveCoulomb.PaperRoute.paper_center_imaginary_form_witness, ``RepulsiveCoulomb.PaperRoute.paper_center_real_form_witness, ``RepulsiveCoulomb.PaperRoute.paper_common_phase_identity, ``RepulsiveCoulomb.PaperRoute.paper_complete_graph_relative_gradient, ``RepulsiveCoulomb.PaperRoute.paper_coulomb_potential_distribution, ``RepulsiveCoulomb.PaperRoute.paper_dbar_core_distance, ``RepulsiveCoulomb.PaperRoute.paper_dbar_graph_distance, ``RepulsiveCoulomb.PaperRoute.paper_dbar_kernel_holomorphic, ``RepulsiveCoulomb.PaperRoute.paper_dg_fixed_coupling, ``RepulsiveCoulomb.PaperRoute.paper_entropy_factorization_disk, ``RepulsiveCoulomb.PaperRoute.paper_exp_integral_inverse_power_concavity, ``RepulsiveCoulomb.PaperRoute.paper_finite_defect_nonneg_disk, ``RepulsiveCoulomb.PaperRoute.paper_fixed_particle_compact_temperature, ``RepulsiveCoulomb.PaperRoute.paper_fixed_particle_form_compact, ``RepulsiveCoulomb.PaperRoute.paper_fixed_particle_kernel_constants, ``RepulsiveCoulomb.PaperRoute.paper_fixed_particle_operator_selfAdjoint, ``RepulsiveCoulomb.PaperRoute.paper_fixed_particle_poincare_via_resolvent, ``RepulsiveCoulomb.PaperRoute.paper_fixed_particle_resolvent_compact, ``RepulsiveCoulomb.PaperRoute.paper_full_defective_compact_via_disk_reference_family, ``RepulsiveCoulomb.PaperRoute.paper_full_defective_of_reference_bounds_of_exp_integrable, ``RepulsiveCoulomb.PaperRoute.paper_full_labeled_lsi_original, ``RepulsiveCoulomb.PaperRoute.paper_full_labeled_poincare_uniform_via_resolvent, ``RepulsiveCoulomb.PaperRoute.paper_full_labeled_poincare_via_resolvent, ``RepulsiveCoulomb.PaperRoute.paper_gibbs_defect_moment_product_power, ``RepulsiveCoulomb.PaperRoute.paper_ginibre_center_equality_witnesses, ``RepulsiveCoulomb.PaperRoute.paper_ginibre_symmetric_poincare_sharp_all_N, ``RepulsiveCoulomb.PaperRoute.paper_label_fluctuation, ``RepulsiveCoulomb.PaperRoute.paper_original_capacity_open_neighborhood, ``RepulsiveCoulomb.PaperRoute.paper_original_capacity_physical_cost, ``RepulsiveCoulomb.PaperRoute.paper_original_center_mass, ``RepulsiveCoulomb.PaperRoute.paper_original_center_mass_optimal_rate, ``RepulsiveCoulomb.PaperRoute.paper_original_collision_capacity, ``RepulsiveCoulomb.PaperRoute.paper_original_collision_capacity_and_common_core, ``RepulsiveCoulomb.PaperRoute.paper_original_compact_optimal_double_inf_lower, ``RepulsiveCoulomb.PaperRoute.paper_original_compact_optimal_double_inf_pos, ``RepulsiveCoulomb.PaperRoute.paper_original_compact_optimal_real_double_inf_lower, ``RepulsiveCoulomb.PaperRoute.paper_original_helmert_center, ``RepulsiveCoulomb.PaperRoute.paper_original_helmert_relative, ``RepulsiveCoulomb.PaperRoute.paper_original_helmert_unitary, ``RepulsiveCoulomb.PaperRoute.paper_original_particle_optimal_inf_pos, ``RepulsiveCoulomb.PaperRoute.paper_random_transposition_gap, ``RepulsiveCoulomb.PaperRoute.paper_real_dbar_physical_energy, ``RepulsiveCoulomb.PaperRoute.paper_reference_EL_normalizer_disk, ``RepulsiveCoulomb.PaperRoute.paper_reference_compact_bounds_disk, ``RepulsiveCoulomb.PaperRoute.paper_reference_partition_holder, ``RepulsiveCoulomb.PaperRoute.paper_reference_partition_lower_polynomial, ``RepulsiveCoulomb.PaperRoute.paper_reference_partition_uniform, ``RepulsiveCoulomb.PaperRoute.paper_reference_spatial_bridge, ``RepulsiveCoulomb.PaperRoute.paper_reference_spatial_energy_ae, ``RepulsiveCoulomb.PaperRoute.paper_reference_spatial_partition_eq, ``RepulsiveCoulomb.PaperRoute.paper_relative_core, ``RepulsiveCoulomb.PaperRoute.paper_relative_form_swap, ``RepulsiveCoulomb.PaperRoute.paper_relative_full, ``RepulsiveCoulomb.PaperRoute.paper_resolvent_form_residual, ``RepulsiveCoulomb.PaperRoute.paper_spatial_partition_uniform, ``RepulsiveCoulomb.PaperRoute.paper_symmetric_holomorphic_removal, ``RepulsiveCoulomb.PaperRoute.paper_symmetric_poincare_small_exponent, ``RepulsiveCoulomb.PaperRoute.paper_symmetric_poincare_via_resolvent, ``RepulsiveCoulomb.PaperRoute.paper_thermal_B_gibbs_integrable_positive_log, ``RepulsiveCoulomb.PaperRoute.paper_transposition_core, ``RepulsiveCoulomb.PaperRoute.paper_uniform_defectAt_compact_disk, ``RepulsiveCoulomb.PaperRoute.paper_uniform_defectAt_finite_disk, ``RepulsiveCoulomb.PaperRoute.paper_uniform_labeled_lsi_original, ``RepulsiveCoulomb.PaperRoute.paper_variance_reduction, ``RepulsiveCoulomb.PaperRoute.paper_weighted_named_inequalities, ``RepulsiveCoulomb.PaperRoute.pointLogForce_weak_l2_atomic_maximal, ``RepulsiveCoulomb.PaperRoute.pointLogForce_weak_l2_atomic_maximal_of_total_le, ``RepulsiveCoulomb.PaperRoute.strong_sobolev_on_balls_of_lipschitzOn, ``RepulsiveCoulomb.PaperRoute.strong_sobolev_squared_norm_of_dilation_two, ``RepulsiveCoulomb.PaperRoute.thermalConstructedReference_measure_unique, ``RepulsiveCoulomb.PaperRoute.thermalConstructedReference_multiIndex_tail, ``RepulsiveCoulomb.PaperRoute.thermalConstructedReference_nonempty, ``RepulsiveCoulomb.PaperRoute.thermal_physicalReference_from_minimizer, ``RepulsiveCoulomb.coulombCollisionSet_capacity_zero, ``RepulsiveCoulomb.coulombConstantForm_energy, ``RepulsiveCoulomb.coulombConstantForm_value, ``RepulsiveCoulomb.coulombConstantJet_mem_closedCore, ``RepulsiveCoulomb.coulombCoreGraph_zero_gradient, ``RepulsiveCoulomb.coulombCoreGraph_zero_of_value_zero, ``RepulsiveCoulomb.coulombExhaustion_line_laplacian_pos, ``RepulsiveCoulomb.coulombExhaustion_strict_sublevel_relativelyCompact, ``RepulsiveCoulomb.coulombFormEnergy_eq_integral, ``RepulsiveCoulomb.coulombFormValueL_injective, ``RepulsiveCoulomb.coulombMeasure_isProbability, ``RepulsiveCoulomb.coulombPartition_lt_top, ``RepulsiveCoulomb.coulombPartition_pos, ``RepulsiveCoulomb.coulombPotential_mixedWirtinger_contraction, ``RepulsiveCoulomb.coulombPotential_mixedWirtinger_entry, ``RepulsiveCoulomb.coulombWeight_integrable, ``RepulsiveCoulomb.coulomb_center_mass_manuscript, ``RepulsiveCoulomb.coulomb_center_mass_optimal_lsi_rate_all_N, ``RepulsiveCoulomb.coulomb_collision_capacity_and_common_core, ``RepulsiveCoulomb.equilibriumReferencePartition_canonical_eq, ``RepulsiveCoulomb.equilibriumReference_coulombMeasure_eq_tilted, ``RepulsiveCoulomb.planar_ladyzhenskaya, ``RepulsiveCoulomb.pointConstantForm_energy, ``RepulsiveCoulomb.pointConstantForm_value, ``RepulsiveCoulomb.pointConstantJet_mem_closedCore, ``RepulsiveCoulomb.pointGroundState_energy_identity, ``RepulsiveCoulomb.pointMeasure_disk_tail_le, ``RepulsiveCoulomb.pointMeasure_disk_tail_real_le, ``RepulsiveCoulomb.pointPartition_integral_unitDisk_lower, ``RepulsiveCoulomb.pointPartition_unitDisk_lower_uniform]
  let definitions := #[``RepulsiveCoulomb.PaperRoute.paperCompactLabeledRateFromReferenceFamily, ``RepulsiveCoulomb.PaperRoute.paperLabeledRateFromReference, ``RepulsiveCoulomb.PaperRoute.paperOriginalCompactLabeledRate, ``RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate]
  for name in holes do
    match env.find? name with
    | some (.thmInfo _) => logInfo m!"PLAN_B_TARGET_KIND {name} theorem"
    | _ => throwError "PLAN_B_TARGET_KIND_MISMATCH {name} expected theorem"
  for name in definitions do
    match env.find? name with
    | some (.defnInfo _) => logInfo m!"PLAN_B_TARGET_KIND {name} def"
    | _ => throwError "PLAN_B_TARGET_KIND_MISMATCH {name} expected def"
  let witnesses : Array (Name × Name) := #[(``RepulsiveCoulomb.PaperRoute.paperCompactLabeledRateFromReferenceFamily, ``RepulsiveCoulomb.PaperRoute.paperOriginalCompactLabeledRate_pos), (``RepulsiveCoulomb.PaperRoute.paperLabeledRateFromReference, ``RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate_pos), (``RepulsiveCoulomb.PaperRoute.paperOriginalCompactLabeledRate, ``RepulsiveCoulomb.PaperRoute.paperOriginalCompactLabeledRate_pos), (``RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate, ``RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate_pos)]
  for pair in witnesses do
    let definition := pair.1
    let witness := pair.2
    let some ci := env.find? witness | throwError "PLAN_B_MISSING_WITNESS {witness}"
    let (_, seen) := (ci.type.getUsedConstants.forM (visitFixed env holes)).run ({} : NameSet)
    unless seen.contains definition do
      throwError "PLAN_B_FIXED_DEFINITION_MISSING {definition} {witness}"
    for name in seen do
      let some info := env.find? name | throwError "PLAN_B_FIXED_CLOSURE_MISSING_CONSTANT {name}"
      if name == `sorryAx then throwError "PLAN_B_FIXED_CLOSURE_SORRY {name}"
      if let .axiomInfo _ := info then
        unless #[`propext, `Classical.choice, `Quot.sound].contains name do
          throwError "PLAN_B_FIXED_CLOSURE_NONSTANDARD_AXIOM {name}"
    logInfo m!"PLAN_B_FIXED_DEFINITION_COVERED {definition} {witness}"
end PlanBVerifierAudit

#print axioms IntegratedOriginalReferenceInstances.original_canonical_partition
#print axioms IntegratedOriginalReferenceInstances.original_canonical_splitting
#print axioms IntegratedOriginalReferenceInstances.original_compact_all_ell_defect
#print axioms IntegratedOriginalReferenceInstances.original_entropy_factorization
#print axioms IntegratedOriginalReferenceInstances.original_fixed_all_ell_defect
#print axioms IntegratedOriginalReferenceInstances.original_partition_uniform
#print axioms IntegratedOriginalReferenceInstances.original_spatial_collisionfree
#print axioms IntegratedOriginalReferenceInstances.original_spatial_partition
#print axioms RepulsiveCoulomb.PaperRoute.PointCurvature.pointConformalDensity_distributional_curvature
#print axioms RepulsiveCoulomb.PaperRoute.atomic_pointCore_weighted_moment_bound
#print axioms RepulsiveCoulomb.PaperRoute.atomic_pointForm_uniform_quadratic_moment
#print axioms RepulsiveCoulomb.PaperRoute.atomic_pointForm_weighted_moment_bound
#print axioms RepulsiveCoulomb.PaperRoute.atomic_pointScore_uncertainty
#print axioms RepulsiveCoulomb.PaperRoute.core_defective_lsi_of_gaussian_spi
#print axioms RepulsiveCoulomb.PaperRoute.core_global_superPoincare
#print axioms RepulsiveCoulomb.PaperRoute.core_global_superPoincare_small
#print axioms RepulsiveCoulomb.PaperRoute.core_poincare_of_raw_sobolev
#print axioms RepulsiveCoulomb.PaperRoute.disk_half_mass_ball
#print axioms RepulsiveCoulomb.PaperRoute.form_global_superPoincare
#print axioms RepulsiveCoulomb.PaperRoute.form_poincare_of_raw_sobolev
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzMollify_centered_moment_tendsto
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzMollify_energy_tendsto
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzMollify_fderiv_ae_tendsto
#print axioms RepulsiveCoulomb.PaperRoute.lipschitzMollify_hasFDerivAt
#print axioms RepulsiveCoulomb.PaperRoute.original_gaussian_local_geometry
#print axioms RepulsiveCoulomb.PaperRoute.original_gaussian_local_sobolev_locallyLipschitz
#print axioms RepulsiveCoulomb.PaperRoute.original_gaussian_strong_sobolev_closedBall
#print axioms RepulsiveCoulomb.PaperRoute.original_point_doubling_and_locallyLipschitz_PI
#print axioms RepulsiveCoulomb.PaperRoute.original_point_localGeometry
#print axioms RepulsiveCoulomb.PaperRoute.original_point_physical_weak_one_two
#print axioms RepulsiveCoulomb.PaperRoute.original_raw_local_sobolev_locallyLipschitz
#print axioms RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_c1_center
#print axioms RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_closedBall
#print axioms RepulsiveCoulomb.PaperRoute.original_raw_strong_sobolev_locallyLipschitz
#print axioms RepulsiveCoulomb.PaperRoute.original_weighted_full_domain
#print axioms RepulsiveCoulomb.PaperRoute.paperCompactLabeledRateFromReferenceFamily
#print axioms RepulsiveCoulomb.PaperRoute.paperCwt_scaling
#print axioms RepulsiveCoulomb.PaperRoute.paperLabeledRateFromReference
#print axioms RepulsiveCoulomb.PaperRoute.paperOriginalCompactLabeledRate
#print axioms RepulsiveCoulomb.PaperRoute.paperOriginalCompactLabeledRate_le_optimal
#print axioms RepulsiveCoulomb.PaperRoute.paperOriginalCompactLabeledRate_pos
#print axioms RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate
#print axioms RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate_le_optimal
#print axioms RepulsiveCoulomb.PaperRoute.paperOriginalLabeledRate_pos
#print axioms RepulsiveCoulomb.PaperRoute.paperRhoWt_scaling
#print axioms RepulsiveCoulomb.PaperRoute.paperTranspositionKernel_identity
#print axioms RepulsiveCoulomb.PaperRoute.paperTranspositionKernel_row_sum
#print axioms RepulsiveCoulomb.PaperRoute.paperTranspositionKernel_swap
#print axioms RepulsiveCoulomb.PaperRoute.paperUniformTransposition_gap_exact
#print axioms RepulsiveCoulomb.PaperRoute.paper_center_imaginary_form_witness
#print axioms RepulsiveCoulomb.PaperRoute.paper_center_real_form_witness
#print axioms RepulsiveCoulomb.PaperRoute.paper_common_phase_identity
#print axioms RepulsiveCoulomb.PaperRoute.paper_complete_graph_relative_gradient
#print axioms RepulsiveCoulomb.PaperRoute.paper_coulomb_potential_distribution
#print axioms RepulsiveCoulomb.PaperRoute.paper_dbar_core_distance
#print axioms RepulsiveCoulomb.PaperRoute.paper_dbar_graph_distance
#print axioms RepulsiveCoulomb.PaperRoute.paper_dbar_kernel_holomorphic
#print axioms RepulsiveCoulomb.PaperRoute.paper_dg_fixed_coupling
#print axioms RepulsiveCoulomb.PaperRoute.paper_entropy_factorization_disk
#print axioms RepulsiveCoulomb.PaperRoute.paper_exp_integral_inverse_power_concavity
#print axioms RepulsiveCoulomb.PaperRoute.paper_finite_defect_nonneg_disk
#print axioms RepulsiveCoulomb.PaperRoute.paper_fixed_particle_compact_temperature
#print axioms RepulsiveCoulomb.PaperRoute.paper_fixed_particle_form_compact
#print axioms RepulsiveCoulomb.PaperRoute.paper_fixed_particle_kernel_constants
#print axioms RepulsiveCoulomb.PaperRoute.paper_fixed_particle_operator_selfAdjoint
#print axioms RepulsiveCoulomb.PaperRoute.paper_fixed_particle_poincare_via_resolvent
#print axioms RepulsiveCoulomb.PaperRoute.paper_fixed_particle_resolvent_compact
#print axioms RepulsiveCoulomb.PaperRoute.paper_full_defective_compact_via_disk_reference_family
#print axioms RepulsiveCoulomb.PaperRoute.paper_full_defective_of_reference_bounds_of_exp_integrable
#print axioms RepulsiveCoulomb.PaperRoute.paper_full_labeled_lsi_original
#print axioms RepulsiveCoulomb.PaperRoute.paper_full_labeled_poincare_uniform_via_resolvent
#print axioms RepulsiveCoulomb.PaperRoute.paper_full_labeled_poincare_via_resolvent
#print axioms RepulsiveCoulomb.PaperRoute.paper_gibbs_defect_moment_product_power
#print axioms RepulsiveCoulomb.PaperRoute.paper_ginibre_center_equality_witnesses
#print axioms RepulsiveCoulomb.PaperRoute.paper_ginibre_symmetric_poincare_sharp_all_N
#print axioms RepulsiveCoulomb.PaperRoute.paper_label_fluctuation
#print axioms RepulsiveCoulomb.PaperRoute.paper_original_capacity_open_neighborhood
#print axioms RepulsiveCoulomb.PaperRoute.paper_original_capacity_physical_cost
#print axioms RepulsiveCoulomb.PaperRoute.paper_original_center_mass
#print axioms RepulsiveCoulomb.PaperRoute.paper_original_center_mass_optimal_rate
#print axioms RepulsiveCoulomb.PaperRoute.paper_original_collision_capacity
#print axioms RepulsiveCoulomb.PaperRoute.paper_original_collision_capacity_and_common_core
#print axioms RepulsiveCoulomb.PaperRoute.paper_original_compact_optimal_double_inf_lower
#print axioms RepulsiveCoulomb.PaperRoute.paper_original_compact_optimal_double_inf_pos
#print axioms RepulsiveCoulomb.PaperRoute.paper_original_compact_optimal_real_double_inf_lower
#print axioms RepulsiveCoulomb.PaperRoute.paper_original_helmert_center
#print axioms RepulsiveCoulomb.PaperRoute.paper_original_helmert_relative
#print axioms RepulsiveCoulomb.PaperRoute.paper_original_helmert_unitary
#print axioms RepulsiveCoulomb.PaperRoute.paper_original_particle_optimal_inf_pos
#print axioms RepulsiveCoulomb.PaperRoute.paper_random_transposition_gap
#print axioms RepulsiveCoulomb.PaperRoute.paper_real_dbar_physical_energy
#print axioms RepulsiveCoulomb.PaperRoute.paper_reference_EL_normalizer_disk
#print axioms RepulsiveCoulomb.PaperRoute.paper_reference_compact_bounds_disk
#print axioms RepulsiveCoulomb.PaperRoute.paper_reference_partition_holder
#print axioms RepulsiveCoulomb.PaperRoute.paper_reference_partition_lower_polynomial
#print axioms RepulsiveCoulomb.PaperRoute.paper_reference_partition_uniform
#print axioms RepulsiveCoulomb.PaperRoute.paper_reference_spatial_bridge
#print axioms RepulsiveCoulomb.PaperRoute.paper_reference_spatial_energy_ae
#print axioms RepulsiveCoulomb.PaperRoute.paper_reference_spatial_partition_eq
#print axioms RepulsiveCoulomb.PaperRoute.paper_relative_core
#print axioms RepulsiveCoulomb.PaperRoute.paper_relative_form_swap
#print axioms RepulsiveCoulomb.PaperRoute.paper_relative_full
#print axioms RepulsiveCoulomb.PaperRoute.paper_resolvent_form_residual
#print axioms RepulsiveCoulomb.PaperRoute.paper_spatial_partition_uniform
#print axioms RepulsiveCoulomb.PaperRoute.paper_symmetric_holomorphic_removal
#print axioms RepulsiveCoulomb.PaperRoute.paper_symmetric_poincare_small_exponent
#print axioms RepulsiveCoulomb.PaperRoute.paper_symmetric_poincare_via_resolvent
#print axioms RepulsiveCoulomb.PaperRoute.paper_thermal_B_gibbs_integrable_positive_log
#print axioms RepulsiveCoulomb.PaperRoute.paper_transposition_core
#print axioms RepulsiveCoulomb.PaperRoute.paper_uniform_defectAt_compact_disk
#print axioms RepulsiveCoulomb.PaperRoute.paper_uniform_defectAt_finite_disk
#print axioms RepulsiveCoulomb.PaperRoute.paper_uniform_labeled_lsi_original
#print axioms RepulsiveCoulomb.PaperRoute.paper_variance_reduction
#print axioms RepulsiveCoulomb.PaperRoute.paper_weighted_named_inequalities
#print axioms RepulsiveCoulomb.PaperRoute.pointLogForce_weak_l2_atomic_maximal
#print axioms RepulsiveCoulomb.PaperRoute.pointLogForce_weak_l2_atomic_maximal_of_total_le
#print axioms RepulsiveCoulomb.PaperRoute.strong_sobolev_on_balls_of_lipschitzOn
#print axioms RepulsiveCoulomb.PaperRoute.strong_sobolev_squared_norm_of_dilation_two
#print axioms RepulsiveCoulomb.PaperRoute.thermalConstructedReference_measure_unique
#print axioms RepulsiveCoulomb.PaperRoute.thermalConstructedReference_multiIndex_tail
#print axioms RepulsiveCoulomb.PaperRoute.thermalConstructedReference_nonempty
#print axioms RepulsiveCoulomb.PaperRoute.thermal_physicalReference_from_minimizer
#print axioms RepulsiveCoulomb.coulombCollisionSet_capacity_zero
#print axioms RepulsiveCoulomb.coulombConstantForm_energy
#print axioms RepulsiveCoulomb.coulombConstantForm_value
#print axioms RepulsiveCoulomb.coulombConstantJet_mem_closedCore
#print axioms RepulsiveCoulomb.coulombCoreGraph_zero_gradient
#print axioms RepulsiveCoulomb.coulombCoreGraph_zero_of_value_zero
#print axioms RepulsiveCoulomb.coulombExhaustion_line_laplacian_pos
#print axioms RepulsiveCoulomb.coulombExhaustion_strict_sublevel_relativelyCompact
#print axioms RepulsiveCoulomb.coulombFormEnergy_eq_integral
#print axioms RepulsiveCoulomb.coulombFormValueL_injective
#print axioms RepulsiveCoulomb.coulombMeasure_isProbability
#print axioms RepulsiveCoulomb.coulombPartition_lt_top
#print axioms RepulsiveCoulomb.coulombPartition_pos
#print axioms RepulsiveCoulomb.coulombPotential_mixedWirtinger_contraction
#print axioms RepulsiveCoulomb.coulombPotential_mixedWirtinger_entry
#print axioms RepulsiveCoulomb.coulombWeight_integrable
#print axioms RepulsiveCoulomb.coulomb_center_mass_manuscript
#print axioms RepulsiveCoulomb.coulomb_center_mass_optimal_lsi_rate_all_N
#print axioms RepulsiveCoulomb.coulomb_collision_capacity_and_common_core
#print axioms RepulsiveCoulomb.equilibriumReferencePartition_canonical_eq
#print axioms RepulsiveCoulomb.equilibriumReference_coulombMeasure_eq_tilted
#print axioms RepulsiveCoulomb.planar_ladyzhenskaya
#print axioms RepulsiveCoulomb.pointConstantForm_energy
#print axioms RepulsiveCoulomb.pointConstantForm_value
#print axioms RepulsiveCoulomb.pointConstantJet_mem_closedCore
#print axioms RepulsiveCoulomb.pointGroundState_energy_identity
#print axioms RepulsiveCoulomb.pointMeasure_disk_tail_le
#print axioms RepulsiveCoulomb.pointMeasure_disk_tail_real_le
#print axioms RepulsiveCoulomb.pointPartition_integral_unitDisk_lower
#print axioms RepulsiveCoulomb.pointPartition_unitDisk_lower_uniform
