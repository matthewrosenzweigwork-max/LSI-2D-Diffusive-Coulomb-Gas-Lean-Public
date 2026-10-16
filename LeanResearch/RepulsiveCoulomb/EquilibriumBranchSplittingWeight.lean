import LeanResearch.RepulsiveCoulomb.EquilibriumBranchProductDensity
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchModulatedDefinition
import LeanResearch.RepulsiveCoulomb.CoulombPotentialWeight
import LeanResearch.RepulsiveCoulomb.CoulombPairGradientSum

/-! Exact canonical Gibbs splitting, with physical l2 confinement and the
full one-body centering correction. These pointwise identities explicitly
exclude spatial collisions. This records-only source is reconstructed after
the 2026-10-01 recovery and is not the lost earlier draft's exact bytes. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators
namespace RepulsiveCoulomb

def equilibriumSplittingConstant {β : ℝ} (N : ℕ)
    (R : EquilibriumConstructedReference β) : ℝ :=
  Real.exp ((N : ℝ) * R.elConstant - β * (N : ℝ) * equilibriumDensityInteraction R.density / 2)

theorem equilibriumSplittingConstant_pos {β : ℝ} (N : ℕ)
    (R : EquilibriumConstructedReference β) : 0 < equilibriumSplittingConstant N R :=
  Real.exp_pos _

/-- The ordered, label-distinct sum has the exact factor two. Injectivity is
needed because the ordinary real-log value at zero is not a singular energy. -/
theorem equilibriumOffDiagonal_log_vandermonde {N : ℕ} (z : Fin N → ℂ)
    (hz : Function.Injective z) :
    equilibriumOrderedOffDiagonalSum (fun i j => equilibriumLogKernel (z i - z j)) =
      -2 * Real.log ‖coulombVandermonde (WithLp.toLp 2 z)‖ := by
  classical
  have hf : ∀ p ∈ coulombPairs N, ‖z p.1 - z p.2‖ ≠ 0 := by
    intro p hp
    have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun he => hp'.ne (hz he)))
  have hl := Real.log_prod (s := coulombPairs N) (f := fun p => ‖z p.1 - z p.2‖) hf
  have ht := symmetric_pair_sum_twice (fun i j : Fin N => equilibriumLogKernel (z i - z j))
    (fun i j => by simp only [equilibriumLogKernel, norm_sub_rev])
    (fun i => by simp [equilibriumLogKernel])
  have he : equilibriumOrderedOffDiagonalSum (fun i j => equilibriumLogKernel (z i - z j)) =
      ∑ i, ∑ j, equilibriumLogKernel (z i - z j) := by
    unfold equilibriumOrderedOffDiagonalSum
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hij
    · subst j
      simp [equilibriumLogKernel]
    · rfl
  rw [he, ← ht, coulombVandermonde_norm]
  change 2 * (∑ p ∈ coulombPairs N, -Real.log ‖z p.1 - z p.2‖) =
    -2 * Real.log (∏ p ∈ coulombPairs N, ‖z p.1 - z p.2‖)
  rw [hl, Finset.sum_neg_distrib]
  ring

theorem equilibriumCoulombPotential_eq_ordered_energy {N : ℕ} (β : ℝ)
    (z : Fin N → ℂ) (hz : Function.Injective z) :
    coulombPotential β (WithLp.toLp 2 z) = β *
      ((∑ i, ‖z i‖ ^ 2) / 2 +
        equilibriumOrderedOffDiagonalSum (fun i j => equilibriumLogKernel (z i - z j)) /
          (2 * (N : ℝ))) := by
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin N => ℂ) (WithLp.toLp 2 z)
  change ‖WithLp.toLp 2 z‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 at hn
  rw [coulombPotential, hn, equilibriumOffDiagonal_log_vandermonde z hz]
  ring

theorem equilibriumReference_sum_log_density {β : ℝ}
    (R : EquilibriumConstructedReference β) (N : ℕ) (z : Fin N → ℂ) :
    (∑ i, Real.log (R.density (z i))) = (N : ℝ) * R.elConstant - β *
      ((∑ i, ‖z i‖ ^ 2) / 2 + ∑ i, equilibriumDensityPotential R.density (z i)) := by
  simp_rw [R.eulerLagrange, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The actual unnormalized densities agree off spatial collisions; no
centered-sum shorthand drops the canonical one-body correction. -/
theorem equilibriumReference_splitting_weight {β : ℝ}
    (R : EquilibriumConstructedReference β) (N : ℕ) (z : Fin N → ℂ)
    (hz : Function.Injective z) :
    equilibriumProductDensity N R.density z *
        Real.exp (-β * equilibriumModulatedEnergy R.density z) =
      equilibriumSplittingConstant N R * coulombWeight β (WithLp.toLp 2 z) := by
  have hdomain : WithLp.toLp 2 z ∈ coulombDomain N := by
    apply (coulombVandermonde_ne_zero_iff _).mpr
    intro i j hij he
    exact hij (hz he)
  rw [equilibriumReference_product_density_exp, equilibriumReference_sum_log_density,
    coulombWeight_eq_exp_neg_potential β hdomain,
    equilibriumCoulombPotential_eq_ordered_energy β z hz, equilibriumSplittingConstant,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold equilibriumModulatedEnergy
  ring

end RepulsiveCoulomb
