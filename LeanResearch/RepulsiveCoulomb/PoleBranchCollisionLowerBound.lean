module

public import LeanResearch.RepulsiveCoulomb.CoulombDensityLocal
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! Near a generic collision, the normalized Gibbs density dominates the exact
single collision power. Other factors must be nonzero; no such comparison is
asserted at a multiple collision. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def poleBranchCollisionResidual {N : ℕ} (β : ℝ) (p : Fin N × Fin N) (z : CoulombConfig N) : ℝ :=
  (∫ w : CoulombConfig N, coulombWeight β w)⁻¹ *
    Real.exp (-β * ‖z‖ ^ 2 / 2) *
      ∏ q ∈ (coulombPairs N).erase p, ‖z q.1 - z q.2‖ ^ (β / (N : ℝ))

theorem poleBranchCollisionResidual_continuous {N : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (p : Fin N × Fin N) : Continuous (poleBranchCollisionResidual β p) := by
  apply Continuous.mul
  · fun_prop
  · apply continuous_finsetProd
    intro q _
    exact (Real.continuous_rpow_const (div_nonneg hβ (Nat.cast_nonneg N))).comp
      (((coulombCoordinate q.1).continuous.sub (coulombCoordinate q.2).continuous).norm)

theorem poleBranchCollisionResidual_pos {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (p : Fin N × Fin N) (z : CoulombConfig N)
    (hz : ∀ q ∈ (coulombPairs N).erase p, z q.1 ≠ z q.2) :
    0 < poleBranchCollisionResidual β p z := by
  apply mul_pos (mul_pos (inv_pos.mpr (coulombWeight_integral_pos hβ)) (Real.exp_pos _))
  exact Finset.prod_pos (fun q hq =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hz q hq))) _)

theorem poleBranchCollisionResidual_factor {N : ℕ} (β : ℝ) (p : Fin N × Fin N)
    (hp : p ∈ coulombPairs N) (z : CoulombConfig N) :
    coulombDensity N β z = poleBranchCollisionResidual β p z *
      ‖z p.1 - z p.2‖ ^ (β / (N : ℝ)) := by
  classical
  dsimp [coulombDensity, coulombWeight, poleBranchCollisionResidual]
  rw [← Finset.prod_erase_mul (coulombPairs N)
    (fun q => ‖z q.1 - z q.2‖ ^ (β / (N : ℝ))) hp]
  ring

theorem poleBranch_coulomb_collision_lower_neighborhood
    {N : ℕ} {β : ℝ} (hβ : 0 < β) (p : Fin N × Fin N) (hp : p ∈ coulombPairs N)
    (z : CoulombConfig N) (hz : ∀ q ∈ (coulombPairs N).erase p, z q.1 ≠ z q.2) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ w ∈ ball z ε,
      C * ‖w p.1 - w p.2‖ ^ (β / (N : ℝ)) ≤ coulombDensity N β w := by
  let C := poleBranchCollisionResidual β p z / 2
  have hpos := poleBranchCollisionResidual_pos hβ p z hz
  have hC : 0 < C := by dsimp [C]; positivity
  have hevent : ∀ᶠ w in 𝓝 z, C < poleBranchCollisionResidual β p w :=
    (poleBranchCollisionResidual_continuous hβ.le p).continuousAt.eventually
      (lt_mem_nhds (by
        change poleBranchCollisionResidual β p z / 2 < poleBranchCollisionResidual β p z
        linarith))
  obtain ⟨ε, hε, hεp⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨ε, C, hε, hC, ?_⟩
  intro w hw
  rw [poleBranchCollisionResidual_factor β p hp w]
  exact mul_le_mul_of_nonneg_right (hεp (mem_ball.mp hw)).le
    (Real.rpow_nonneg (norm_nonneg _) _)

theorem poleBranch_coulomb_l2_density_integrable
    {N : ℕ} {β : ℝ} (hβ : 0 < β) {f : CoulombConfig N → ℂ}
    (hf : MemLp f 2 (coulombMeasure N β)) :
    Integrable (fun z => coulombDensity N β z * ‖f z‖ ^ 2) := by
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  rw [coulombMeasure_eq_withDensity hβ] at hi
  have H := (integrable_withDensity_iff_integrable_smul'
    (coulombDensity_continuous hβ.le).measurable.ennreal_ofReal
    (Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))).mp hi
  simpa only [ENNReal.toReal_ofReal (coulombDensity_nonneg (N := N) β _), smul_eq_mul] using H

theorem poleBranch_coulomb_aestronglyMeasurable_volume
    {N : ℕ} {β : ℝ} (hβ : 0 < β) {f : CoulombConfig N → ℂ}
    (hf : AEStronglyMeasurable f (coulombMeasure N β)) : AEStronglyMeasurable f volume := by
  obtain ⟨g, hg, heq⟩ := hf
  exact ⟨g, hg, (coulombMeasure_ae_iff hβ).mp heq⟩

theorem poleBranch_coulomb_collision_l2_integrableOn
    {N : ℕ} {β C : ℝ} (hβ : 0 < β) (hC : 0 < C) (p : Fin N × Fin N)
    {U : Set (CoulombConfig N)} (hU : MeasurableSet U) {f : CoulombConfig N → ℂ}
    (hf : MemLp f 2 (coulombMeasure N β))
    (hb : ∀ z ∈ U, C * ‖z p.1 - z p.2‖ ^ (β / (N : ℝ)) ≤ coulombDensity N β z) :
    IntegrableOn (fun z => ‖z p.1 - z p.2‖ ^ (β / (N : ℝ)) * ‖f z‖ ^ 2) U := by
  have hi := (poleBranch_coulomb_l2_density_integrable hβ hf).restrict (s := U)
  have hm := poleBranch_coulomb_aestronglyMeasurable_volume hβ hf.aestronglyMeasurable
  have hp : Continuous (fun z : CoulombConfig N => ‖z p.1 - z p.2‖ ^ (β / (N : ℝ))) :=
    (Real.continuous_rpow_const (div_nonneg hβ.le (Nat.cast_nonneg N))).comp
      (((coulombCoordinate p.1).continuous.sub (coulombCoordinate p.2).continuous).norm)
  apply (hi.const_mul C⁻¹).mono' ((hp.aestronglyMeasurable.mul (hm.norm.pow 2)).restrict)
  filter_upwards [ae_restrict_mem hU] with z hz
  have hw : 0 ≤ ‖z p.1 - z p.2‖ ^ (β / (N : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  calc
    _ = C⁻¹ * (C * (‖z p.1 - z p.2‖ ^ (β / (N : ℝ)) * ‖f z‖ ^ 2)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
    _ ≤ C⁻¹ * (coulombDensity N β z * ‖f z‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hC.le)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hb z hz) (sq_nonneg ‖f z‖)

end RepulsiveCoulomb
