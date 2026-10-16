module

public import LeanResearch.RepulsiveCoulomb.PoleBranchPairComplexChart
public import LeanResearch.RepulsiveCoulomb.PoleBranchCollisionLowerBound

@[expose] public section

/-! Actual Gibbs L2 integrability becomes the exact |u|^(beta/(N+2)) weighted
product integrability required by the parameter-dependent removal theorem. -/
noncomputable section
open Set MeasureTheory Metric
namespace RepulsiveCoulomb

theorem poleBranch_pair_weighted_integrable
    {N : ℕ} {β C R : ℝ} (hβ : 0 < β) (hC : 0 < C)
    (σ : Equiv.Perm (Fin (N + 2))) (i j : Fin (N + 2))
    (hσ0 : σ 0 = i) (hσ1 : σ (Fin.succ 0) = j)
    {K : Set (CoulombConfig (N + 2))} (hK : MeasurableSet K)
    {U : Set (ℂ × CoulombConfig N)} {f : CoulombConfig (N + 2) → ℂ}
    (hf : MemLp f 2 (coulombMeasure (N + 2) β))
    (hb : ∀ z ∈ K, C * ‖z i - z j‖ ^ (β / ((N + 2 : ℕ) : ℝ)) ≤ coulombDensity (N + 2) β z)
    (hmap : MapsTo (poleBranchPairChart σ) (U ×ˢ ball (0 : ℂ) R) K) :
    Integrable (fun p : (ℂ × CoulombConfig N) × ℂ =>
      ‖p.2‖ ^ (β / ((N + 2 : ℕ) : ℝ)) * ‖f (poleBranchPairChart σ p)‖ ^ 2)
      ((volume.restrict U).prod (volume.restrict (ball (0 : ℂ) R))) := by
  have hi := poleBranch_coulomb_collision_l2_integrableOn hβ hC (i, j) hK hf hb
  have hpull := (poleBranchPairChart_measurePreserving σ).integrableOn_comp_preimage
    (poleBranchPairChart σ).toHomeomorph.toMeasurableEquiv.measurableEmbedding |>.mpr hi
  have hloc := hpull.mono_set hmap
  let a := β / ((N + 2 : ℕ) : ℝ)
  have hc : (Real.sqrt 2) ^ a ≠ 0 :=
    (Real.rpow_pos_of_pos (Real.sqrt_pos.mpr (by norm_num)) a).ne'
  have H : IntegrableOn (fun p : (ℂ × CoulombConfig N) × ℂ =>
      ‖p.2‖ ^ a * ‖f (poleBranchPairChart σ p)‖ ^ 2) (U ×ˢ ball (0 : ℂ) R)
      (volume : Measure ((ℂ × CoulombConfig N) × ℂ)) := by
    change Integrable (fun p : (ℂ × CoulombConfig N) × ℂ =>
      ‖p.2‖ ^ a * ‖f (poleBranchPairChart σ p)‖ ^ 2)
      (volume.restrict (U ×ˢ ball (0 : ℂ) R))
    apply (hloc.const_mul ((Real.sqrt 2) ^ a)⁻¹).congr
    filter_upwards with p
    change ((Real.sqrt 2) ^ a)⁻¹ *
      (‖poleBranchPairChart σ p i - poleBranchPairChart σ p j‖ ^ a * ‖f (poleBranchPairChart σ p)‖ ^ 2) = _
    rw [poleBranchPairChart_difference σ i j hσ0 hσ1,
      norm_real_smul_rpow _ _ (Real.sqrt_nonneg 2),
      ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact H

end RepulsiveCoulomb
