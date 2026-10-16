import LeanResearch.RepulsiveCoulomb.CoulombLeviQuadratic

/-! Identification and smoothness of the actual effective potential. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

theorem coulombVandermonde_norm {N : ℕ} (z : CoulombConfig N) :
    ‖coulombVandermonde z‖ = ∏ p ∈ coulombPairs N, ‖z p.1 - z p.2‖ := by
  simp [coulombVandermonde, norm_prod]

theorem coulombWeight_eq_exp_neg_potential {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) : coulombWeight β z = Real.exp (-coulombPotential β z) := by
  have hn : 0 < ‖coulombVandermonde z‖ := norm_pos_iff.mpr hz
  rw [coulombWeight, Real.finsetProd_rpow _ _ (fun p _ => norm_nonneg _),
    ← coulombVandermonde_norm, Real.rpow_def_of_pos hn, ← Real.exp_add]
  congr 1
  unfold coulombPotential
  ring

theorem coulombVandermonde_contDiff_real (N : ℕ) :
    ContDiff ℝ ⊤ (coulombVandermonde (N := N)) := by
  have h (p : Fin N × Fin N) : ContDiff ℝ ⊤ (fun z : CoulombConfig N => z p.1 - z p.2) :=
    (coulombCoordinate p.1).contDiff.sub (coulombCoordinate p.2).contDiff
  unfold coulombVandermonde
  fun_prop

theorem coulombPotential_contDiffAt {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) : ContDiffAt ℝ ⊤ (coulombPotential β) z := by
  have hv : coulombVandermonde z ≠ 0 := hz
  have hl := ((coulombVandermonde_contDiff_real N).contDiffAt.norm ℂ hv).log (norm_ne_zero_iff.mpr hv)
  have hn : ContDiffAt ℝ ⊤ (fun x : CoulombConfig N => ‖x‖ ^ 2) z := (contDiff_norm_sq ℝ).contDiffAt
  exact (contDiffAt_const.mul hn).sub (contDiffAt_const.mul hl)

end RepulsiveCoulomb
