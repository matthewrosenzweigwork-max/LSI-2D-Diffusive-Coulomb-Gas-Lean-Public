import LeanResearch.RepulsiveCoulomb.CoulombDensityLocal

/-! Smoothness of the exact many-particle density off the full collision set. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulombWeight_contDiffAt {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) : ContDiffAt ℝ ⊤ (coulombWeight β) z := by
  have hz' := (coulombVandermonde_ne_zero_iff z).mp hz
  have hfactor (p : Fin N × Fin N) : ContDiffAt ℝ ⊤
      (fun x : CoulombConfig N => ‖x p.1 - x p.2‖ ^ (β / (N : ℝ))) z := by
    by_cases hp : p.1 = p.2
    · simpa only [hp, sub_self, norm_zero] using
        (contDiffAt_const : ContDiffAt ℝ ⊤ (fun _ : CoulombConfig N => (0 : ℝ) ^ (β / (N : ℝ))) z)
    · have hne : z p.1 - z p.2 ≠ 0 := sub_ne_zero.mpr (hz' p.1 p.2 hp)
      exact (((coulombCoordinate p.1).contDiff.contDiffAt.sub
        (coulombCoordinate p.2).contDiff.contDiffAt).norm ℂ hne).rpow_const_of_ne (norm_ne_zero_iff.mpr hne)
  have hprod : ContDiffAt ℝ ⊤ (fun x : CoulombConfig N =>
      ∏ p ∈ coulombPairs N, ‖x p.1 - x p.2‖ ^ (β / (N : ℝ))) z := by fun_prop
  have hnorm : ContDiffAt ℝ ⊤ (fun x : CoulombConfig N => ‖x‖ ^ 2) z := (contDiff_norm_sq ℝ).contDiffAt
  have hgauss : ContDiffAt ℝ ⊤ (fun x : CoulombConfig N => Real.exp (-β * ‖x‖ ^ 2 / 2)) z := by fun_prop
  exact hgauss.mul hprod

theorem coulombDensity_contDiffAt {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) : ContDiffAt ℝ ⊤ (coulombDensity N β) z :=
  contDiffAt_const.mul (coulombWeight_contDiffAt β hz)

theorem coulombDensity_contDiffOn (N : ℕ) (β : ℝ) :
    ContDiffOn ℝ ⊤ (coulombDensity N β) (coulombDomain N) :=
  fun _ hz => (coulombDensity_contDiffAt β hz).contDiffWithinAt

end RepulsiveCoulomb
