module

public import LeanResearch.RepulsiveCoulomb.CoulombCenterRelativeFiniteRate
public import LeanResearch.RepulsiveCoulomb.CoulombCenterOptimalFactorization

@[expose] public section

/-! The literal REAL-valued optimal-rate minimum in manuscript prop:com.
Relative finiteness is proved from an actual positive-entropy smooth test,
so this statement does not misuse the ENNReal toReal value of infinity. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

/-- The actual real supremum of all native full-relative-form LSI rates. -/
def coulombHelmertRelativeOptimalLSIRateReal (m : ℕ) {β : ℝ} (hβ : 0 < β) : ℝ :=
  coulombCenterRelativeOptimalRateReal (coulombHelmertRotation (m + 1))
    (coulombHelmertRotation_axis (m + 1)) hβ

theorem coulombHelmertRelativeOptimalLSIRate_finite (m : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombHelmertRelativeOptimalLSIRate m hβ < ∞ :=
  coulombCenterRelativeOptimalRate_lt_top m (coulombHelmertRotation (m + 1))
    (coulombHelmertRotation_axis (m + 1)) hβ

theorem coulombHelmertRelativeOptimalLSIRate_real_bridge (m : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombHelmertRelativeOptimalLSIRate m hβ =
      ENNReal.ofReal (coulombHelmertRelativeOptimalLSIRateReal m hβ) :=
  coulombCenterRelativeOptimalRate_eq_ofReal m (coulombHelmertRotation (m + 1))
    (coulombHelmertRotation_axis (m + 1)) hβ

/-- Literal manuscript equality of actual optimal rates on the original and
relative full physical form domains: rho(P_N)=min(beta,rho(P_N^rel)). -/
theorem coulomb_center_mass_optimal_lsi_rate_real_min (m : ℕ) {β : ℝ} (hβ : 0 < β) :
    poleBranchOptimalLSIRate (m + 2) hβ =
      min β (coulombHelmertRelativeOptimalLSIRateReal m hβ) := by
  have h := coulomb_center_mass_optimal_lsi_rate m hβ
  rw [coulombHelmertRelativeOptimalLSIRate_real_bridge m hβ] at h
  have hr : 0 ≤ coulombHelmertRelativeOptimalLSIRateReal m hβ :=
    coulombCenterRelativeOptimalRateReal_nonneg m (coulombHelmertRotation (m + 1))
      (coulombHelmertRotation_axis (m + 1)) hβ
  have hmin : min (ENNReal.ofReal β) (ENNReal.ofReal (coulombHelmertRelativeOptimalLSIRateReal m hβ)) =
      ENNReal.ofReal (min β (coulombHelmertRelativeOptimalLSIRateReal m hβ)) := by
    rcases le_total β (coulombHelmertRelativeOptimalLSIRateReal m hβ) with hle | hle
    · rw [min_eq_left hle, min_eq_left (ENNReal.ofReal_le_ofReal hle)]
    · rw [min_eq_right hle, min_eq_right (ENNReal.ofReal_le_ofReal hle)]
  rw [hmin] at h
  exact (ENNReal.ofReal_eq_ofReal_iff
    (poleBranchOptimalLSIRate_nonneg (m + 2) (by omega) hβ) (le_min hβ.le hr)).mp h

end RepulsiveCoulomb
