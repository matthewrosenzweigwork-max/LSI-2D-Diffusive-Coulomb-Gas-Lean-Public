import LeanResearch.RepulsiveCoulomb.CoulombCenterOptimalOrder
import LeanResearch.RepulsiveCoulomb.CoulombCenterFactorization
import LeanResearch.RepulsiveCoulomb.CoulombGaussianSharpLSI

/-! Exact optimal-rate equality in prop:com. Both factor tests and tensorization
use genuine physical closed domains. The original optimal rate is the source's
real supremum; the relative optimal rate is its actual full-domain extended
supremum, so the statement also covers a possible infinite factor rate. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem coulombCenter_admissible_iff_beta_relative (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ) :
    poleBranchAdmissibleLSIRate (m + 2) hβ ρ ↔
      ρ ≤ β ∧ coulombCenterRelativeAdmissibleRate e he hβ ρ := by
  rw [coulombCenter_admissible_iff_factor_cores m e he hβ hρ]
  have hG : CoulombCenterGaussianCoreLSI β (2 / ρ) ↔ ρ ≤ β :=
    coulombCenterGaussian_core_lsi_iff hβ hρ
  rw [hG]
  unfold coulombCenterRelativeAdmissibleRate
  rw [coulombCenterRelative_full_iff_core e he hβ]
  simp only [hρ, true_and]

theorem coulombCenter_rates_eq_intersection (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β : ℝ} (hβ : 0 < β) :
    poleBranchLSIRates (m + 2) hβ = Set.Icc 0 β ∩ coulombCenterRelativeRates e he hβ := by
  ext ρ
  constructor
  · rintro (rfl | hρ)
    · exact ⟨⟨le_rfl, hβ.le⟩, Or.inl rfl⟩
    · have h := (coulombCenter_admissible_iff_beta_relative m e he hβ hρ.1).mp hρ
      exact ⟨⟨hρ.1.le, h.1⟩, Or.inr h.2⟩
  · rintro ⟨hρβ, hρ⟩
    rcases hρ with rfl | hρ
    · exact Or.inl rfl
    · exact Or.inr ((coulombCenter_admissible_iff_beta_relative m e he hβ hρ.1).mpr
        ⟨hρβ.2, hρ⟩)

/-- Exact full-domain optimal-rate tensorization, with no finite-relative-rate
assumption and no replacement of the original optimal constant by a witness. -/
theorem coulombCenter_optimal_rate_min (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β : ℝ} (hβ : 0 < β) :
    ENNReal.ofReal (poleBranchOptimalLSIRate (m + 2) hβ) =
      min (ENNReal.ofReal β) (coulombCenterRelativeOptimalRate e he hβ) := by
  rw [coulombCenter_originalOptimalRate_extended (m + 2) (by omega) hβ,
    coulombCenter_rates_eq_intersection m e he hβ,
    coulombCenter_ofReal_image_inter (fun _ hr => hr.1)
      (fun r hr => coulombCenterRelativeRates_nonneg e he hβ hr)]
  have hI : IsLowerSet (ENNReal.ofReal '' Set.Icc 0 β) :=
    coulombCenter_ofReal_rates_lower (fun _ hr => hr.1)
      (fun r hr s hs hsr => ⟨hs, hsr.trans hr.2⟩)
  have hR : IsLowerSet (ENNReal.ofReal '' coulombCenterRelativeRates e he hβ) :=
    coulombCenter_ofReal_rates_lower
      (fun r hr => coulombCenterRelativeRates_nonneg e he hβ hr)
      (fun r hr s hs hsr => coulombCenterRelativeRates_downward e he hβ hr hs hsr)
  rw [coulombCenter_sSup_inter_lower hI hR, coulombCenter_sSup_ofReal_Icc hβ.le]
  rfl

/-- The optimal rate of the actual relative Helmert law, on its native closed
physical form domain. It is extended-valued only to preserve the ∞ convention. -/
def coulombHelmertRelativeOptimalLSIRate (m : ℕ) {β : ℝ} (hβ : 0 < β) : ℝ≥0∞ :=
  coulombCenterRelativeOptimalRate (coulombHelmertRotation (m + 1))
    (coulombHelmertRotation_axis (m + 1)) hβ

/-- Manuscript prop:com optimal-rate conclusion for every N=m+2 and β>0. -/
theorem coulomb_center_mass_optimal_lsi_rate (m : ℕ) {β : ℝ} (hβ : 0 < β) :
    ENNReal.ofReal (poleBranchOptimalLSIRate (m + 2) hβ) =
      min (ENNReal.ofReal β) (coulombHelmertRelativeOptimalLSIRate m hβ) :=
  coulombCenter_optimal_rate_min m (coulombHelmertRotation (m + 1))
    (coulombHelmertRotation_axis (m + 1)) hβ

/-- The real optimal many-particle rate is bounded by the actual Gaussian rate. -/
theorem coulomb_center_mass_optimal_lsi_rate_le_beta (m : ℕ) {β : ℝ} (hβ : 0 < β) :
    poleBranchOptimalLSIRate (m + 2) hβ ≤ β := by
  apply (ENNReal.ofReal_le_ofReal_iff hβ.le).mp
  rw [coulomb_center_mass_optimal_lsi_rate m hβ]
  exact min_le_left _ _

/-- A real-valued restatement without an arbitrary ∞→0 conversion: the minimum
is finite because of the Gaussian factor before toReal is applied. -/
theorem coulomb_center_mass_optimal_lsi_rate_real (m : ℕ) {β : ℝ} (hβ : 0 < β) :
    poleBranchOptimalLSIRate (m + 2) hβ =
      (min (ENNReal.ofReal β) (coulombHelmertRelativeOptimalLSIRate m hβ)).toReal := by
  rw [← coulomb_center_mass_optimal_lsi_rate m hβ,
    ENNReal.toReal_ofReal (poleBranchOptimalLSIRate_nonneg (m + 2) (by omega) hβ)]

end RepulsiveCoulomb
