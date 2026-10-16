import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalGaussianWeightedRoute
import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchCoulombLabels
import LeanResearch.RepulsiveCoulomb.CoulombCoreConditional

/-! Additive experimental source; verification is recorded separately in evidence. Actual one-site full-domain entropy
and summed conditional core costs from the newly proved weighted witnesses.
No thermal reference, partition bound, or final labeled LSI is selected here.
Imported conditional helper files may contain old endpoints; eventual audits
must inspect actual declaration bodies, not reject unused imported siblings. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory InformationTheory
open PeriodicAttractiveLogGas
open scoped BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem paper_core_entropy_of_full_one_site {β K : ℝ} (hβ : 0 < β)
    (hFull : ∀ (N : ℕ) (y : CoulombConfig N),
      ∀ u : PointFormDomain hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j),
      entropy (coulombOneSiteKernel N β hβ y)
        (fun w => (pointFormValueL hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) u w) ^ 2) ≤
        ((K * pointFormEnergy hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) u : ℝ) : EReal)) :
    ∀ (N : ℕ) (y : CoulombConfig N) (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤),
      entropy (coulombOneSiteKernel N β hβ y) (fun w => φ (coulombInsertZero w y) ^ 2) ≤
        ((K * (∫ w, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) (coulombInsertZero w y) 0‖ ^ 2
          ∂coulombOneSiteKernel N β hβ y) : ℝ) : EReal) := by
  intro N y φ
  let a := coulombOneSiteExponents N β
  let ha := coulombOneSiteExponents_nonneg N hβ.le
  let ψ := coulombCoreSliceZero a φ y
  have h := hFull N y (pointFormCore hβ ha (fun j => y j) ψ)
  have hval := (pointFormCore_value hβ ha (fun j => y j) ψ).mono
    (fun _ hx => congrArg (fun t : ℝ => t ^ 2) hx)
  rw [coulombOneSiteKernel_apply, entropy_congr_ae hval, pointFormCore_energy_eq_integral] at h
  simpa only [ψ, coulombCoreSliceZero_apply, coulombCoreSliceZero_gradient,
    coulombOneSiteKernel_apply] using h

def paperOneSiteRate (β : ℝ) : ℝ := paperRhoWt β β

def paperOneSiteIntervalRate (a b : ℝ) : ℝ := a * paperRhoWt 1 b

theorem paperOneSiteRate_pos {β : ℝ} (hβ : 0 < β) :
    0 < paperOneSiteRate β := paperRhoWt_pos hβ β

theorem paperOneSiteIntervalRate_pos {a b : ℝ} (ha : 0 < a) :
    0 < paperOneSiteIntervalRate a b :=
  mul_pos ha (paperRhoWt_pos (by norm_num : (0 : ℝ) < 1) b)

theorem paper_one_site_full {γ₀ β Q : ℝ}
    (hγ₀ : 0 < γ₀) (hβ : 0 < β) (hlo : γ₀ ≤ β) (hhi : β ≤ Q)
    (N : ℕ) (y : CoulombConfig N)
    (u : PointFormDomain hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j)) :
    entropy (coulombOneSiteKernel N β hβ y)
      (fun w => (pointFormValueL hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) u w) ^ 2) ≤
      (((2 / paperRhoWt γ₀ Q) *
        pointFormEnergy hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) u : ℝ) : EReal) := by
  have hQ := (coulomb_one_site_exponent_sum_lt N hβ).le.trans hhi
  simpa only [coulombOneSiteKernel_apply] using
    (paper_weighted_named_full_above Q hγ₀ hβ hlo N (coulombOneSiteExponents N β)
      (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) hQ u).2

/-- The same fixed one-site rate, without another existential selection,
is fed through every conditional core integration. -/
theorem paper_core_sum_of_one_site_rate {β rho : ℝ} (hβ : 0 < β)
    (hFull : ∀ (N : ℕ) (y : CoulombConfig N),
      ∀ u : PointFormDomain hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j),
      entropy (coulombOneSiteKernel N β hβ y)
        (fun w => (pointFormValueL hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) u w) ^ 2) ≤
        (((2 / rho) * pointFormEnergy hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) u : ℝ) : EReal))
    (N : ℕ) (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤)
    (hmass : (∫ z, φ z ^ 2 ∂coulombMeasure (N + 1) β) = 1) :
    (∑ i : Fin (N + 1), (conditionalEntropyBranchCoulombSiteCost hβ
      (conditionalEntropyBranchCoulombCoreLaw β φ) i).toReal) ≤
      (2 / rho) * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z‖ ^ 2 ∂coulombMeasure (N + 1) β) := by
  have hsum := conditionalEntropyBranch_coulomb_sum_core_upper_of_sites hβ (2 / rho)
    (conditionalEntropyBranch_coulomb_all_sites_core_upper_of_first hβ (2 / rho)
      (conditionalEntropyBranch_coulomb_first_core_upper_of_conditional hβ (2 / rho)
        (paper_core_entropy_of_full_one_site hβ hFull)))
  exact (hsum N φ hmass).2

/-- New weighted witnesses, actually integrated over every conditional core. -/
theorem paper_core_one_site_sum {β : ℝ} (hβ : 0 < β)
    (N : ℕ) (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤)
    (hmass : (∫ z, φ z ^ 2 ∂coulombMeasure (N + 1) β) = 1) :
    (∑ i : Fin (N + 1), (conditionalEntropyBranchCoulombSiteCost hβ
      (conditionalEntropyBranchCoulombCoreLaw β φ) i).toReal) ≤
      (2 / paperOneSiteRate β) *
        (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z‖ ^ 2 ∂coulombMeasure (N + 1) β) :=
  paper_core_sum_of_one_site_rate hβ (paper_one_site_full hβ hβ le_rfl le_rfl) N φ hmass

/-- A single positive-temperature floor and total-exponent cap are selected
before beta, particle number, frozen coordinates, or the observable. -/
theorem paper_core_one_site_sum_compact {a b β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hlo : a ≤ β) (hhi : β ≤ b)
    (N : ℕ) (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤)
    (hmass : (∫ z, φ z ^ 2 ∂coulombMeasure (N + 1) β) = 1) :
    (∑ i : Fin (N + 1), (conditionalEntropyBranchCoulombSiteCost hβ
      (conditionalEntropyBranchCoulombCoreLaw β φ) i).toReal) ≤
      (2 / paperOneSiteIntervalRate a b) *
        (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z‖ ^ 2 ∂coulombMeasure (N + 1) β) := by
  have hFull := paper_one_site_full ha hβ hlo hhi
  rw [paperRhoWt_scaling] at hFull
  exact paper_core_sum_of_one_site_rate hβ hFull N φ hmass

end RepulsiveCoulomb.PaperRoute
