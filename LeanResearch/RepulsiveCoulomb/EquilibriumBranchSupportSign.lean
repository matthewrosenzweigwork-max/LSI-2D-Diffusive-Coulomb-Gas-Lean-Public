import LeanResearch.RepulsiveCoulomb.EquilibriumBranchLogPositivity

/-! An explicit common-measure representation of two mutually singular
probability measures supported on opposite sides of a measurable set.
This is the intended circle-support bridge; no RN density is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical
namespace RepulsiveCoulomb

variable {α : Type*} [MeasurableSpace α]

def equilibriumSupportSign (A : Set α) : α → ℝ := by
  classical
  exact fun x => if x ∈ A then 1 else -1

theorem equilibriumSupportSign_measurable {A : Set α} (hA : MeasurableSet A) :
    Measurable (equilibriumSupportSign A) := measurable_const.ite hA measurable_const

theorem equilibriumSupportSign_abs (A : Set α) (x : α) : |equilibriumSupportSign A x| = 1 := by
  by_cases hx : x ∈ A <;> simp [equilibriumSupportSign, hx]

theorem equilibriumSupportSign_integrable {μ : Measure α} [IsFiniteMeasure μ]
    {A : Set α} (hA : MeasurableSet A) : Integrable (equilibriumSupportSign A) μ := by
  apply (integrable_const (1 : ℝ)).mono' (equilibriumSupportSign_measurable hA).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    change ‖equilibriumSupportSign A x‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs, equilibriumSupportSign_abs])

theorem equilibriumSupportSign_one_ae {σ : Measure α} {A : Set α} (hσ : σ Aᶜ = 0) :
    equilibriumSupportSign A =ᵐ[σ] (fun _ => (1 : ℝ)) := by
  have ha : ∀ᵐ x ∂σ, x ∈ A := by
    rw [ae_iff]
    exact hσ
  filter_upwards [ha] with x hx
  simp [equilibriumSupportSign, hx]

theorem equilibriumSupportSign_neg_one_ae {ρ : Measure α} {A : Set α} (hρ : ρ A = 0) :
    equilibriumSupportSign A =ᵐ[ρ] (fun _ => (-1 : ℝ)) := by
  have ha : ∀ᵐ x ∂ρ, x ∉ A := by
    rw [ae_iff]
    simp only [not_not]
    change ρ A = 0
    exact hρ
  filter_upwards [ha] with x hx
  simp [equilibriumSupportSign, hx]

/-- The explicit sign function has zero mass against the sum of the actual
probability measures; all its L1 conditions are automatic from boundedness. -/
theorem integral_equilibriumSupportSign_zero {σ ρ : Measure α}
    [IsProbabilityMeasure σ] [IsProbabilityMeasure ρ] {A : Set α}
    (hA : MeasurableSet A) (hσ : σ Aᶜ = 0) (hρ : ρ A = 0) :
    (∫ x, equilibriumSupportSign A x ∂(σ + ρ)) = 0 := by
  rw [integral_add_measure (equilibriumSupportSign_integrable hA)
    (equilibriumSupportSign_integrable hA)]
  rw [integral_congr_ae (equilibriumSupportSign_one_ae hσ),
    integral_congr_ae (equilibriumSupportSign_neg_one_ae hρ)]
  simp

/-- Actual signed-integral transport, without a hidden RN identification. -/
theorem integral_mul_equilibriumSupportSign {σ ρ : Measure α} {A : Set α}
    (hσ : σ Aᶜ = 0) (hρ : ρ A = 0) {F : α → ℝ}
    (hFσ : Integrable F σ) (hFρ : Integrable F ρ) :
    (∫ x, F x * equilibriumSupportSign A x ∂(σ + ρ)) =
      (∫ x, F x ∂σ) - (∫ x, F x ∂ρ) := by
  have heσ : (fun x => F x * equilibriumSupportSign A x) =ᵐ[σ] F :=
    (equilibriumSupportSign_one_ae hσ).mono (fun x h => by simp only [h, mul_one])
  have heρ : (fun x => F x * equilibriumSupportSign A x) =ᵐ[ρ] (fun x => -F x) :=
    (equilibriumSupportSign_neg_one_ae hρ).mono (fun x h => by simp only [h, mul_neg_one])
  have hiσ := hFσ.congr heσ.symm
  have hiρ := hFρ.neg.congr heρ.symm
  rw [integral_add_measure hiσ hiρ, integral_congr_ae heσ, integral_congr_ae heρ, integral_neg]
  ring


/-- Actual use of the common-measure sign density in logarithmic repulsivity.
For circle-smearing applications, the displayed absolute-energy condition
must still be proved from the circle/reference integrability lemmas. -/
theorem equilibriumSupportSign_logRepulsive {σ ρ : Measure ℂ}
    [IsProbabilityMeasure σ] [IsProbabilityMeasure ρ]
    [NullSingletonClass σ] [NullSingletonClass ρ] {A : Set ℂ}
    (hA : MeasurableSet A) (hσ : σ Aᶜ = 0) (hρ : ρ A = 0)
    (hg : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((σ + ρ).prod (σ + ρ))) :
    0 ≤ ∫ p : ℂ × ℂ, equilibriumSupportSign A p.1 * equilibriumSupportSign A p.2 *
      equilibriumLogKernel (p.1 - p.2) ∂(σ + ρ).prod (σ + ρ) := by
  letI : NullSingletonClass (σ + ρ) := ⟨fun z => by simp⟩
  have hs := equilibriumSupportSign_measurable hA
  have hi : Integrable (fun p : ℂ × ℂ => equilibriumSupportSign A p.1 *
      equilibriumSupportSign A p.2 * equilibriumLogKernel (p.1 - p.2))
      ((σ + ρ).prod (σ + ρ)) := by
    apply hg.mono (((hs.comp measurable_fst).mul (hs.comp measurable_snd)).mul
      (equilibriumLogKernel_measurable.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
    exact Eventually.of_forall (fun p => by
      change ‖equilibriumSupportSign A p.1 * equilibriumSupportSign A p.2 *
        equilibriumLogKernel (p.1 - p.2)‖ ≤ ‖equilibriumLogKernel (p.1 - p.2)‖
      simp only [norm_mul, Real.norm_eq_abs, equilibriumSupportSign_abs, one_mul, le_refl])
  exact equilibriumLogKernel_zeroMass_nonneg hs (equilibriumSupportSign_integrable hA)
    (integral_equilibriumSupportSign_zero hA hσ hρ) hi

end RepulsiveCoulomb
