import LeanResearch.RepulsiveCoulomb.EquilibriumBranchSupportSign

/-! Exact quadratic-energy expansion for the explicit common-measure sign
representation. This applies to mutually singular nonatomic probabilities,
including circular empirical measures versus planar reference densities,
once their three actual absolute logarithmic energies are supplied. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

private theorem equilibriumSupportSign_product_ae {μ ν : Measure ℂ}
    [SFinite μ] [SFinite ν] {A : Set ℂ} (hA : MeasurableSet A) {c d : ℝ}
    (hc : equilibriumSupportSign A =ᵐ[μ] (fun _ => c))
    (hd : equilibriumSupportSign A =ᵐ[ν] (fun _ => d)) :
    (fun p : ℂ × ℂ => equilibriumSupportSign A p.1 * equilibriumSupportSign A p.2) =ᵐ[μ.prod ν]
      (fun _ => c * d) := by
  have hs := equilibriumSupportSign_measurable hA
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun ((hs.comp measurable_fst).mul (hs.comp measurable_snd)) measurable_const)).mpr
  filter_upwards [hc] with x hx
  filter_upwards [hd] with y hy
  change equilibriumSupportSign A x * equilibriumSupportSign A y = c * d
  rw [hx, hy]

/-- Three genuine absolute logarithmic energies give integrability over the
sum reference squared. The reversed mixed term follows by actual symmetry. -/
theorem equilibriumLogKernel_sum_prod_integrable {σ ρ : Measure ℂ}
    [SFinite σ] [SFinite ρ]
    (hσσ : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) (σ.prod σ))
    (hσρ : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) (σ.prod ρ))
    (hρρ : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) (ρ.prod ρ)) :
    Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) ((σ + ρ).prod (σ + ρ)) := by
  have hρσ : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) (ρ.prod σ) := by
    simpa only [Function.comp_def, Prod.swap, equilibriumLogKernel, norm_sub_rev] using hσρ.swap
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add]
  exact integrable_add_measure.mpr
    ⟨integrable_add_measure.mpr ⟨hσσ, hσρ⟩, integrable_add_measure.mpr ⟨hρσ, hρρ⟩⟩

/-- The common-measure sign form is exactly the usual self-minus-two-cross
plus-reference energy, with every integral justified on its actual measure. -/
theorem equilibriumSupportSign_energy_expansion {σ ρ : Measure ℂ}
    [IsProbabilityMeasure σ] [IsProbabilityMeasure ρ] {A : Set ℂ}
    (hA : MeasurableSet A) (hσ : σ Aᶜ = 0) (hρ : ρ A = 0)
    (hσσ : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) (σ.prod σ))
    (hσρ : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) (σ.prod ρ))
    (hρρ : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) (ρ.prod ρ)) :
    (∫ p : ℂ × ℂ, equilibriumSupportSign A p.1 * equilibriumSupportSign A p.2 *
      equilibriumLogKernel (p.1 - p.2) ∂(σ + ρ).prod (σ + ρ)) =
      (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂σ.prod σ) -
      2 * (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂σ.prod ρ) +
      (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂ρ.prod ρ) := by
  let K : ℂ × ℂ → ℝ := fun p => equilibriumLogKernel (p.1 - p.2)
  let H : ℂ × ℂ → ℝ := fun p => equilibriumSupportSign A p.1 * equilibriumSupportSign A p.2 * K p
  have h1 := equilibriumSupportSign_one_ae hσ
  have hm := equilibriumSupportSign_neg_one_ae hρ
  have heσσ : H =ᵐ[σ.prod σ] K :=
    (equilibriumSupportSign_product_ae hA h1 h1).mono (fun p hp => by
      change equilibriumSupportSign A p.1 * equilibriumSupportSign A p.2 = (1 : ℝ) * 1 at hp
      dsimp only [H]
      rw [hp, one_mul, one_mul])
  have heσρ : H =ᵐ[σ.prod ρ] (fun p => -K p) :=
    (equilibriumSupportSign_product_ae hA h1 hm).mono (fun p hp => by
      change equilibriumSupportSign A p.1 * equilibriumSupportSign A p.2 = (1 : ℝ) * -1 at hp
      dsimp only [H]
      rw [hp]
      ring)
  have heρσ : H =ᵐ[ρ.prod σ] (fun p => -K p) :=
    (equilibriumSupportSign_product_ae hA hm h1).mono (fun p hp => by
      change equilibriumSupportSign A p.1 * equilibriumSupportSign A p.2 = (-1 : ℝ) * 1 at hp
      dsimp only [H]
      rw [hp]
      ring)
  have heρρ : H =ᵐ[ρ.prod ρ] K :=
    (equilibriumSupportSign_product_ae hA hm hm).mono (fun p hp => by
      change equilibriumSupportSign A p.1 * equilibriumSupportSign A p.2 = (-1 : ℝ) * -1 at hp
      dsimp only [H]
      rw [hp]
      ring)
  have hρσ : Integrable K (ρ.prod σ) := by
    simpa only [K, Function.comp_def, Prod.swap, equilibriumLogKernel, norm_sub_rev] using hσρ.swap
  have hHσσ : Integrable H (σ.prod σ) := hσσ.congr heσσ.symm
  have hHσρ : Integrable H (σ.prod ρ) := hσρ.neg.congr heσρ.symm
  have hHρσ : Integrable H (ρ.prod σ) := hρσ.neg.congr heρσ.symm
  have hHρρ : Integrable H (ρ.prod ρ) := hρρ.congr heρρ.symm
  have hswap : (∫ p : ℂ × ℂ, K p ∂ρ.prod σ) = ∫ p : ℂ × ℂ, K p ∂σ.prod ρ := by
    have he := integral_prod_swap (μ := σ) (ν := ρ) K
    simpa only [K, Prod.swap, equilibriumLogKernel, norm_sub_rev] using he
  change (∫ p, H p ∂(σ + ρ).prod (σ + ρ)) = _
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add,
    integral_add_measure (integrable_add_measure.mpr ⟨hHσσ, hHσρ⟩)
      (integrable_add_measure.mpr ⟨hHρσ, hHρρ⟩),
    integral_add_measure hHσσ hHσρ, integral_add_measure hHρσ hHρρ,
    integral_congr_ae heσσ, integral_congr_ae heσρ, integral_congr_ae heρσ,
    integral_congr_ae heρρ, integral_neg, integral_neg, hswap]
  dsimp only [K]
  ring

/-- Genuine signed-measure repulsivity in self/cross-energy form. The common
measure is nonatomic; circles have not been silently replaced by densities. -/
theorem equilibriumMutuallySingular_logRepulsive {σ ρ : Measure ℂ}
    [IsProbabilityMeasure σ] [IsProbabilityMeasure ρ]
    [NullSingletonClass σ] [NullSingletonClass ρ] {A : Set ℂ}
    (hA : MeasurableSet A) (hσ : σ Aᶜ = 0) (hρ : ρ A = 0)
    (hσσ : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) (σ.prod σ))
    (hσρ : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) (σ.prod ρ))
    (hρρ : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) (ρ.prod ρ)) :
    0 ≤ (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂σ.prod σ) -
      2 * (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂σ.prod ρ) +
      (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂ρ.prod ρ) := by
  have hp := equilibriumSupportSign_logRepulsive hA hσ hρ
    (equilibriumLogKernel_sum_prod_integrable hσσ hσρ hρρ)
  rwa [equilibriumSupportSign_energy_expansion hA hσ hρ hσσ hσρ hρρ] at hp

end RepulsiveCoulomb
