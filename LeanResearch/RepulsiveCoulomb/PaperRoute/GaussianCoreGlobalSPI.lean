module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianCoreLocalSPI
public import LeanResearch.RepulsiveCoulomb.PointCoreCutoffMass
public import LeanResearch.RepulsiveCoulomb.GaussianSPIRate

@[expose] public section

/-! Additive experimental source. Verification status is recorded separately in evidence. Actual cutoff local/exterior absorption using the new local SPI. All rate constants are newly selected. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators ENNReal
namespace RepulsiveCoulomb.PaperRoute

/-- Exterior mass is derived from the same supplied full-domain moment witness. -/
theorem core_exterior_mass_of_moment {γ Q U : ℝ} (hγ : 0 < γ)
    (hMoment : UniformFormMomentBound hγ Q U) :
    ∀ (m : ℕ) (a : Fin m → ℝ) (_ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ),
      (∑ j, a j ≤ Q) → ∀ (R : ℝ) (_hR : 0 < R), 2 * U ≤ R ^ 2 →
      ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      (∀ x ∈ ball (0 : ℂ) R, φ x = 0) →
      (∫ x, φ x ^ 2 ∂pointMeasure γ a y) ≤ (2 * U / R ^ 2) *
        (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) := by
  intro m a ha y hQ R hR hlarge φ hz
  let _ := pointMeasure_isProbability hγ ha y
  have hs : HasCompactSupport (fun x : ℂ => φ x ^ 2) :=
    φ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hi : Integrable (fun x : ℂ => φ x ^ 2) (pointMeasure γ a y) :=
    (φ.continuous.pow 2).integrable_of_hasCompactSupport hs
  obtain ⟨hmi, hmb⟩ := hMoment m a ha y hQ (pointFormCore hγ ha y φ)
  have hv : (fun x : ℂ => ‖x‖ ^ 2 *
      (pointFormValueL hγ ha y (pointFormCore hγ ha y φ) x) ^ 2)
      =ᵐ[pointMeasure γ a y] (fun x => ‖x‖ ^ 2 * φ x ^ 2) := by
    filter_upwards [pointFormCore_value hγ ha y φ] with x hx
    rw [hx]
  have hm := hmi.congr hv
  rw [integral_congr_ae hv, pointFormCore_norm_sq_eq_integrals] at hmb
  have htail := exterior_quadratic_mass hR (φ : ℂ → ℝ) hi hm hz
  exact exterior_moment_absorb hR hlarge (integral_nonneg (fun _ => sq_nonneg _))
    (htail.trans hmb)

theorem core_global_superPoincare_small {γ Q κ S U Rbase : ℝ} (hγ : 0 < γ)
    (hκ : 1 < κ) (hS : 0 < S) (hraw : UniformRawStrongSobolev Q κ S)
    (hU : 0 < U) (hMoment : UniformFormMomentBound hγ Q U)
    (hRbase : 1 ≤ Rbase) (hHalf : UniformHalfMassBall γ Q Rbase) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (_ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ),
      (∑ j, a j ≤ Q) → ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      (∫ x, φ x ^ 2 ∂pointMeasure γ a y) ≤
        s * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        A * Real.exp (B / s) * (∫ x, |φ x| ∂pointMeasure γ a y) ^ 2 := by
  obtain ⟨R₀, A, B, hR₀, hA, hB, hlocal⟩ := core_local_superPoincare hγ hκ hS hraw hRbase hHalf
  have houter := core_exterior_mass_of_moment hγ hMoment
  obtain ⟨K, hK, hKbound⟩ := exists_pointCutoffBump_gradient_bound
  let L := 1 + R₀ ^ 2 + 32 * U + K ^ 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hLR : R₀ ^ 2 ≤ L := by dsimp [L]; nlinarith [sq_nonneg K]
  have hLU : 32 * U ≤ L := by dsimp [L]; nlinarith [sq_nonneg R₀, sq_nonneg K]
  have hLK : K ^ 2 ≤ L := by dsimp [L]; nlinarith [sq_nonneg R₀]
  have hη : 0 < sobolevSPIExponent κ := sobolevSPIExponent_pos hκ
  refine ⟨4 * A * (16 : ℝ) ^ (sobolevSPIExponent κ), 9 * B * L + (sobolevSPIExponent κ), by positivity, by positivity, ?_⟩
  intro m a ha y hQ s hs hs1 φ
  let μ := pointMeasure γ a y
  let R := Real.sqrt (L / s)
  have hRp : 0 < R := Real.sqrt_pos.mpr (div_pos hL hs)
  have hR2 : R ^ 2 = L / s := Real.sq_sqrt (div_pos hL hs).le
  have hRL : L ≤ R ^ 2 := by rw [hR2]; apply (le_div_iff₀ hs).mpr; nlinarith
  have hRR : R₀ ≤ R := by nlinarith [Real.sqrt_nonneg (L / s)]
  have hlarge : 2 * U ≤ R ^ 2 := by linarith
  have hcoeff : 2 * U / R ^ 2 ≤ s / 16 := by
    apply (div_le_iff₀ (sq_pos_of_pos hRp)).mpr
    rw [hR2]
    have hid : s / 16 * (L / s) = L / 16 := by field_simp
    rw [hid]
    linarith
  have hcut : s * (K / R) ^ 2 ≤ 1 := by
    have hid : s * (K / R) ^ 2 = s ^ 2 * K ^ 2 / L := by
      rw [div_pow, hR2]
      field_simp
    rw [hid]
    apply (div_le_iff₀ hL).mpr
    have hs2 : s ^ 2 ≤ 1 := by nlinarith
    have hb := mul_le_mul_of_nonneg_right hs2 (sq_nonneg K)
    nlinarith only [hb, hLK]
  let g := pointCoreInnerCutoff R hRp φ
  let h := pointCoreOuterCutoff R hRp φ
  let β := A * Real.exp (B * (3 * R) ^ 2) * (s / 16) ^ (-(sobolevSPIExponent κ))
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hgSupp : tsupport (g : ℂ → ℝ) ⊆ ball (0 : ℂ) (3 * R) :=
    (pointCore_inner_cutoff_support R hRp φ).trans (closedBall_subset_ball (by linarith))
  have hg := hlocal m a ha y hQ (3 * R) (by linarith) (s / 16) (by positivity) (by linarith) g hgSupp
  have hl1 := pointCore_inner_cutoff_l1 hγ ha y hRp φ
  have hlsq : (∫ x, |g x| ∂μ) ^ 2 ≤ (∫ x, |φ x| ∂μ) ^ 2 := by
    have hgn : 0 ≤ ∫ x, |g x| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
    have hfn : 0 ≤ ∫ x, |φ x| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
    change (∫ x, |g x| ∂μ) ≤ ∫ x, |φ x| ∂μ at hl1
    nlinarith
  have hg' : (∫ x, g x ^ 2 ∂μ) ≤ (s / 16) * (∫ x, ‖gradient (g : ℂ → ℝ) x‖ ^ 2 ∂μ) +
      β * (∫ x, |φ x| ∂μ) ^ 2 :=
    hg.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlsq hβ))
  have hh := houter m a ha y hQ R hRp hlarge h
    (fun x hx => pointCore_outer_cutoff_zero R hRp φ (ball_subset_closedBall hx))
  have hh' : (∫ x, h x ^ 2 ∂μ) ≤ (s / 16) * (∫ x, ‖gradient (h : ℂ → ℝ) x‖ ^ 2 ∂μ) :=
    hh.trans (mul_le_mul_of_nonneg_right hcoeff (integral_nonneg (fun _ => sq_nonneg _)))
  have hpair := pointCore_cutoff_pair_energy hγ ha y hRp (div_pos hK hRp).le (hKbound 0 R hRp) φ
  have hsplit := pointCore_cutoff_mass_split hγ ha y hRp φ
  have hab := spi_cutoff_absorption (integral_nonneg (fun _ => sq_nonneg _)) hs hcut hsplit hg' hh' hpair
  have hrate := gaussian_spi_radius_rate (B := B) hA.le hs hη.le hR2
  have hrate' := mul_le_mul_of_nonneg_right hrate (sq_nonneg (∫ x, |φ x| ∂μ))
  have hE : 0 ≤ ∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  change (∫ x, φ x ^ 2 ∂μ) ≤ (s / 2) * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂μ) +
    4 * β * (∫ x, |φ x| ∂μ) ^ 2 at hab
  change 4 * β * (∫ x, |φ x| ∂μ) ^ 2 ≤ _ at hrate'
  nlinarith only [hab, hrate', mul_nonneg hs.le hE]

theorem core_global_superPoincare {γ Q κ S U Rbase : ℝ} (hγ : 0 < γ)
    (hκ : 1 < κ) (hS : 0 < S) (hraw : UniformRawStrongSobolev Q κ S)
    (hU : 0 < U) (hMoment : UniformFormMomentBound hγ Q U)
    (hRbase : 1 ≤ Rbase) (hHalf : UniformHalfMassBall γ Q Rbase) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (_ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ),
      (∑ j, a j ≤ Q) → ∀ s : ℝ, 0 < s →
      ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      (∫ x, φ x ^ 2 ∂pointMeasure γ a y) ≤
        s * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        A * Real.exp (B / s) * (∫ x, |φ x| ∂pointMeasure γ a y) ^ 2 := by
  obtain ⟨A, B, hA, hB, hb⟩ := core_global_superPoincare_small hγ hκ hS hraw hU hMoment hRbase hHalf
  refine ⟨A * Real.exp B, B, mul_pos hA (Real.exp_pos _), hB, ?_⟩
  intro m a ha y hQ s hs φ
  exact spi_small_to_all hA hB (integral_nonneg (fun _ => sq_nonneg _)) (sq_nonneg _)
    (fun t ht ht1 => hb m a ha y hQ t ht ht1 φ) hs

end RepulsiveCoulomb.PaperRoute
