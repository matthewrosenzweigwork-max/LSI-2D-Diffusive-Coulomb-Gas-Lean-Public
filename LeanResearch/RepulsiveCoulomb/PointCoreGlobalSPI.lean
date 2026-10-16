module

public import LeanResearch.RepulsiveCoulomb.PointCoreCutoffMass
public import LeanResearch.RepulsiveCoulomb.GaussianSPIRate

@[expose] public section

/-! Configuration-uniform Gaussian-rate super-Poincare on the actual original core. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointCore_global_superPoincare_small {γ Q : ℝ} (hγ : 0 < γ) (hQ0 : 0 ≤ Q) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ),
      (∑ j, a j ≤ Q) → ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      (∫ x, φ x ^ 2 ∂pointMeasure γ a y) ≤
        s * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        A * Real.exp (B / s) * (∫ x, |φ x| ∂pointMeasure γ a y) ^ 2 := by
  obtain ⟨R₀, A, B, hR₀, hA, hB, hlocal⟩ := pointCore_local_superPoincare hγ hQ0
  obtain ⟨U, hU, houter⟩ := pointCore_uniform_exterior_mass (Q := Q) hγ
  obtain ⟨K, hK, hKbound⟩ := exists_pointCutoffBump_gradient_bound
  let L := 1 + R₀ ^ 2 + 32 * U + K ^ 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hLR : R₀ ^ 2 ≤ L := by dsimp [L]; nlinarith [sq_nonneg K]
  have hLU : 32 * U ≤ L := by dsimp [L]; nlinarith [sq_nonneg R₀, sq_nonneg K]
  have hLK : K ^ 2 ≤ L := by dsimp [L]; nlinarith [sq_nonneg R₀]
  have hη : 0 < Q + 2 := by linarith
  refine ⟨4 * A * (16 : ℝ) ^ (Q + 2), 9 * B * L + (Q + 2), by positivity, by positivity, ?_⟩
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
      <;> ring
    rw [hid]
    apply (div_le_iff₀ hL).mpr
    have hs2 : s ^ 2 ≤ 1 := by nlinarith
    have hb := mul_le_mul_of_nonneg_right hs2 (sq_nonneg K)
    nlinarith only [hb, hLK]
  let g := pointCoreInnerCutoff R hRp φ
  let h := pointCoreOuterCutoff R hRp φ
  let β := A * Real.exp (B * (3 * R) ^ 2) * (s / 16) ^ (-(Q + 2))
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

theorem pointCore_global_superPoincare {γ Q : ℝ} (hγ : 0 < γ) (hQ0 : 0 ≤ Q) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ),
      (∑ j, a j ≤ Q) → ∀ s : ℝ, 0 < s →
      ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      (∫ x, φ x ^ 2 ∂pointMeasure γ a y) ≤
        s * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        A * Real.exp (B / s) * (∫ x, |φ x| ∂pointMeasure γ a y) ^ 2 := by
  obtain ⟨A, B, hA, hB, hb⟩ := pointCore_global_superPoincare_small hγ hQ0
  refine ⟨A * Real.exp B, B, mul_pos hA (Real.exp_pos _), hB, ?_⟩
  intro m a ha y hQ s hs φ
  exact spi_small_to_all hA hB (integral_nonneg (fun _ => sq_nonneg _)) (sq_nonneg _)
    (fun t ht ht1 => hb m a ha y hQ t ht ht1 φ) hs

end RepulsiveCoulomb
