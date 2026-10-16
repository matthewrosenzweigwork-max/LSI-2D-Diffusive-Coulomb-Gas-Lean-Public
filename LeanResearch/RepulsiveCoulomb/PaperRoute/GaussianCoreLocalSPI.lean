import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianCoreLocalNorm
import LeanResearch.RepulsiveCoulomb.L1LqInterpolation
import LeanResearch.RepulsiveCoulomb.SuperPoincareCoefficients

/-! Additive experimental source. Verification status is recorded separately in evidence. Generic-exponent local SPI from the new Gaussian geometry. The exponent κ/(κ-1) is not the weight cap Q. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators ENNReal
namespace RepulsiveCoulomb.PaperRoute

theorem testFunction_abs_rpow_integrable (Ω : TopologicalSpace.Opens ℂ)
    (φ : TestFunction Ω ℝ ⊤) (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) : Integrable (fun x => |φ x| ^ r) μ := by
  have hc : Continuous (fun x : ℂ => |φ x| ^ r) :=
    (Real.continuous_rpow_const hr.le).comp φ.continuous.abs
  have hs : HasCompactSupport (fun x : ℂ => |φ x| ^ r) :=
    φ.hasCompactSupport.comp_left (g := fun t : ℝ => |t| ^ r)
      (by simp [Real.zero_rpow hr.ne'])
  exact hc.integrable_of_hasCompactSupport hs

def sobolevSPIExponent (κ : ℝ) : ℝ := κ / (κ - 1)

theorem sobolevSPIExponent_pos {κ : ℝ} (hκ : 1 < κ) : 0 < sobolevSPIExponent κ :=
  div_pos (by linarith) (by linarith)

theorem core_local_superPoincare {γ Q κ S Rbase : ℝ} (hγ : 0 < γ)
    (hκ : 1 < κ) (hS : 0 < S) (hraw : UniformRawStrongSobolev Q κ S)
    (hRbase : 1 ≤ Rbase) (hHalf : UniformHalfMassBall γ Q Rbase) :
    ∃ R₀ A B : ℝ, 1 ≤ R₀ ∧ 0 < A ∧ 0 < B ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (_ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ),
      (∑ j, a j ≤ Q) → ∀ R : ℝ, R₀ ≤ R → ∀ u : ℝ, 0 < u → u ≤ 1 →
      ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      tsupport (φ : ℂ → ℝ) ⊆ ball (0 : ℂ) R →
      (∫ x, φ x ^ 2 ∂pointMeasure γ a y) ≤
        u * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        A * Real.exp (B * R ^ 2) * u ^ (-sobolevSPIExponent κ) * (∫ x, |φ x| ∂pointMeasure γ a y) ^ 2 := by
  obtain ⟨R₀, hR₀, hn⟩ := core_local_uncentered_norm hγ hκ hS hraw hRbase hHalf
  let C := gaussianLocalConstant γ κ S
  let θ := κ / (2 * κ - 1)
  let η := sobolevSPIExponent κ
  have hC : 0 < C := gaussianLocalConstant_pos hγ κ S
  have hη : 0 < η := sobolevSPIExponent_pos hκ
  have hθ0 : 0 < θ := div_pos (by linarith) (by linarith)
  have hθ1 : θ < 1 := by dsimp [θ]; apply (div_lt_one (by linarith)).mpr; linarith
  have hθη : θ / (1 - θ) = η := by
    apply (div_eq_iff (show 1 - θ ≠ 0 by linarith)).mpr
    have hden : 2 * κ - 1 ≠ 0 := by linarith
    have hk1 : κ - 1 ≠ 0 := by linarith
    have hd : (1 - θ) * (2 * κ - 1) = κ - 1 := by
      dsimp only [θ]
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hden]
      ring
    apply mul_right_cancel₀ hden
    calc
      θ * (2 * κ - 1) = κ := div_mul_cancel₀ _ hden
      _ = η * (κ - 1) := (div_mul_cancel₀ _ hk1).symm
      _ = (η * (1 - θ)) * (2 * κ - 1) := by rw [mul_assoc, hd]
  refine ⟨R₀, 1 + (8 + 8 * C ^ 2) ^ η, (2 * C + 1) * η, hR₀, by positivity,
    mul_pos (by linarith) hη, ?_⟩
  intro m a ha y hQ R hR u hu hu1 φ hs
  let _ := pointMeasure_isProbability hγ ha y
  let μ := pointMeasure γ a y
  let r := 2 * κ
  let H := C * Real.exp (C * R ^ 2) * R
  let D := 8 + 8 * H ^ 2
  let E := ∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂μ
  let L := ∫ x, |φ x| ∂μ
  let N := ∫ x, |φ x| ^ r ∂μ
  have hr : 2 < r := by dsimp [r]; linarith
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  have hL : 0 ≤ L := integral_nonneg (fun _ => abs_nonneg _)
  have hN : 0 ≤ N := integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hH : 0 ≤ H := by dsimp [H]; exact mul_nonneg (mul_nonneg hC.le (Real.exp_pos _).le) (by linarith)
  have hD : 0 < D := by dsimp [D]; positivity
  have h1 : Integrable (fun x : ℂ => |φ x|) μ :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).abs
  have hrint := testFunction_abs_rpow_integrable (pointDomain a y) φ μ (by linarith : 0 < r)
  have hsq : HasCompactSupport (fun x : ℂ => φ x ^ 2) :=
    φ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have h2 : Integrable (fun x : ℂ => φ x ^ 2) μ := (φ.continuous.pow 2).integrable_of_hasCompactSupport hsq
  have ht : r / (2 * (r - 1)) = θ := by
    dsimp [r, θ]
    field_simp [show 2 * κ - 1 ≠ 0 by linarith]
  have hi := l1_lq_l2_interpolation hr h1 hrint h2
  change (∫ x, φ x ^ 2 ∂μ) ≤ (N ^ (2 / r)) ^ (r / (2 * (r - 1))) * (L ^ 2) ^ (1 - r / (2 * (r - 1))) at hi
  rw [ht] at hi
  have hnorm : N ^ (1 / r) ≤ 2 * L + 2 * H * Real.sqrt E := by
    simpa only [Real.norm_eq_abs] using hn m a ha y hQ R hR φ hs
  have hsquare := local_norm_square_bound (Real.rpow_nonneg hN _) hL hE hH hnorm
  have hpow : (N ^ (1 / r)) ^ 2 = N ^ (2 / r) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hN]
    congr 1
    ring
  rw [hpow] at hsquare
  have hab := local_interpolation_energy_absorb (Real.rpow_nonneg hN _) (sq_nonneg L) hE hD hθ0 hθ1 hu hi hsquare
  rw [interpolation_coefficient_identity hD hu hθ1, show -θ / (1 - θ) = -(θ / (1 - θ)) by ring, hθη] at hab
  have hDbound : D ≤ (8 + 8 * C ^ 2) * Real.exp ((2 * C + 1) * R ^ 2) := local_gaussian_square_coefficient hC.le
  have hcoef := local_spi_coefficient_bound hD.le (by positivity : 0 < 8 + 8 * C ^ 2)
    (by linarith : 0 ≤ 2 * C + 1) hη.le hu hu1 hDbound
  exact hab.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef (sq_nonneg L)))

end RepulsiveCoulomb.PaperRoute
