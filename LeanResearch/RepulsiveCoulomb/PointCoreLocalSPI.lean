import LeanResearch.RepulsiveCoulomb.PointCoreLocalNorm
import LeanResearch.RepulsiveCoulomb.L1LqInterpolation
import LeanResearch.RepulsiveCoulomb.SuperPoincareCoefficients

/-! Actual local super-Poincare with Gaussian radius dependence. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem testFunction_abs_rpow_integrable (Ω : TopologicalSpace.Opens ℂ)
    (φ : TestFunction Ω ℝ ⊤) (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) : Integrable (fun x => |φ x| ^ r) μ := by
  have hc : Continuous (fun x : ℂ => |φ x| ^ r) :=
    (Real.continuous_rpow_const hr.le).comp φ.continuous.abs
  have hs : HasCompactSupport (fun x : ℂ => |φ x| ^ r) :=
    φ.hasCompactSupport.comp_left (g := fun t : ℝ => |t| ^ r)
      (by simp [Real.zero_rpow hr.ne'])
  exact hc.integrable_of_hasCompactSupport hs

theorem pointCore_local_superPoincare {γ Q : ℝ} (hγ : 0 < γ) (hQ0 : 0 ≤ Q) :
    ∃ R₀ A B : ℝ, 1 ≤ R₀ ∧ 0 < A ∧ 0 < B ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ),
      (∑ j, a j ≤ Q) → ∀ R : ℝ, R₀ ≤ R → ∀ u : ℝ, 0 < u → u ≤ 1 →
      ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      tsupport (φ : ℂ → ℝ) ⊆ ball (0 : ℂ) R →
      (∫ x, φ x ^ 2 ∂pointMeasure γ a y) ≤
        u * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        A * Real.exp (B * R ^ 2) * u ^ (-(Q + 2)) * (∫ x, |φ x| ∂pointMeasure γ a y) ^ 2 := by
  obtain ⟨R₀, hR₀, hn⟩ := pointCore_local_uncentered_norm hγ hQ0
  let C := pointGaussianLocalConstant γ Q (pointUniformMeanTransferConstant Q)
  let θ := (Q + 2) / (Q + 3)
  let η := Q + 2
  have hC : 0 < C := pointGaussianLocalConstant_pos hγ Q _
  have hη : 0 < η := by dsimp [η]; linarith
  have hθ0 : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ < 1 := by dsimp [θ]; apply (div_lt_one (by linarith)).mpr; linarith
  have hθη : θ / (1 - θ) = η := by dsimp [θ, η]; field_simp; ring
  refine ⟨R₀, 1 + (8 + 8 * C ^ 2) ^ η, (2 * C + 1) * η, hR₀, by positivity,
    mul_pos (by linarith) hη, ?_⟩
  intro m a ha y hQ R hR u hu hu1 φ hs
  let _ := pointMeasure_isProbability hγ ha y
  let μ := pointMeasure γ a y
  let r := 2 * pointSobolevKappa Q
  let H := C * Real.exp (C * R ^ 2) * R
  let D := 8 + 8 * H ^ 2
  let E := ∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂μ
  let L := ∫ x, |φ x| ∂μ
  let N := ∫ x, |φ x| ^ r ∂μ
  have hr : 2 < r := by dsimp [r]; linarith [pointSobolevKappa_gt_one hQ0]
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
    calc
      _ = pointSobolevKappa Q / (2 * pointSobolevKappa Q - 1) := by
        dsimp [r]
        have hk := pointSobolevKappa_gt_one hQ0
        field_simp [show 2 * pointSobolevKappa Q - 1 ≠ 0 by linarith]
        <;> ring
      _ = _ := pointSobolev_interpolation_exponent hQ0
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

end RepulsiveCoulomb
