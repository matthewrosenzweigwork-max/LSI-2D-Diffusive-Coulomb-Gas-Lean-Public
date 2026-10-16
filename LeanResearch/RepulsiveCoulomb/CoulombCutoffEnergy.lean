import LeanResearch.RepulsiveCoulomb.CoulombCutoffCore

/-! Uniform physical first-order bounds for a fixed compact cutoff. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RepulsiveCoulomb

theorem coulomb_testFunction_c1_bound {N : ℕ}
    (η : TestFunction (coulombDomain N) ℝ ⊤) :
    ∃ B : ℝ, 0 < B ∧ ∀ z, |η z| ≤ B ∧ ‖gradient (η : CoulombConfig N → ℝ) z‖ ≤ B := by
  let f : CoulombConfig N → ℝ := fun z => |η z| + ‖gradient (η : CoulombConfig N → ℝ) z‖
  have hc : Continuous f := η.continuous.abs.add (TauCeti.continuous_gradient_testFunction η).norm
  have hs : HasCompactSupport f := by
    convert! η.hasCompactSupport.norm.add (TauCeti.hasCompactSupport_gradient_testFunction η).norm using 1 <;>
      simp only [f, Real.norm_eq_abs, Pi.add_apply]
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro z
  have hf0 : 0 ≤ f z := by dsimp [f]; positivity
  have hb : f z ≤ |B| + 1 := by
    by_cases hz : z ∈ tsupport f
    · have h := hB z hz
      rw [Real.norm_eq_abs, abs_of_nonneg hf0] at h
      linarith [le_abs_self B]
    · rw [image_eq_zero_of_notMem_tsupport hz]
      positivity
  dsimp only [f] at hb
  constructor <;> linarith [abs_nonneg (η z), norm_nonneg (gradient (η : CoulombConfig N → ℝ) z)]

theorem coulombLocalizedCore_h1_pointwise_bound {N : ℕ}
    (η : TestFunction (coulombDomain N) ℝ ⊤) (U : Opens (CoulombConfig N))
    (hηU : tsupport (η : CoulombConfig N → ℝ) ⊆ U)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) {B : ℝ}
    (hB : ∀ z, |η z| ≤ B ∧ ‖gradient (η : CoulombConfig N → ℝ) z‖ ≤ B)
    (z : CoulombConfig N) :
    (coulombLocalizedCore η U hηU φ z) ^ 2 +
      ‖gradient (coulombLocalizedCore η U hηU φ : CoulombConfig N → ℝ) z‖ ^ 2 ≤
        3 * B ^ 2 * ((φ z) ^ 2 + ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2) := by
  change (η z * φ z) ^ 2 + ‖gradient (fun x => η x * φ x) z‖ ^ 2 ≤ _
  have hp := coulomb_gradient_mul_sq_le
    (η.contDiff.differentiable (by simp) z) (φ.contDiff.differentiable (by simp) z)
  have hη : (η z) ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (η z)) (hB z).1 2
  have hgrad : ‖gradient (η : CoulombConfig N → ℝ) z‖ ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hB z).2 2
  have h0 := mul_le_mul_of_nonneg_right hη (sq_nonneg (φ z))
  have h1 := mul_le_mul_of_nonneg_right hη (sq_nonneg ‖gradient (φ : CoulombConfig N → ℝ) z‖)
  have h2 := mul_le_mul_of_nonneg_right hgrad (sq_nonneg (φ z))
  have h3 := mul_nonneg (sq_nonneg B) (sq_nonneg ‖gradient (φ : CoulombConfig N → ℝ) z‖)
  nlinarith

end RepulsiveCoulomb
