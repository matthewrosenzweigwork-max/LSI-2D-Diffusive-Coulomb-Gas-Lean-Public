module

public import LeanResearch.RepulsiveCoulomb.CoulombRelativePoincare
public import LeanResearch.RepulsiveCoulomb.CoulombRelativeSymmetry

@[expose] public section

/-! A genuine conditional swap estimate; no global spectral gap is assumed. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology
namespace RepulsiveCoulomb

theorem measurePreserving_difference_le_variance {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (e : α ≃ᵐ α)
    (he : MeasurePreserving e μ μ) {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, (f x - f (e x)) ^ 2 ∂μ) ≤ 4 * variance f μ := by
  let m := ∫ x, f x ∂μ
  have hc : Integrable (fun x => (f x - m) ^ 2) μ :=
    (hf.sub (memLp_const m)).integrable_sq
  have hce : Integrable (fun x => (f (e x) - m) ^ 2) μ :=
    he.integrable_comp_of_integrable hc
  have hd : Integrable (fun x => (f x - f (e x)) ^ 2) μ :=
    (hf.sub (hf.comp_measurePreserving he)).integrable_sq
  rw [variance_eq_integral hf.aestronglyMeasurable.aemeasurable]
  change _ ≤ 4 * ∫ x, (f x - m) ^ 2 ∂μ
  calc
    _ ≤ ∫ x, 2 * ((f x - m) ^ 2 + (f (e x) - m) ^ 2) ∂μ :=
      integral_mono hd ((hc.add hce).const_mul 2) (fun x => by
        nlinarith [sq_nonneg ((f x - m) + (f (e x) - m))])
    _ = _ := by
      rw [integral_const_mul, integral_add hc hce, he.integral_comp' (fun x => (f x - m) ^ 2)]
      ring

theorem coulomb_relative_core_swap_bound {β : ℝ} (hβ : 0 < β) :
    ∃ P : ℝ, 0 < P ∧ ∀ (N : ℕ) (c : ℂ) (y : CoulombConfig N)
      (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤),
    (∫ u, (φ (coulombRelativeInsert c u y) - φ (coulombRelativeInsert c (-u) y)) ^ 2
      ∂coulombRelativeKernel N β hβ (c, y)) ≤
      (2 * P) * (∫ u, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) 0 -
        gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) (Fin.succ 0)‖ ^ 2
          ∂coulombRelativeKernel N β hβ (c, y)) := by
  obtain ⟨P, hP, hp⟩ := coulomb_relative_core_uniform_poincare hβ
  refine ⟨P, hP, ?_⟩
  intro N c y φ
  let ψ := coulombRelativeCore (coulombRelativeExponents N β) φ c y
  have hm : MemLp (ψ : ℂ → ℝ) 2 (coulombRelativeKernel N β hβ (c, y)) :=
    ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport
  let e : ℂ ≃ᵐ ℂ := (LinearIsometryEquiv.neg ℝ : ℂ ≃ₗᵢ[ℝ] ℂ).toMeasurableEquiv
  have he : MeasurePreserving e (coulombRelativeKernel N β hβ (c, y))
      (coulombRelativeKernel N β hβ (c, y)) := coulombRelativeKernel_neg_measurePreserving hβ (c, y)
  have hs := measurePreserving_difference_le_variance (coulombRelativeKernel N β hβ (c, y)) e he hm
  have hpi := hp N c y φ
  change (∫ u, (φ (coulombRelativeInsert c u y) - φ (coulombRelativeInsert c (-u) y)) ^ 2
    ∂coulombRelativeKernel N β hβ (c, y)) ≤
    4 * variance (fun u => φ (coulombRelativeInsert c u y)) (coulombRelativeKernel N β hβ (c, y)) at hs
  calc
    _ ≤ _ := hs
    _ ≤ 4 * ((P / 2) * _) := mul_le_mul_of_nonneg_left hpi (by norm_num)
    _ = _ := by ring

end RepulsiveCoulomb

