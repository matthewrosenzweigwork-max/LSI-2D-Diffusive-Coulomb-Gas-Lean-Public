module

public import LeanResearch.RepulsiveCoulomb.PointScoreLaplacian
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section

/-! Actual directional derivatives and divergence of the physical score. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointScore_inner_eq_neg_fderiv {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ}
    (hz : z ∉ pointPunctures a y) (v : ℂ) :
    inner ℝ (pointScore γ a y z) v = -fderiv ℝ (pointLogWeight γ a y) z v := by
  rw [(hasFDerivAt_pointLogWeight γ ha y hz).fderiv]
  change inner ℝ (pointScore γ a y z) v = -inner ℝ (-pointScore γ a y z) v
  simp

theorem pointScore_component_hasFDerivAt {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ}
    (hz : z ∉ pointPunctures a y) (v : ℂ) :
    HasFDerivAt (fun x => inner ℝ (pointScore γ a y x) v)
      (-(fderiv ℝ (fderiv ℝ (pointLogWeight γ a y)) z).flip v) z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (pointLogWeight γ a y)) z :=
    ((pointLogWeight_contDiffAt_two γ ha y hz).fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hv := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v z)
  have he : (fun x => inner ℝ (pointScore γ a y x) v) =ᶠ[𝓝 z]
      (fun x => -fderiv ℝ (pointLogWeight γ a y) x v) := by
    filter_upwards [(pointDomain a y).isOpen.mem_nhds hz] with x hx
    exact pointScore_inner_eq_neg_fderiv γ ha y hx v
  simpa only [ContinuousLinearMap.comp_zero, zero_add] using hv.neg.congr_of_eventuallyEq he

theorem pointScore_divergence {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ}
    (hz : z ∉ pointPunctures a y) :
    fderiv ℝ (fun x => inner ℝ (pointScore γ a y x) (1 : ℂ)) z 1 +
      fderiv ℝ (fun x => inner ℝ (pointScore γ a y x) Complex.I) z Complex.I = 2 * γ := by
  rw [(pointScore_component_hasFDerivAt γ ha y hz 1).fderiv,
    (pointScore_component_hasFDerivAt γ ha y hz Complex.I).fderiv]
  have h := pointLogWeight_laplacian γ ha y hz
  rw [laplacian_eq_iteratedFDeriv_complexPlane] at h
  simp only [iteratedFDeriv_two_apply] at h
  change fderiv ℝ (fderiv ℝ (pointLogWeight γ a y)) z 1 1 +
    fderiv ℝ (fderiv ℝ (pointLogWeight γ a y)) z Complex.I Complex.I = -2 * γ at h
  change -fderiv ℝ (fderiv ℝ (pointLogWeight γ a y)) z 1 1 +
    -fderiv ℝ (fderiv ℝ (pointLogWeight γ a y)) z Complex.I Complex.I = 2 * γ
  linarith

theorem pointScore_component_contDiffAt_one {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ}
    (hz : z ∉ pointPunctures a y) (v : ℂ) :
    ContDiffAt ℝ 1 (fun x => inner ℝ (pointScore γ a y x) v) z := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ (pointLogWeight γ a y)) z :=
    (pointLogWeight_contDiffAt_two γ ha y hz).fderiv_right (m := 1) (by norm_num)
  have hv : ContDiffAt ℝ 1 (fun x => fderiv ℝ (pointLogWeight γ a y) x v) z :=
    hd.clm_apply contDiffAt_const
  apply hv.neg.congr_of_eventuallyEq
  filter_upwards [(pointDomain a y).isOpen.mem_nhds hz] with x hx
  exact pointScore_inner_eq_neg_fderiv γ ha y hx v

end RepulsiveCoulomb
