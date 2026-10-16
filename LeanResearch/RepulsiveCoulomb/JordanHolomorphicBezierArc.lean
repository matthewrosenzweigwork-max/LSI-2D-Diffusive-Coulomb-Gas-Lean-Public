import LeanResearch.RepulsiveCoulomb.JordanBezierCorner
import LeanResearch.RepulsiveCoulomb.AnalyticArcSmoothExtension

/-! Actual global smooth representatives of the holomorphic quadratic corner
replacement, with the genuine endpoint velocities, regularity and embedding.
The retained radial tails are excluded by the proved quadratic formula.
Records-only draft, not admitted or compiled. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem euclideanBezierCorner_analyticAt (u v : ℂ) (t : ℝ) :
    AnalyticAt ℝ (euclideanBezierCorner u v) t := by
  have h₁ : AnalyticAt ℝ (fun s : ℝ => -((1 - s) ^ 2)) t :=
    ((analyticAt_const.sub analyticAt_id).pow 2).neg
  have h₂ : AnalyticAt ℝ (fun s : ℝ => s ^ 2) t := analyticAt_id.pow 2
  exact (h₁.smul analyticAt_const).add (h₂.smul analyticAt_const)

/-- A noncritical holomorphic image of the actual quadratic replacement has a
global smooth representative agreeing on a neighborhood of every parameter in
the closed interval. Actual endpoint derivatives are retained, not just image. -/
theorem exists_holomorphic_bezier_smooth_arc
    {H : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hH : AnalyticOnNhd ℂ H U) (hHreg : ∀ z ∈ U, deriv H z ≠ 0)
    (hHinj : InjOn H U) {u v : ℂ} (hu : u ≠ 0)
    (hc : v / u ∈ Complex.slitPlane)
    (hBU : MapsTo (euclideanBezierCorner u v) (Icc (0 : ℝ) 1) U) :
    ∃ η : ℝ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞)) η ∧
      (∀ t ∈ Icc (0 : ℝ) 1, η =ᶠ[𝓝 t] (H ∘ euclideanBezierCorner u v)) ∧
      InjOn η (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, deriv η t ≠ 0) ∧
      η 0 = H (-u) ∧ η 1 = H v ∧
      deriv η 0 = (2 : ℝ) • (deriv H (-u) * u) ∧
      deriv η 1 = (2 : ℝ) • (deriv H v * v) ∧
      η '' Icc (0 : ℝ) 1 = H '' (euclideanBezierCorner u v '' Icc (0 : ℝ) 1) := by
  have hA : AnalyticOnNhd ℝ (H ∘ euclideanBezierCorner u v) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ((hH _ (hBU ht)).restrictScalars (𝕜 := ℝ)).comp (euclideanBezierCorner_analyticAt u v t)
  have hD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      deriv (H ∘ euclideanBezierCorner u v) t =
        deriv H (euclideanBezierCorner u v t) * ((2 : ℝ) • euclideanCornerBlend u v t) := by
    exact (((hH _ (hBU ht)).differentiableAt.hasDerivAt).comp t
      (euclideanBezierCorner_hasDerivAt u v t)).deriv
  obtain ⟨η, hη, hagree⟩ := analytic_unitInterval_global_smooth_extension
    (H ∘ euclideanBezierCorner u v) hA
  have heq : EqOn η (H ∘ euclideanBezierCorner u v) (Icc (0 : ℝ) 1) :=
    fun t ht => (hagree t ht).self_of_nhds
  have hηD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      deriv η t = deriv H (euclideanBezierCorner u v t) *
        ((2 : ℝ) • euclideanCornerBlend u v t) :=
    (hagree t ht).deriv_eq.trans (hD t ht)
  refine ⟨η, hη, hagree, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    exact euclideanBezierCorner_injOn hu hc hs ht
      (hHinj (hBU hs) (hBU ht) ((heq hs).symm.trans (hst.trans (heq ht))))
  · intro t ht
    rw [hηD t ht]
    exact mul_ne_zero (hHreg _ (hBU ht))
      (smul_ne_zero (by norm_num) (euclideanCornerBlend_ne_zero hu hc ht))
  · simpa only [Function.comp_apply, euclideanBezierCorner_zero] using heq (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
  · simpa only [Function.comp_apply, euclideanBezierCorner_one] using heq (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  · rw [hηD 0 (by norm_num)]
    simp only [euclideanBezierCorner_zero, euclideanCornerBlend_zero, mul_smul_comm]
  · rw [hηD 1 (by norm_num)]
    simp only [euclideanBezierCorner_one, euclideanCornerBlend_one, mul_smul_comm]
  · rw [heq.image_eq, image_comp]

/-- A literal local radial description of the retained boundary forces the
open quadratic replacement to miss the whole retained set. -/
theorem holomorphic_bezier_open_disjoint_retained
    {H : ℂ → ℂ} {U S : Set ℂ} {u v : ℂ} (hu : u ≠ 0)
    (hc : v / u ∈ Complex.slitPlane)
    (hBU : MapsTo (euclideanBezierCorner u v) (Icc (0 : ℝ) 1) U)
    (hret : ∀ z ∈ U, H z ∈ S →
      (∃ c : ℝ, 1 ≤ c ∧ z = -c • u) ∨ (∃ c : ℝ, 1 ≤ c ∧ z = c • v)) :
    Disjoint ((H ∘ euclideanBezierCorner u v) '' Ioo (0 : ℝ) 1) S := by
  apply Set.disjoint_left.mpr
  rintro z ⟨t, ht, rfl⟩ hS
  rcases hret (euclideanBezierCorner u v t) (hBU (Ioo_subset_Icc_self ht)) hS with hi | ho
  · obtain ⟨c, hc1, he⟩ := hi
    exact euclideanBezierCorner_ne_incoming_tail hu hc ⟨ht.1, ht.2.le⟩ hc1 he
  · obtain ⟨c, hc1, he⟩ := ho
    exact euclideanBezierCorner_ne_outgoing_tail hu hc ⟨ht.1.le, ht.2⟩ hc1 he

/-- Consequently the closed replacement meets the retained boundary only at
its two actual attachment points. -/
theorem holomorphic_bezier_inter_retained_subset_endpoints
    {H : ℂ → ℂ} {U S : Set ℂ} {u v : ℂ} (hu : u ≠ 0)
    (hc : v / u ∈ Complex.slitPlane)
    (hBU : MapsTo (euclideanBezierCorner u v) (Icc (0 : ℝ) 1) U)
    (hret : ∀ z ∈ U, H z ∈ S →
      (∃ c : ℝ, 1 ≤ c ∧ z = -c • u) ∨ (∃ c : ℝ, 1 ≤ c ∧ z = c • v)) :
    (H ∘ euclideanBezierCorner u v) '' Icc (0 : ℝ) 1 ∩ S ⊆ {H (-u), H v} := by
  rintro z ⟨⟨t, ht, rfl⟩, hS⟩
  by_cases ht0 : t = 0
  · simp [ht0]
  by_cases ht1 : t = 1
  · simp [ht1]
  have hti : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  exact ((Set.disjoint_left.mp (holomorphic_bezier_open_disjoint_retained hu hc hBU hret))
    ⟨t, hti, rfl⟩ hS).elim

end RepulsiveCoulomb
