import LeanResearch.RepulsiveCoulomb.JordanSmoothSupportedTurn
import LeanResearch.RepulsiveCoulomb.PlaneJordanSeparation
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Relate a supporting-line turn calculation to the actual bounded side.
The region is an actual bounded open set with the actual curve as its frontier;
compactness and Fermat's theorem force its whole interior to the strict
supporting half-plane. This supplies a genuine inside-side witness at a support
point. It does not yet prove global left/right transport around a piecewise loop.
Records-only phase-four candidate. -/
noncomputable section
open Set
open scoped Topology
namespace RepulsiveCoulomb

private theorem complex_im_no_local_min (z : ℂ) : ¬ IsLocalMin Complex.im z := by
  intro hmin
  have hd : HasFDerivAt Complex.im Complex.imCLM z := Complex.imCLM.hasFDerivAt
  have hz : Complex.imCLM = 0 := hd.fderiv.symm.trans hmin.fderiv_eq_zero
  have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) hz
  norm_num at h

/-- A linear functional attains its minimum over a compact closed region at
its actual frontier, since it has no local minimum in the plane. -/
theorem bounded_open_region_frontier_support {U : Set ℂ} (hU : IsOpen U)
    (hK : IsCompact (closure U)) {c : ℝ}
    (hfront : ∀ z ∈ frontier U, c ≤ z.im) :
    ∀ z ∈ closure U, c ≤ z.im := by
  intro z hz
  obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn ⟨z, hz⟩ Complex.continuous_im.continuousOn
  have hwfront : w ∈ frontier U := by
    by_contra hn
    have hwU : w ∈ U := by
      by_contra hwN
      apply hn
      rw [frontier, hU.interior_eq]
      exact ⟨hw, hwN⟩
    have hnhds : closure U ∈ 𝓝 w :=
      Filter.mem_of_superset (hU.mem_nhds hwU) subset_closure
    exact complex_im_no_local_min w (hmin.isLocalMin hnhds)
  exact (hfront w hwfront).trans (hmin hz)

/-- The actual interior lies strictly on the supporting side; equality cannot
occur at an interior point of an open planar region. -/
theorem bounded_open_region_strict_support {U : Set ℂ} (hU : IsOpen U)
    (hK : IsCompact (closure U)) {c : ℝ}
    (hfront : ∀ z ∈ frontier U, c ≤ z.im) :
    ∀ z ∈ U, c < z.im := by
  have hclosure := bounded_open_region_frontier_support hU hK hfront
  intro z hz
  have hle := hclosure z (subset_closure hz)
  rcases hle.eq_or_lt with heq | hlt
  · have hmin : IsMinOn Complex.im U z := by
      intro w hw
      rw [← heq]
      exact hclosure w (subset_closure hw)
    exact (complex_im_no_local_min z (hmin.isLocalMin (hU.mem_nhds hz))).elim
  · exact hlt

/-- Applied to the actual bounded Jordan region, an upper supporting line of
the actual boundary places every interior point strictly above that line. -/
theorem bounded_jordan_region_above_support {γ : ℝ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hK : IsCompact (closure U))
    (hfront : frontier U = γ '' Icc (0 : ℝ) 1)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (γ t - γ 0).im) :
    ∀ z ∈ U, (γ 0).im < z.im := by
  apply bounded_open_region_strict_support hU hK
  intro z hz
  rw [hfront] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  exact sub_nonneg.mp (by simpa only [Complex.sub_im] using hsupport t ht)

/-- The positive total-turn calculation has a matching ACTUAL inside-side
witness: the bounded Jordan region lies left of the normalized supporting
tangent. This asserts the side through the actual region, not a chosen sign. -/
theorem supported_loop_turn_and_actual_inside
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hregular : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    (hbase : deriv γ 0 = 1)
    (hsupport : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ (γ r - γ 0).im)
    {θ : Icc (0 : ℝ) 1 → ℝ} (hθ : Continuous θ)
    (hθlift : ∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
      deriv γ t / (‖deriv γ t‖ : ℂ))
    {U : Set ℂ} (hU : IsOpen U) (hK : IsCompact (closure U))
    (hfront : frontier U = γ '' Icc (0 : ℝ) 1) :
    θ 1 - θ 0 = 2 * Real.pi ∧ ∀ z ∈ U, 0 < ((z - γ 0) / deriv γ 0).im := by
  refine ⟨regular_simple_supported_loop_total_turn hγ hp hinj hregular hbase hsupport hθ hθlift, ?_⟩
  intro z hz
  rw [hbase, div_one, Complex.sub_im]
  exact sub_pos.mpr (bounded_jordan_region_above_support hU hK hfront hsupport z hz)

end RepulsiveCoulomb
