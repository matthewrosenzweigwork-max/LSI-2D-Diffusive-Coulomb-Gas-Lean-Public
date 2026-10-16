module

public import LeanResearch.RepulsiveCoulomb.PointRadialCornerNormalization
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.Topology.Algebra.GroupWithZero

@[expose] public section

/-! The normalized radial inverse is the inverse of an actual rotated
partial-homeomorphism chart. Exact source/target, analytic maps and derivative
regularity survive, so the positive-orientation/region-side theorems can be
applied to the same actual physical corner. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def pointRotatedRadialChart (e : OpenPartialHomeomorph ℂ ℂ) (c : ℂ) (hc : c ≠ 0) :
    OpenPartialHomeomorph ℂ ℂ := e.trans (Homeomorph.mulLeft₀ c hc).toOpenPartialHomeomorph

@[simp] theorem pointRotatedRadialChart_apply (e : OpenPartialHomeomorph ℂ ℂ)
    (c : ℂ) (hc : c ≠ 0) (z : ℂ) : pointRotatedRadialChart e c hc z = c * e z := rfl

@[simp] theorem pointRotatedRadialChart_symm_apply (e : OpenPartialHomeomorph ℂ ℂ)
    (c : ℂ) (hc : c ≠ 0) (z : ℂ) : (pointRotatedRadialChart e c hc).symm z = e.symm (c⁻¹ * z) := rfl

@[simp] theorem pointRotatedRadialChart_source (e : OpenPartialHomeomorph ℂ ℂ)
    (c : ℂ) (hc : c ≠ 0) : (pointRotatedRadialChart e c hc).source = e.source := by
  simp [pointRotatedRadialChart, OpenPartialHomeomorph.trans_source]

@[simp] theorem pointRotatedRadialChart_target (e : OpenPartialHomeomorph ℂ ℂ)
    (c : ℂ) (hc : c ≠ 0) : (pointRotatedRadialChart e c hc).target =
      (fun z : ℂ => c⁻¹ * z) ⁻¹' e.target := by
  simp [pointRotatedRadialChart, OpenPartialHomeomorph.trans_target]

/-- Normalize a genuine local chart, rather than retaining only a free
holomorphic map. The selected rotation and both literal radial rates remain
visible in the conclusion. -/
theorem exists_normalized_actual_radial_chart (e : OpenPartialHomeomorph ℂ ℂ)
    {p : ℂ} (hp : p ∈ e.source) (hep : e p = 0)
    (he : ∀ z ∈ e.source, AnalyticAt ℂ e z)
    (hinv : AnalyticOnNhd ℂ e.symm e.target) (hinvn : deriv e.symm 0 ≠ 0)
    {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hdistinct : ¬ ∃ b : ℝ, 0 < b ∧ v = b • u) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧
      ∃ E : OpenPartialHomeomorph ℂ ℂ, E.source = e.source ∧ p ∈ E.source ∧ E p = 0 ∧
        (∀ z, E z = c * e z) ∧ (∀ z, E.symm z = e.symm (c⁻¹ * z)) ∧
        (∀ z ∈ E.source, AnalyticAt ℂ E z) ∧ AnalyticOnNhd ℂ E.symm E.target ∧
        deriv E.symm 0 ≠ 0 ∧
        (∀ t : ℝ, e.symm (t • u) = E.symm (pointRadialSectorPoint (‖u‖ * t) 0)) ∧
        (∀ t : ℝ, e.symm (t • v) = E.symm (pointRadialSectorPoint (‖v‖ * t) θ)) := by
  have h0t : (0 : ℂ) ∈ e.target := hep ▸ e.mapsTo hp
  obtain ⟨c, hcn, θ, hθ0, hθ2, Wn, hWn, hWn0, hWneq,
      Hn, hHn, hDn, _, _, hrep, hL, hR⟩ :=
    exists_normalized_holomorphic_radial_corner e.open_target h0t hinv hinvn
      e.symm.injOn hu hv hdistinct
  have hc : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hcn]; norm_num)
  let E := pointRotatedRadialChart e c hc
  have hsource : E.source = e.source := pointRotatedRadialChart_source e c hc
  have htarget : E.target = Wn := (pointRotatedRadialChart_target e c hc).trans hWneq.symm
  have hfun : (E.symm : ℂ → ℂ) = Hn := by
    funext z
    exact (pointRotatedRadialChart_symm_apply e c hc z).trans (hrep z).symm
  have hEA (z : ℂ) (hz : z ∈ E.source) : AnalyticAt ℂ E z := by
    rw [hsource] at hz
    exact analyticAt_const.mul (he z hz)
  refine ⟨c, hcn, θ, hθ0, hθ2, E, hsource, hsource.symm ▸ hp, ?_,
    (fun _ => rfl), (fun _ => rfl), hEA, ?_, ?_, ?_, ?_⟩
  · change c * e p = 0
    rw [hep, mul_zero]
  · rw [hfun, htarget]
    exact hHn
  · rw [hfun]
    exact hDn
  · intro t
    rw [hfun]
    exact hL t
  · intro t
    rw [hfun]
    exact hR t

end RepulsiveCoulomb
