import LeanResearch.RepulsiveCoulomb.PointRadialCornerWinding
import LeanResearch.RepulsiveCoulomb.PointCornerLoopArgumentLift

/-! An actual radial-chart Jordan corner supplies its own continuous
boundary-point argument lift and its full side-sector increment. The endpoint
extension and nonvanishing lift are constructed; no angle/flux certificate is
an input. This includes reflex Euclidean sectors and arbitrary cone exponents. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- Construct the boundary-atom point-angle and prove its full sector value
from the actual Jordan outside and actual holomorphic radial collars. -/
theorem exists_radial_corner_boundary_argument
    {W : Set ℂ} (hW : IsOpen W) (hW0 : (0 : ℂ) ∈ W)
    {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H W) (hD : deriv H 0 ≠ 0)
    {θ φ : ℝ} (hθ : 0 < θ) (hθφ : θ < φ) (hφ2 : φ < 2 * Real.pi)
    (γ : Icc (0 : ℝ) 1 → ℂ) (hγ : Continuous γ) (hclose : γ 0 = γ 1)
    (hinj : InjOn γ {t : Icc (0 : ℝ) 1 | t.1 < 1})
    {U V : Set ℂ} (hK : IsCompact (closure U)) (hV : IsOpen V) (hVc : IsConnected V)
    (hcover : U ∪ V = (range γ)ᶜ)
    (hout : ∀ᶠ ε in 𝓝[>] (0 : ℝ), H (pointRadialSectorPoint ε φ) ∈ V)
    {l r cL cR : ℝ} (hl : 0 < l) (hlr : l < r) (hr : r < 1)
    (hcL : 0 < cL) (hcR : 0 < cR)
    (hleft : ∀ t : Icc (0 : ℝ) 1, t.1 ≤ l →
      γ t = H (pointRadialSectorPoint (cL * t.1) 0))
    (hright : ∀ t : Icc (0 : ℝ) 1, r ≤ t.1 →
      γ t = H (pointRadialSectorPoint (cR * (1 - t.1)) θ)) :
    ∃ ψ : Icc (0 : ℝ) 1 → ℝ, Continuous ψ ∧
      (∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
        Complex.exp ((ψ t : ℂ) * Complex.I) = (γ t - H 0) / (‖γ t - H 0‖ : ℂ)) ∧
      ψ 1 - ψ 0 = θ := by
  let L : ℝ → ℂ := fun u => H (pointRadialSectorPoint (cL * u) 0)
  let R : ℝ → ℂ := fun u => H (pointRadialSectorPoint (cR * (1 - u)) θ)
  have hLin : HasDerivAt (fun u : ℝ => pointRadialSectorPoint (cL * u) 0) (cL : ℂ) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).const_mul cL).ofReal_comp using 1 <;>
      simp [pointRadialSectorPoint]
  have hRin : HasDerivAt (fun u : ℝ => pointRadialSectorPoint (cR * (1 - u)) θ)
      ((-cR : ℂ) * (Circle.exp θ : ℂ)) 1 := by
    convert! (((hasDerivAt_id (1 : ℝ)).const_sub 1).const_mul cR).ofReal_comp.mul_const
      (Circle.exp θ : ℂ) using 1 <;>
      simp [pointRadialSectorPoint]
  have hHL : HasDerivAt H (deriv H 0) (pointRadialSectorPoint (cL * (0 : ℝ)) 0) := by
    simpa only [mul_zero, pointRadialSectorPoint_zero] using (hH 0 hW0).differentiableAt.hasDerivAt
  have hHR : HasDerivAt H (deriv H 0) (pointRadialSectorPoint (cR * (1 - (1 : ℝ))) θ) := by
    simpa only [sub_self, mul_zero, pointRadialSectorPoint_zero] using
      (hH 0 hW0).differentiableAt.hasDerivAt
  have hLD : HasDerivAt L (deriv H 0 * (cL : ℂ)) 0 :=
    hHL.comp (h := fun u : ℝ => pointRadialSectorPoint (cL * u) 0) 0 hLin
  have hRD : HasDerivAt R (deriv H 0 * ((-cR : ℂ) * (Circle.exp θ : ℂ))) 1 := hHR.comp 1 hRin
  have hLn : deriv L 0 ≠ 0 := by
    rw [hLD.deriv]
    exact mul_ne_zero hD (Complex.ofReal_ne_zero.mpr hcL.ne')
  have hRn : deriv R 1 ≠ 0 := by
    rw [hRD.deriv]
    exact mul_ne_zero hD (mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hcR.ne'))
      (Circle.coe_ne_zero _))
  have hγ0 : γ 0 = H 0 := by
    simpa [pointRadialSectorPoint] using
      hleft 0 (show (0 : ℝ) ≤ l from hl.le)
  have havoid (t : Icc (0 : ℝ) 1) (ht : t.1 ∈ Ioo (0 : ℝ) 1) : γ t ≠ γ 0 := by
    intro heq
    have he : t = 0 := hinj ht.2 (by norm_num) heq
    exact ht.1.ne' (congrArg Subtype.val he)
  obtain ⟨ψ, hψ, hlift⟩ := exists_corner_loop_point_argument_of_endpoint_germs
    γ hγ hclose havoid hl hlr hr L R hLD.differentiableAt hRD.differentiableAt hLn hRn
    hleft hright
  have hψlift : ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ t : ℂ) * Complex.I) = (γ t - H 0) / (‖γ t - H 0‖ : ℂ) := by
    intro t ht
    simpa only [hγ0] using hlift t ht
  exact ⟨ψ, hψ, hψlift, radial_corner_boundary_argument_eq_sector hW hW0 hH hD
    hθ hθφ hφ2 γ hγ hclose hinj hK hV hVc hcover hout hl hlr hr hcL hcR hleft hright
    ψ hψ hψlift⟩

end RepulsiveCoulomb
