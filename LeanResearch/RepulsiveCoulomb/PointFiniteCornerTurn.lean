module

public import LeanResearch.RepulsiveCoulomb.PointFiniteRadialCornerGeometry
public import LeanResearch.RepulsiveCoulomb.PointRadialCornerNormalization
public import Mathlib.Analysis.Calculus.TangentCone.Real

@[expose] public section

/-! The full normalized sector geometry determines the principal turn of
actual adjacent original tangents. Equality only on the actual closed collars
suffices by one-sided derivative uniqueness; no fictitious full-neighborhood
extension equality is imposed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

private theorem deriv_eq_on_closed_collar {f g : ℝ → ℂ} {a b t : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b) (hf : DifferentiableAt ℝ f t)
    (hg : DifferentiableAt ℝ g t) (heq : EqOn f g (Icc a b)) :
    deriv f t = deriv g t := by
  have hud := uniqueDiffOn_Icc hab t ht
  calc
    deriv f t = derivWithin f (Icc a b) t := (hf.hasDerivAt.hasDerivWithinAt.derivWithin hud).symm
    _ = derivWithin g (Icc a b) t := derivWithin_congr heq (heq ht)
    _ = deriv g t := hg.hasDerivAt.hasDerivWithinAt.derivWithin hud

/-- The signed Euclidean corner is π minus the full inside Euclidean sector,
including reflex sectors. Its cone counterpart is obtained by subtracting
the independently proved boundary-atom correction κθ/2. -/
theorem PointFiniteRadialCornerAt.principal_turn_eq
    {f : ℕ → ℝ → ℂ} {n k : ℕ} {θ : ℝ} (D : PointFiniteRadialCornerAt f n k θ)
    (hf : ∀ i ≤ n, ContDiff ℝ 1 (f i)) :
    Complex.arg (deriv (f k) 0 / deriv (f (D.order n)) 1) = Real.pi - θ := by
  have hk : k ≤ n := by simpa only [D.order_zero] using D.order_le 0 (Nat.zero_le n)
  have hδ1 : D.width < 1 := by linarith [D.width_half]
  have h0target : (0 : ℂ) ∈ D.chart.target := D.origin ▸ D.chart.mapsTo D.source
  let H : ℂ → ℂ := D.chart.symm
  let L : ℝ → ℂ := fun u => H (pointRadialSectorPoint (D.leftRate * u) 0)
  let R : ℝ → ℂ := fun u => H (pointRadialSectorPoint (D.rightRate * (1 - u)) θ)
  have hLin : HasDerivAt (fun u : ℝ => pointRadialSectorPoint (D.leftRate * u) 0)
      (D.leftRate : ℂ) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).const_mul D.leftRate).ofReal_comp using 1 <;>
      simp [pointRadialSectorPoint]
  have hRin : HasDerivAt (fun u : ℝ => pointRadialSectorPoint (D.rightRate * (1 - u)) θ)
      ((-D.rightRate : ℂ) * (Circle.exp θ : ℂ)) 1 := by
    convert! (((hasDerivAt_id (1 : ℝ)).const_sub 1).const_mul D.rightRate).ofReal_comp.mul_const
      (Circle.exp θ : ℂ) using 1 <;> simp [pointRadialSectorPoint]
  have hHL : HasDerivAt H (deriv H 0) (pointRadialSectorPoint (D.leftRate * (0 : ℝ)) 0) := by
    simpa only [mul_zero, pointRadialSectorPoint_zero] using
      (D.inverse_analytic 0 h0target).differentiableAt.hasDerivAt
  have hHR : HasDerivAt H (deriv H 0) (pointRadialSectorPoint (D.rightRate * (1 - (1 : ℝ))) θ) := by
    simpa only [sub_self, mul_zero, pointRadialSectorPoint_zero] using
      (D.inverse_analytic 0 h0target).differentiableAt.hasDerivAt
  have hLD : HasDerivAt L (deriv H 0 * (D.leftRate : ℂ)) 0 :=
    hHL.comp (h := fun u : ℝ => pointRadialSectorPoint (D.leftRate * u) 0) 0 hLin
  have hRD : HasDerivAt R (deriv H 0 * ((-D.rightRate : ℂ) * (Circle.exp θ : ℂ))) 1 :=
    hHR.comp (h := fun u : ℝ => pointRadialSectorPoint (D.rightRate * (1 - u)) θ) 1 hRin
  have hLeq : EqOn (f k) L (Icc (0 : ℝ) D.width) := by
    intro u hu
    exact D.left_collar u ⟨hu.1, hu.2.trans hδ1.le⟩ hu.2
  have hReq : EqOn (f (D.order n)) R (Icc (1 - D.width) 1) := by
    intro u hu
    exact D.right_collar u ⟨by linarith [hu.1], hu.2⟩ hu.1
  have hleft : deriv (f k) 0 = deriv H 0 * (D.leftRate : ℂ) :=
    (deriv_eq_on_closed_collar D.width_pos ⟨le_rfl, D.width_pos.le⟩
      ((hf k hk).differentiable (by norm_num) 0) hLD.differentiableAt hLeq).trans hLD.deriv
  have hright : deriv (f (D.order n)) 1 =
      -(deriv H 0 * ((D.rightRate : ℂ) * (Circle.exp θ : ℂ))) := by
    have heq := (deriv_eq_on_closed_collar (show 1 - D.width < (1 : ℝ) by linarith [D.width_pos])
      ⟨by linarith [D.width_pos], le_rfl⟩
      ((hf _ (D.order_le n le_rfl)).differentiable (by norm_num) 1) hRD.differentiableAt hReq).trans hRD.deriv
    rw [heq]
    push_cast
    ring
  rw [hleft, hright]
  exact holomorphic_radial_corner_principal_turn D.inverse_regular D.angle_pos D.angle_lt
    D.leftRate_pos D.rightRate_pos

end RepulsiveCoulomb
