import LeanResearch.RepulsiveCoulomb.PointRadialSectorTopology
import LeanResearch.RepulsiveCoulomb.JordanConformalTurnTransport

/-! Explicit argument branches for the two radial legs viewed from an
exterior polar point. The interior angle may be reflex: only 0 < θ < 2π is
used. The two branches agree at the vertex, and their oriented V increment
tends to -θ as the exterior observer approaches that vertex. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

def pointExteriorRayFactor (ε r δ : ℝ) : ℂ :=
  (ε : ℂ) + (r : ℂ) * (Circle.exp (Real.pi - δ) : ℂ)

def pointExteriorRadialArgument (ε φ A r : ℝ) : ℝ :=
  Complex.arg (-(Circle.exp φ : ℂ)) + Complex.arg (pointExteriorRayFactor ε r (φ - A))

theorem circle_pi_sub_mem_slitPlane {δ : ℝ} (hδ0 : 0 < δ) (hδ2 : δ < 2 * Real.pi) :
    (Circle.exp (Real.pi - δ) : ℂ) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff_arg.mpr
  refine ⟨?_, Circle.coe_ne_zero _⟩
  rw [Circle.arg_exp (by linarith) (by linarith)]
  linarith

theorem positive_real_add_nonneg_real_mul_mem_slitPlane {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 ≤ r) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    (ε : ℂ) + (r : ℂ) * z ∈ Complex.slitPlane := by
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · rw [← hr0, Complex.ofReal_zero, zero_mul, add_zero]
    exact Complex.ofReal_mem_slitPlane.mpr hε
  · rcases Complex.mem_slitPlane_iff.mp hz with hre | him
    · apply Complex.mem_slitPlane_iff.mpr
      left
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      positivity
    · apply Complex.mem_slitPlane_iff.mpr
      right
      simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, zero_mul, zero_add, add_zero] using mul_ne_zero hrpos.ne' him

theorem pointExteriorRayFactor_mem_slitPlane {ε r δ : ℝ}
    (hε : 0 < ε) (hr : 0 ≤ r) (hδ0 : 0 < δ) (hδ2 : δ < 2 * Real.pi) :
    pointExteriorRayFactor ε r δ ∈ Complex.slitPlane :=
  positive_real_add_nonneg_real_mul_mem_slitPlane hε hr (circle_pi_sub_mem_slitPlane hδ0 hδ2)

/-- Exact physical factorization, with the same nonzero prefactor on both
legs. The radial arguments therefore match at their common vertex. -/
theorem pointExteriorRayFactor_identity (ε r φ A : ℝ) :
    pointRadialSectorPoint r A - pointRadialSectorPoint ε φ =
      (-(Circle.exp φ : ℂ)) * pointExteriorRayFactor ε r (φ - A) := by
  have he : (Circle.exp φ : ℂ) * (Circle.exp (Real.pi - (φ - A)) : ℂ) =
      -(Circle.exp A : ℂ) := by
    simp only [Circle.coe_exp]
    rw [← Complex.exp_add]
    have hx : (φ : ℂ) * Complex.I + ((Real.pi - (φ - A) : ℝ) : ℂ) * Complex.I =
        (Real.pi : ℂ) * Complex.I + (A : ℂ) * Complex.I := by push_cast; ring
    rw [hx, Complex.exp_add, Complex.exp_pi_mul_I, neg_one_mul]
  unfold pointRadialSectorPoint pointExteriorRayFactor
  linear_combination (r : ℂ) * he

theorem pointExteriorRadialArgument_continuousOn {ε φ A : ℝ}
    (hε : 0 < ε) (hδ0 : 0 < φ - A) (hδ2 : φ - A < 2 * Real.pi) :
    ContinuousOn (pointExteriorRadialArgument ε φ A) (Ici (0 : ℝ)) := by
  apply continuousOn_const.add
  apply Complex.continuousOn_arg.comp (by unfold pointExteriorRayFactor; fun_prop)
  intro r hr
  exact pointExteriorRayFactor_mem_slitPlane hε hr hδ0 hδ2

theorem pointExteriorRadialArgument_zero {ε : ℝ} (hε : 0 < ε) (φ A : ℝ) :
    pointExteriorRadialArgument ε φ A 0 = Complex.arg (-(Circle.exp φ : ℂ)) := by
  simp only [pointExteriorRadialArgument, pointExteriorRayFactor, Complex.ofReal_zero,
    zero_mul, add_zero, Complex.arg_ofReal_of_nonneg hε.le]

/-- A constructed real angle, not an angle supplied as a premise. -/
theorem pointExteriorRadialArgument_lift {ε r φ A : ℝ}
    (hε : 0 < ε) (hr : 0 ≤ r) (hδ0 : 0 < φ - A) (hδ2 : φ - A < 2 * Real.pi) :
    Complex.exp ((pointExteriorRadialArgument ε φ A r : ℂ) * Complex.I) =
      (pointRadialSectorPoint r A - pointRadialSectorPoint ε φ) /
        (‖pointRadialSectorPoint r A - pointRadialSectorPoint ε φ‖ : ℂ) := by
  have hD : -(Circle.exp φ : ℂ) ≠ 0 := neg_ne_zero.mpr (Circle.coe_ne_zero _)
  have hF : pointExteriorRayFactor ε r (φ - A) ≠ 0 :=
    Complex.slitPlane_ne_zero (pointExteriorRayFactor_mem_slitPlane hε hr hδ0 hδ2)
  have he : Circle.exp (pointExteriorRadialArgument ε φ A r) =
      euclideanDirection (-(Circle.exp φ : ℂ)) hD *
        euclideanDirection (pointExteriorRayFactor ε r (φ - A)) hF := by
    rw [pointExteriorRadialArgument, Circle.exp_add,
      ← euclideanDirection_arg _ hD, Circle.exp_arg,
      ← euclideanDirection_arg _ hF, Circle.exp_arg]
  rw [← euclideanDirection_mul _ _ hD hF] at he
  have hc := congrArg (fun z : Circle => (z : ℂ)) he
  simp only [euclideanDirection_coe, ← pointExteriorRayFactor_identity] at hc
  simpa only [Circle.coe_exp] using hc

theorem pointExteriorRayFactor_arg_limit {R δ : ℝ}
    (hR : 0 < R) (hδ0 : 0 < δ) (hδ2 : δ < 2 * Real.pi) :
    Tendsto (fun ε : ℝ => Complex.arg (pointExteriorRayFactor ε R δ)) (𝓝 0)
      (𝓝 (Real.pi - δ)) := by
  have harg : Complex.arg (pointExteriorRayFactor 0 R δ) = Real.pi - δ := by
    rw [pointExteriorRayFactor, Complex.ofReal_zero, zero_add, Complex.arg_real_mul _ hR,
      Circle.arg_exp (by linarith) (by linarith)]
  have hne : pointExteriorRayFactor 0 R δ ≠ 0 := by
    simp only [pointExteriorRayFactor, Complex.ofReal_zero, zero_add]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (Circle.coe_ne_zero _)
  have hslit : pointExteriorRayFactor 0 R δ ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff_arg.mpr ⟨by rw [harg]; linarith, hne⟩
  have hc : ContinuousAt (fun ε : ℝ => Complex.arg (pointExteriorRayFactor ε R δ)) 0 :=
    (Complex.continuousAt_arg hslit).comp (f := fun ε : ℝ => pointExteriorRayFactor ε R δ)
      (by unfold pointExteriorRayFactor; fun_prop)
  simpa only [harg] using hc.tendsto

/-- Incoming radius R at angle θ, followed by outgoing radius R at angle0,
viewed from angle φ in the exterior sector (θ,2π), has limiting increment
-θ. This includes θ > π and does not replace θ by its principal short angle. -/
theorem pointExteriorTwoRayArgument_limit {R θ φ : ℝ} (hR : 0 < R)
    (hθ0 : 0 < θ) (hθφ : θ < φ) (hφ2 : φ < 2 * Real.pi) :
    Tendsto (fun ε : ℝ => pointExteriorRadialArgument ε φ 0 R -
      pointExteriorRadialArgument ε φ θ R) (𝓝 0) (𝓝 (-θ)) := by
  have ho := pointExteriorRayFactor_arg_limit hR (lt_trans hθ0 hθφ) hφ2
  have hi := pointExteriorRayFactor_arg_limit hR (sub_pos.mpr hθφ)
    (show φ - θ < 2 * Real.pi by linarith)
  have he : (fun ε : ℝ => pointExteriorRadialArgument ε φ 0 R -
      pointExteriorRadialArgument ε φ θ R) =
      (fun ε : ℝ => Complex.arg (pointExteriorRayFactor ε R φ) -
        Complex.arg (pointExteriorRayFactor ε R (φ - θ))) := by
    funext ε
    simp only [pointExteriorRadialArgument, sub_zero]
    ring
  rw [he]
  convert ho.sub hi using 1 <;> congr 1 <;> ring

end RepulsiveCoulomb
