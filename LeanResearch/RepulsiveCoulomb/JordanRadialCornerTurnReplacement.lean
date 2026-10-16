import LeanResearch.RepulsiveCoulomb.JordanConformalTurnTransport
import LeanResearch.RepulsiveCoulomb.JordanBezierCorner

/-! The actual holomorphic quadratic rounding preserves the sum of the two
actual incident radial arc turns and their actual principal corner turn.
A single chart-derivative angle is constructed and its endpoint terms cancel.
This is a local turn-preservation theorem, not a global smoothing certificate.
Records-only candidate, not admitted or compiled. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def euclideanIncomingRadius (u : ℂ) (t : ℝ) : ℂ := (t - 1) • u

def euclideanOutgoingRadius (v : ℂ) (t : ℝ) : ℂ := t • v

@[simp] theorem euclideanIncomingRadius_deriv (u : ℂ) (t : ℝ) :
    deriv (euclideanIncomingRadius u) t = u := by
  change deriv (fun y : ℝ => (y - 1) • u) t = u
  have h := ((hasDerivAt_id t).sub_const 1).smul_const u
  simpa only [euclideanIncomingRadius, id_eq, one_smul] using h.deriv

@[simp] theorem euclideanOutgoingRadius_deriv (v : ℂ) (t : ℝ) :
    deriv (euclideanOutgoingRadius v) t = v := by
  change deriv (fun y : ℝ => y • v) t = v
  have h := (hasDerivAt_id t).smul_const v
  simpa only [euclideanOutgoingRadius, id_eq, one_smul] using h.deriv

private theorem constant_vector_argument (u : ℂ) (hu : u ≠ 0) :
    Complex.exp ((Complex.arg u : ℂ) * Complex.I) = u / (‖u‖ : ℂ) := by
  have h := Circle.exp_arg (euclideanDirection u hu)
  rw [euclideanDirection_arg] at h
  exact congrArg (fun z : Circle => (z : ℂ)) h

/-- Every actual tangent-angle lift on the three physical arcs obeys the
same exact turn-preservation equation, including the physical corner ratio. -/
theorem conformal_radial_corner_turn_replacement
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsSimplyConnected U) {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H U) (hG : ContinuousOn (deriv H) U)
    (hHreg : ∀ z ∈ U, deriv H z ≠ 0) {u v : ℂ} (hu : u ≠ 0)
    (hc : v / u ∈ Complex.slitPlane)
    (hLU : MapsTo (euclideanIncomingRadius u) (Icc (0 : ℝ) 1) U)
    (hRU : MapsTo (euclideanOutgoingRadius v) (Icc (0 : ℝ) 1) U)
    (hBU : MapsTo (euclideanBezierCorner u v) (Icc (0 : ℝ) 1) U)
    {ΘL ΘR ΘB : Icc (0 : ℝ) 1 → ℝ}
    (hΘL : Continuous ΘL) (hΘR : Continuous ΘR) (hΘB : Continuous ΘB)
    (hΘLl : ∀ t, Complex.exp ((ΘL t : ℂ) * Complex.I) =
      deriv (H ∘ euclideanIncomingRadius u) t / (‖deriv (H ∘ euclideanIncomingRadius u) t‖ : ℂ))
    (hΘRl : ∀ t, Complex.exp ((ΘR t : ℂ) * Complex.I) =
      deriv (H ∘ euclideanOutgoingRadius v) t / (‖deriv (H ∘ euclideanOutgoingRadius v) t‖ : ℂ))
    (hΘBl : ∀ t, Complex.exp ((ΘB t : ℂ) * Complex.I) =
      deriv (H ∘ euclideanBezierCorner u v) t / (‖deriv (H ∘ euclideanBezierCorner u v) t‖ : ℂ)) :
    ΘB 1 - ΘB 0 = (ΘL 1 - ΘL 0) + (ΘR 1 - ΘR 0) +
      Complex.arg (deriv (H ∘ euclideanOutgoingRadius v) 0 /
        deriv (H ∘ euclideanIncomingRadius u) 1) := by
  have hv : v ≠ 0 := by
    intro he
    exact Complex.slitPlane_ne_zero hc (by simp [he])
  have hL : ContDiff ℝ 1 (euclideanIncomingRadius u) := by
    unfold euclideanIncomingRadius
    fun_prop
  have hR : ContDiff ℝ 1 (euclideanOutgoingRadius v) := by
    unfold euclideanOutgoingRadius
    fun_prop
  have hB : ContDiff ℝ 1 (euclideanBezierCorner u v) :=
    (euclideanBezierCorner_contDiff u v).of_le (by simp)
  have hLreg : ∀ t ∈ Icc (0 : ℝ) 1, deriv (euclideanIncomingRadius u) t ≠ 0 := by
    intro t _
    simpa using hu
  have hRreg : ∀ t ∈ Icc (0 : ℝ) 1, deriv (euclideanOutgoingRadius v) t ≠ 0 := by
    intro t _
    simpa using hv
  have hBreg : ∀ t ∈ Icc (0 : ℝ) 1, deriv (euclideanBezierCorner u v) t ≠ 0 :=
    fun _ ht => euclideanBezierCorner_regular hu hc ht
  obtain ⟨θB, hθB, hθBl⟩ := exists_regular_edge_tangent_angle_lift hB hBreg
  have hBturn : θB 1 - θB 0 = Complex.arg (v / u) := by
    apply euclideanBezierCorner_total_turn hu hc hθB
    intro t
    apply Circle.ext
    exact hθBl t
  obtain ⟨ψ, _, hcorr⟩ := exists_conformal_arc_turn_endpoint_correction hU hUc hH hG hHreg
  have hCL := hcorr (euclideanIncomingRadius u) hL hLU hLreg
    (fun _ => Complex.arg u) ΘL continuous_const hΘL
    (fun t => by simpa only [euclideanIncomingRadius_deriv] using constant_vector_argument u hu) hΘLl
  have hCR := hcorr (euclideanOutgoingRadius v) hR hRU hRreg
    (fun _ => Complex.arg v) ΘR continuous_const hΘR
    (fun t => by simpa only [euclideanOutgoingRadius_deriv] using constant_vector_argument v hv) hΘRl
  have hCB := hcorr (euclideanBezierCorner u v) hB hBU hBreg θB ΘB hθB hΘB hθBl hΘBl
  have hnegU : -u ∈ U := by simpa [euclideanIncomingRadius] using hLU (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  have hzeroU : (0 : ℂ) ∈ U := by simpa [euclideanIncomingRadius] using hLU (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  have hvU : v ∈ U := by simpa [euclideanOutgoingRadius] using hRU (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  have hCL' : ΘL 1 - ΘL 0 = ψ ⟨0, hzeroU⟩ - ψ ⟨-u, hnegU⟩ := by
    simpa [euclideanIncomingRadius] using hCL
  have hCR' : ΘR 1 - ΘR 0 = ψ ⟨v, hvU⟩ - ψ ⟨0, hzeroU⟩ := by
    simpa [euclideanOutgoingRadius] using hCR
  have hCB' : (ΘB 1 - ΘB 0) - Complex.arg (v / u) = ψ ⟨v, hvU⟩ - ψ ⟨-u, hnegU⟩ := by
    simpa only [hBturn, euclideanBezierCorner_zero, euclideanBezierCorner_one] using hCB
  have hH0 : HasDerivAt H (deriv H 0) 0 :=
    ((hH 0 hzeroU).differentiableAt (hU.mem_nhds hzeroU)).hasDerivAt
  have hdL : deriv (H ∘ euclideanIncomingRadius u) 1 = deriv H 0 * u := by
    have hLi : HasDerivAt (euclideanIncomingRadius u) u 1 := by
      simpa only [euclideanIncomingRadius_deriv] using
        ((hL.differentiable (by norm_num)) 1).hasDerivAt
    have hHL : HasDerivAt H (deriv H 0) (euclideanIncomingRadius u 1) := by
      simpa [euclideanIncomingRadius] using hH0
    exact (hHL.comp 1 hLi).deriv
  have hdR : deriv (H ∘ euclideanOutgoingRadius v) 0 = deriv H 0 * v := by
    have hRi : HasDerivAt (euclideanOutgoingRadius v) v 0 := by
      simpa only [euclideanOutgoingRadius_deriv] using
        ((hR.differentiable (by norm_num)) 0).hasDerivAt
    have hHR : HasDerivAt H (deriv H 0) (euclideanOutgoingRadius v 0) := by
      simpa [euclideanOutgoingRadius] using hH0
    exact (hHR.comp 0 hRi).deriv
  rw [hdL, hdR, conformal_corner_principal_turn _ _ _ (hHreg 0 hzeroU)]
  linarith

end RepulsiveCoulomb
