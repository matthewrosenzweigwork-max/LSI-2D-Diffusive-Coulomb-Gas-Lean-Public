module

public import LeanResearch.RepulsiveCoulomb.DifferentiablePlanarCircleHomotopy
public import LeanResearch.RepulsiveCoulomb.PointMetricMapJacobian

@[expose] public section

/-!
A signed-Jacobian bridge with a genuine topological orientation hypothesis.
`PositiveLocalCircleWindingAt` refers only to the actual image of actual
positively oriented small circles, never to a derivative or determinant.
Its construction from the future oriented surgery/developing atlas is NOT
asserted here. The a.e. theorem is conditional on that explicit hypothesis
and actual metric estimates. It makes no weak-derivative or Sobolev claim.
Records-only candidate: not compiled or accepted.
-/
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology
namespace RepulsiveCoulomb

/-- Genuine local topological orientation, phrased without derivatives: every
sufficiently small actual positive circle has an actual continuous argument
lift of its image relative to the image center, with increment `+2π`.
The existential lift makes this hypothesis nonvacuous. -/
def PositiveLocalCircleWindingAt (F : ℂ → ℂ) (z : ℂ) : Prop :=
  ∃ R > 0, ∀ r, 0 < r → r < R →
    ∃ θ : Icc (0 : ℝ) 1 → ℝ,
      PlanarArgumentLift (fun t => F (z + planarCircleVector r t) - F z) θ ∧
      θ 1 - θ 0 = 2 * Real.pi

/-- Positive lower stretch supplies genuine invertibility in dimension two. -/
theorem planarLinear_injective_of_lower (A : ℂ →L[ℝ] ℂ) {c : ℝ}
    (hc : 0 < c) (hlower : ∀ v, c * ‖v‖ ≤ ‖A v‖) : Function.Injective A := by
  intro u v huv
  have hzero : A (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have h := hlower (u - v)
  rw [hzero, norm_zero] at h
  have hn : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem planarLinear_bijective_of_lower (A : ℂ →L[ℝ] ℂ) {c : ℝ}
    (hc : 0 < c) (hlower : ∀ v, c * ‖v‖ ≤ ‖A v‖) : Function.Bijective A := by
  have hi := planarLinear_injective_of_lower A hc hlower
  exact ⟨hi, LinearMap.surjective_of_injective (f := A.toLinearMap) hi⟩

theorem planarLinear_det_ne_zero_of_lower (A : ℂ →L[ℝ] ℂ) {c : ℝ}
    (hc : 0 < c) (hlower : ∀ v, c * ‖v‖ ≤ ‖A v‖) : A.toLinearMap.det ≠ 0 := by
  have h := complex_realLinear_abs_det_lower A.toLinearMap hc.le hlower
  intro hz
  rw [hz, abs_zero] at h
  nlinarith [sq_pos_of_pos hc]

/-- Injectivity of a real-linear plane map yields the positive lower stretch
needed for the small-circle argument; this uses finite dimensionality only. -/
theorem planarLinear_exists_positive_lower (A : ℂ →L[ℝ] ℂ)
    (hA : Function.Injective A) : ∃ c > 0, ∀ v, c * ‖v‖ ≤ ‖A v‖ := by
  obtain ⟨K, hK, hanti⟩ := A.toLinearMap.injective_iff_antilipschitz.mp hA
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  refine ⟨(K : ℝ)⁻¹, inv_pos.mpr hKreal, fun v => ?_⟩
  have hb : ‖v‖ ≤ (K : ℝ) * ‖A v‖ := A.bound_of_antilipschitz hanti v
  have hd : ‖v‖ / (K : ℝ) ≤ ‖A v‖ :=
    (div_le_iff₀ hKreal).mpr (by simpa only [mul_comm] using hb)
  simpa only [div_eq_mul_inv, mul_comm] using hd

/-- Small-circle homotopy transfers genuine local positive winding to the
actual derivative ellipse, ruling out its negative-determinant branch. -/
theorem positiveLocalCircleWindingAt_det_pos_of_lower
    {F : ℂ → ℂ} (hcont : Continuous F) {z : ℂ} {A : ℂ →L[ℝ] ℂ}
    (hF : HasFDerivAt F A z) (horient : PositiveLocalCircleWindingAt F z)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ v, c * ‖v‖ ≤ ‖A v‖) :
    0 < A.toLinearMap.det := by
  obtain ⟨R, hR, hinc⟩ := hasFDerivAt_small_circle_argument_increment hcont hF hc hlower
  obtain ⟨S, hS, hpos⟩ := horient
  let r : ℝ := min R S / 2
  have hr : 0 < r := half_pos (lt_min hR hS)
  have hrR : r < R := (half_lt_self (lt_min hR hS)).trans_le (min_le_left _ _)
  have hrS : r < S := (half_lt_self (lt_min hR hS)).trans_le (min_le_right _ _)
  obtain ⟨θ, hθ, hθinc⟩ := hpos r hr hrS
  have hne (t : Icc (0 : ℝ) 1) : A (planarCircleVector r t) ≠ 0 := by
    apply norm_pos_iff.mp
    have h := hlower (planarCircleVector r t)
    rw [planarSignedCircleVector_norm hr.le] at h
    exact (mul_pos hc hr).trans_le h
  obtain ⟨ψ, hψ, hψlift⟩ := exists_interval_euclidean_angle_lift
    (A.continuous.comp (planarSignedCircleVector_continuous r 1)) hne
  have hψ' : PlanarArgumentLift (fun t => A (planarCircleVector r t)) ψ := ⟨hψ, hψlift⟩
  have hsame := hinc r hr hrR θ ψ hθ hψ'
  rcases lt_or_gt_of_ne (planarLinear_det_ne_zero_of_lower A hc hlower) with hn | hp
  · have hneg := planar_realLinear_circle_increment_neg A hn hr hψ'
    nlinarith [Real.pi_pos]
  · exact hp

/-- The desired differentiable orientation-preserving plane-map implication,
with orientation given by actual local circle winding and invertibility given
by injectivity of the genuine derivative. Global homeomorphism structure is
not needed for this local implication. -/
theorem positiveLocalCircleWindingAt_det_pos
    {F : ℂ → ℂ} (hcont : Continuous F) {z : ℂ} {A : ℂ →L[ℝ] ℂ}
    (hF : HasFDerivAt F A z) (horient : PositiveLocalCircleWindingAt F z)
    (hA : Function.Injective A) : 0 < A.toLinearMap.det := by
  obtain ⟨c, hc, hlower⟩ := planarLinear_exists_positive_lower A hA
  exact positiveLocalCircleWindingAt_det_pos_of_lower hcont hF horient hc hlower

/-- The metric hypotheses supply the lower stretch away from the finite atoms;
only the explicitly topological local orientation remains to be constructed. -/
theorem pointMetricMap_fderiv_det_pos {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {F : ℂ → ℂ} (hcont : Continuous F)
    {L : ℝ} (hL : 0 < L)
    (hlower : ∀ p z, (pointSmoothConformalEDist a y p z).toReal ≤ L * dist (F p) (F z))
    (hupper : ∀ p z, dist (F p) (F z) ≤ L * (pointSmoothConformalEDist a y p z).toReal)
    {z : ℂ} (hz : z ∉ pointPunctures a y) (hF : DifferentiableAt ℝ F z)
    (horient : PositiveLocalCircleWindingAt F z) :
    0 < (fderiv ℝ F z).toLinearMap.det := by
  exact positiveLocalCircleWindingAt_det_pos_of_lower hcont hF.hasFDerivAt horient
    (div_pos (pointConformalDensity_pos_off_punctures ha y hz) hL)
    (fun v => (pointMetricMap_fderiv_bounds ha y hL hlower hupper hF v).1)

/-- Genuine signed a.e. Jacobian comparison, conditional on actual metric
bounds and explicitly supplied positive local circle winding off the atoms.
The distortion exponent here is the accepted `L^4`; sharpening it to `L^2`
is a separate linear-algebra result and is not claimed by this module. -/
theorem pointMetricHomeomorph_ae_signed_jacobian_bounds {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (F : ℂ ≃ₜ ℂ) {L : ℝ} (hL : 1 ≤ L)
    (hmetric : ∀ p z,
      L⁻¹ * (pointSmoothConformalEDist a y p z).toReal ≤ ‖F p - F z‖ ∧
      ‖F p - F z‖ ≤ L * (pointSmoothConformalEDist a y p z).toReal)
    (horient : ∀ z, z ∉ pointPunctures a y → PositiveLocalCircleWindingAt F z) :
    ∀ᵐ z ∂volume, DifferentiableAt ℝ F z ∧
      0 < (fderiv ℝ F z).toLinearMap.det ∧
      rawPointWeight a y z / L ^ 2 ≤ (fderiv ℝ F z).toLinearMap.det ∧
      (fderiv ℝ F z).toLinearMap.det ≤ L ^ 2 * rawPointWeight a y z ∧
      ‖fderiv ℝ F z‖ ^ 2 ≤ L ^ 4 * (fderiv ℝ F z).toLinearMap.det := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hlower : ∀ p z, (pointSmoothConformalEDist a y p z).toReal ≤ L * dist (F p) (F z) := by
    intro p z
    have h := mul_le_mul_of_nonneg_left (hmetric p z).1 hLp.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hLp.ne', one_mul, dist_eq_norm] using h
  have hupper : ∀ p z, dist (F p) (F z) ≤ L * (pointSmoothConformalEDist a y p z).toReal := by
    intro p z
    simpa only [dist_eq_norm] using (hmetric p z).2
  have hnot : ∀ᵐ z : ℂ ∂volume, z ∉ pointPunctures a y := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using (pointPunctures_finite a y).measure_zero volume
  filter_upwards [pointMetricHomeomorph_ae_jacobian_bounds ha y F hL hmetric, hnot] with z hz hp
  have hdet := pointMetricMap_fderiv_det_pos ha y F.continuous hLp hlower hupper hp hz.1
    (horient z hp)
  refine ⟨hz.1, hdet, ?_⟩
  simpa only [abs_of_pos hdet] using hz.2

end RepulsiveCoulomb
