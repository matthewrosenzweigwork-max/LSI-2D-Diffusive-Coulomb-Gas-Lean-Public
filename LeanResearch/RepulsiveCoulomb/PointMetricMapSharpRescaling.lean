import LeanResearch.RepulsiveCoulomb.PointRectifiableConformalMetric
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Exact positive output rescaling of a supplied surgery development

Source-only candidate, not compiled, staged or accepted. An actual continuous
open bijection D is packaged as a homeomorphism using its proved bijectivity;
its output is multiplied by the single positive factor sqrt(B). The asymmetric
bounds B^(-1) d <= dist(Dp,Dz) <= d then become symmetric sqrt(B) bounds.

The point-metric endpoint has B = 1 + (sum_j a_j)/2 literally and rewrites the
existing all-rectifiable-curve metric identification. The actual development D
and its hypotheses remain inputs; they are not existence certificates proved
here. This is the exact algebraic interface to the separate constructed
orientation and sharp signed analytic normalization.
-/

noncomputable section
open Set Metric
open scoped Topology BigOperators
namespace RepulsiveCoulomb

/-- Package the actual open bijection and apply one positive output scale. -/
def planarScaledOpenBijection (D : ℂ → ℂ) (hcont : Continuous D)
    (hopen : IsOpenMap D) (hbij : Function.Bijective D) (s : ℝ) (hs : 0 < s) : ℂ ≃ₜ ℂ :=
  ((Equiv.ofBijective D hbij).toHomeomorphOfContinuousOpen hcont hopen).trans
    (Homeomorph.mulLeft₀ (s : ℂ) (Complex.ofReal_ne_zero.mpr hs.ne'))

@[simp] theorem planarScaledOpenBijection_apply (D : ℂ → ℂ) (hcont : Continuous D)
    (hopen : IsOpenMap D) (hbij : Function.Bijective D) (s : ℝ) (hs : 0 < s) (z : ℂ) :
    planarScaledOpenBijection D hcont hopen hbij s hs z = (s : ℂ) * D z := rfl

theorem planarScaledOpenBijection_norm_sub (D : ℂ → ℂ) (hcont : Continuous D)
    (hopen : IsOpenMap D) (hbij : Function.Bijective D) (s : ℝ) (hs : 0 < s)
    (p z : ℂ) :
    ‖planarScaledOpenBijection D hcont hopen hbij s hs p -
      planarScaledOpenBijection D hcont hopen hbij s hs z‖ = s * dist (D p) (D z) := by
  rw [planarScaledOpenBijection_apply, planarScaledOpenBijection_apply, ← mul_sub,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, dist_eq_norm]

/-- The numerical identity needed at the lower bound uses B > 0, including
B = 1 in the zero-total-mass case. -/
theorem sqrt_mul_inv_eq_inv_sqrt_of_pos {B : ℝ} (hB : 0 < B) :
    Real.sqrt B * B⁻¹ = (Real.sqrt B)⁻¹ := by
  have hL : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  apply mul_left_cancel₀ hL.ne'
  calc
    Real.sqrt B * (Real.sqrt B * B⁻¹) = (Real.sqrt B) ^ 2 * B⁻¹ := by ring
    _ = 1 := by rw [Real.sq_sqrt hB.le, mul_inv_cancel₀ hB.ne']
    _ = Real.sqrt B * (Real.sqrt B)⁻¹ := (mul_inv_cancel₀ hL.ne').symm

/-- Exact asymmetric-to-symmetric conversion for a supplied open bijection.
No metric-space instance is silently changed: d is the literal real distance
function used in both the premise and conclusion. -/
theorem exists_scaled_homeomorph_of_asymmetric_bounds
    (D : ℂ → ℂ) (hcont : Continuous D) (hopen : IsOpenMap D)
    (hbij : Function.Bijective D) (d : ℂ → ℂ → ℝ) {B : ℝ} (hB : 0 < B)
    (hmetric : ∀ p z, B⁻¹ * d p z ≤ dist (D p) (D z) ∧ dist (D p) (D z) ≤ d p z) :
    ∃ F : ℂ ≃ₜ ℂ, (∀ z, F z = (Real.sqrt B : ℂ) * D z) ∧
      ∀ p z, (Real.sqrt B)⁻¹ * d p z ≤ ‖F p - F z‖ ∧
        ‖F p - F z‖ ≤ Real.sqrt B * d p z := by
  have hL : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  let F := planarScaledOpenBijection D hcont hopen hbij (Real.sqrt B) hL
  refine ⟨F, fun _ => rfl, fun p z => ?_⟩
  have hn : ‖F p - F z‖ = Real.sqrt B * dist (D p) (D z) :=
    planarScaledOpenBijection_norm_sub D hcont hopen hbij (Real.sqrt B) hL p z
  rw [hn]
  constructor
  · have hl := mul_le_mul_of_nonneg_left (hmetric p z).1 hL.le
    simpa only [← mul_assoc, sqrt_mul_inv_eq_inv_sqrt_of_pos hB] using hl
  · exact mul_le_mul_of_nonneg_left (hmetric p z).2 hL.le

/-- A supplied surgery development with its original-point-metric asymmetric
bounds produces exactly the sharp symmetric literal rectifiable-metric
homeomorphism needed by
`pointRectifiableMetricHomeomorph_sharp_analytic_normalization_of_supplied_map`.
This theorem does not construct the surgery development. -/
theorem pointAsymmetricMetricMap_exists_sharp_metric_homeomorph_of_supplied_map
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (D : ℂ → ℂ) (hcont : Continuous D) (hopen : IsOpenMap D)
    (hbij : Function.Bijective D)
    (hmetric : ∀ p z,
      (1 + (∑ j, a j) / 2)⁻¹ * (pointSmoothConformalEDist a y p z).toReal ≤
        dist (D p) (D z) ∧
      dist (D p) (D z) ≤ (pointSmoothConformalEDist a y p z).toReal) :
    ∃ F : ℂ ≃ₜ ℂ,
      (∀ z, F z = (Real.sqrt (1 + (∑ j, a j) / 2) : ℂ) * D z) ∧
      ∀ p z,
        (Real.sqrt (1 + (∑ j, a j) / 2))⁻¹ *
            (pointRectifiableConformalEDist a y p z).toReal ≤ ‖F p - F z‖ ∧
        ‖F p - F z‖ ≤ Real.sqrt (1 + (∑ j, a j) / 2) *
            (pointRectifiableConformalEDist a y p z).toReal := by
  have hq : 0 ≤ ∑ j, a j := Finset.sum_nonneg fun j _ => ha j
  have hB : 0 < 1 + (∑ j, a j) / 2 := by positivity
  obtain ⟨F, hF, hbounds⟩ := exists_scaled_homeomorph_of_asymmetric_bounds
    D hcont hopen hbij (fun p z => (pointSmoothConformalEDist a y p z).toReal) hB hmetric
  refine ⟨F, hF, fun p z => ?_⟩
  simpa only [pointRectifiableConformalEDist_eq_smooth ha y p z] using hbounds p z

end RepulsiveCoulomb
