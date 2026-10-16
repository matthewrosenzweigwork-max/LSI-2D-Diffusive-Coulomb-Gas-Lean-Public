module

public import LeanResearch.RepulsiveCoulomb.JordanBezierCorner

@[expose] public section

/-! The symmetric parameter-width quadratic replacement matches the actual
incoming and outgoing radial velocities exactly. This elementary jet identity
lets finite corner smoothing retain affine radial collars, avoiding another
speed normalization at the true vertices. Records-only candidate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def euclideanSymmetricCornerPatch (δ : ℝ) (u v : ℂ) (t : ℝ) : ℂ :=
  euclideanBezierCorner (δ • u) (δ • v) ((t + δ) / (2 * δ))

@[simp] theorem euclideanSymmetricCornerPatch_left {δ : ℝ} (hδ : δ ≠ 0) (u v : ℂ) :
    euclideanSymmetricCornerPatch δ u v (-δ) = (-δ) • u := by
  simp [euclideanSymmetricCornerPatch, hδ, neg_smul]

@[simp] theorem euclideanSymmetricCornerPatch_right {δ : ℝ} (hδ : δ ≠ 0) (u v : ℂ) :
    euclideanSymmetricCornerPatch δ u v δ = δ • v := by
  have h : (δ + δ) / (2 * δ) = 1 := by field_simp [hδ]; ring
  simp only [euclideanSymmetricCornerPatch, h, euclideanBezierCorner_one]

theorem euclideanSymmetricCornerPatch_contDiff (δ : ℝ) (u v : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanSymmetricCornerPatch δ u v) := by
  unfold euclideanSymmetricCornerPatch
  exact (euclideanBezierCorner_contDiff _ _).comp (by fun_prop)

theorem euclideanSymmetricCornerPatch_hasDerivAt {δ : ℝ} (hδ : δ ≠ 0)
    (u v : ℂ) (t : ℝ) :
    HasDerivAt (euclideanSymmetricCornerPatch δ u v)
      ((2 * δ)⁻¹ • ((2 : ℝ) •
        euclideanCornerBlend (δ • u) (δ • v) ((t + δ) / (2 * δ)))) t := by
  have hinner : HasDerivAt (fun t : ℝ => (t + δ) / (2 * δ)) (2 * δ)⁻¹ t := by
    simpa only [one_div, id_eq] using ((hasDerivAt_id t).add_const δ).div_const (2 * δ)
  change HasDerivAt (fun x : ℝ => euclideanBezierCorner (δ • u) (δ • v) ((x + δ) / (2 * δ))) _ t
  simpa only [Function.comp_def] using
    (euclideanBezierCorner_hasDerivAt (δ • u) (δ • v) ((t + δ) / (2 * δ))).scomp t hinner

/-- The two endpoint derivatives are literally the old affine radial
velocities, rather than merely positive multiples. -/
theorem euclideanSymmetricCornerPatch_endpoint_derivatives {δ : ℝ}
    (hδ : δ ≠ 0) (u v : ℂ) :
    deriv (euclideanSymmetricCornerPatch δ u v) (-δ) = u ∧
      deriv (euclideanSymmetricCornerPatch δ u v) δ = v := by
  have h2 : (2 * δ) ≠ 0 := mul_ne_zero (by norm_num) hδ
  have hplus : (δ + δ) / (2 * δ) = 1 := by field_simp [hδ]; ring
  constructor
  · rw [(euclideanSymmetricCornerPatch_hasDerivAt hδ u v (-δ)).deriv]
    simp only [neg_add_cancel, zero_div, euclideanCornerBlend_zero, smul_smul,
      inv_mul_cancel₀ h2, one_smul]
  · rw [(euclideanSymmetricCornerPatch_hasDerivAt hδ u v δ).deriv, hplus,
      euclideanCornerBlend_one, smul_smul, smul_smul]
    rw [show (2 * δ)⁻¹ * 2 * δ = 1 by field_simp [hδ], one_smul]

/-- The exact endpoint-jet matching survives a genuine differentiable chart,
by the actual chain rule at the two attachment points. -/
theorem holomorphic_symmetric_corner_endpoint_jets {δ : ℝ} (hδ : δ ≠ 0)
    {H : ℂ → ℂ} (u v : ℂ)
    (hleft : DifferentiableAt ℂ H ((-δ) • u))
    (hright : DifferentiableAt ℂ H (δ • v)) :
    deriv (H ∘ euclideanSymmetricCornerPatch δ u v) (-δ) =
        deriv (fun t : ℝ => H (t • u)) (-δ) ∧
      deriv (H ∘ euclideanSymmetricCornerPatch δ u v) δ =
        deriv (fun t : ℝ => H (t • v)) δ := by
  have he := euclideanSymmetricCornerPatch_endpoint_derivatives hδ u v
  have hP : Differentiable ℝ (euclideanSymmetricCornerPatch δ u v) :=
    (euclideanSymmetricCornerPatch_contDiff δ u v).differentiable (by simp)
  have hPL : HasDerivAt (euclideanSymmetricCornerPatch δ u v) u (-δ) := by
    simpa only [he.1] using (hP (-δ)).hasDerivAt
  have hPR : HasDerivAt (euclideanSymmetricCornerPatch δ u v) v δ := by
    simpa only [he.2] using (hP δ).hasDerivAt
  have hHL : HasDerivAt H (deriv H ((-δ) • u))
      (euclideanSymmetricCornerPatch δ u v (-δ)) := by
    simpa only [euclideanSymmetricCornerPatch_left hδ] using hleft.hasDerivAt
  have hHR : HasDerivAt H (deriv H (δ • v))
      (euclideanSymmetricCornerPatch δ u v δ) := by
    simpa only [euclideanSymmetricCornerPatch_right hδ] using hright.hasDerivAt
  have hL : HasDerivAt (fun t : ℝ => t • u) u (-δ) := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (-δ)).smul_const u
  have hR : HasDerivAt (fun t : ℝ => t • v) v δ := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id δ).smul_const v
  constructor
  · rw [(hHL.comp (-δ) hPL).deriv]
    simpa only [Function.comp_def] using (hleft.hasDerivAt.comp (-δ) hL).deriv.symm
  · rw [(hHR.comp δ hPR).deriv]
    simpa only [Function.comp_def] using (hright.hasDerivAt.comp δ hR).deriv.symm

end RepulsiveCoulomb
