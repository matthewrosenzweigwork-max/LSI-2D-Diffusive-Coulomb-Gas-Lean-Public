module

public import LeanResearch.RepulsiveCoulomb.PointSmoothJoinTangents
public import LeanResearch.RepulsiveCoulomb.JordanSmoothArcTurnAssembly

@[expose] public section

/-! Actual positive-affine trace comparison, including the closed endpoints.
Derivative uniqueness on the closed unit interval prevents any use of an
unproved full-neighborhood equality at a corner attachment. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem normalized_complex_smul_pos {z : ℂ} (hz : z ≠ 0) {c : ℝ} (hc : 0 < c) :
    (c • z) / (‖c • z‖ : ℂ) = z / (‖z‖ : ℂ) :=
  congrArg (fun q : Circle => (q : ℂ)) (euclideanDirection_smul_pos hz hc)

theorem hasDerivAt_positive_affine_trace
    {f : ℝ → ℂ} (hf : Differentiable ℝ f) (a b t : ℝ) :
    HasDerivAt (fun s : ℝ => f (a + b * s)) (b • deriv f (a + b * t)) t := by
  have hp : HasDerivAt (fun s : ℝ => a + b * s) b t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul b).const_add a
  exact ((hf (a + b * t)).hasDerivAt).scomp t hp

/-- Identical actual positively parametrized traces have identical tangent
DIRECTIONS. Their speeds need not agree. Both closed endpoints are included. -/
theorem positive_affine_trace_tangent_direction
    {f g : ℝ → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    {a b c d t : ℝ} (hb : 0 < b) (hd : 0 < d) (ht : t ∈ Icc (0 : ℝ) 1)
    (heq : ∀ s ∈ Icc (0 : ℝ) 1, f (a + b * s) = g (c + d * s))
    (hfr : deriv f (a + b * t) ≠ 0) (hgr : deriv g (c + d * t) ≠ 0) :
    deriv f (a + b * t) / (‖deriv f (a + b * t)‖ : ℂ) =
      deriv g (c + d * t) / (‖deriv g (c + d * t)‖ : ℂ) := by
  have hdf := hasDerivAt_positive_affine_trace hf a b t
  have hdg := hasDerivAt_positive_affine_trace hg c d t
  have he : b • deriv f (a + b * t) = d • deriv g (c + d * t) := by
    rw [← hdf.deriv, ← hdg.deriv]
    exact deriv_eq_of_eqOn_unitInterval ht hdf.differentiableAt hdg.differentiableAt heq
  calc
    deriv f (a + b * t) / (‖deriv f (a + b * t)‖ : ℂ) =
        (b • deriv f (a + b * t)) / (‖b • deriv f (a + b * t)‖ : ℂ) :=
      (normalized_complex_smul_pos hfr hb).symm
    _ = (d • deriv g (c + d * t)) / (‖d • deriv g (c + d * t)‖ : ℂ) := by rw [he]
    _ = deriv g (c + d * t) / (‖deriv g (c + d * t)‖ : ℂ) :=
      normalized_complex_smul_pos hgr hd

end RepulsiveCoulomb
