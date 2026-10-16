module

public import LeanResearch.RepulsiveCoulomb.CoulombPotentialWeight
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section

/-! Local affine Hessian pullback. The function is smooth only on an open
neighborhood, not globally across the Coulomb collision set. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem local_affine_hessian {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    {z : E} (hz : z ∈ U) (L : F →L[ℝ] E) (v w : F) :
    fderiv ℝ (fderiv ℝ (fun x : F => f (z + L x))) 0 v w =
      fderiv ℝ (fderiv ℝ f) z (L v) (L w) := by
  have hfl (x : E) (hx : x ∈ U) : ContDiffAt ℝ 2 f x :=
    (hf x hx).contDiffAt (hU.mem_nhds hx)
  have hA (x : F) : HasFDerivAt (fun y : F => z + L y) L x :=
    L.hasFDerivAt.const_add z
  have hD : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hfl z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hd : HasFDerivAt (fun x : F => fderiv ℝ f (z + L x))
      ((fderiv ℝ (fderiv ℝ f) z).comp L) 0 := by
    have hD' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) (z + L 0) := by
      simpa only [map_zero, add_zero] using hD.hasFDerivAt
    exact hD'.comp 0 (hA 0)
  have he : fderiv ℝ (fun x : F => f (z + L x)) =ᶠ[𝓝 0]
      (fun x : F => (fderiv ℝ f (z + L x)).comp L) := by
    have hnb : ∀ᶠ x in 𝓝 (0 : F), z + L x ∈ U := by
      have ht : Tendsto (fun x : F => z + L x) (𝓝 0) (𝓝 z) := by
        simpa only [map_zero, add_zero] using (hA 0).continuousAt.tendsto
      exact ht.eventually (hU.mem_nhds hz)
    filter_upwards [hnb] with x hx
    exact ((hfl _ hx).differentiableAt (by norm_num)).hasFDerivAt.comp x (hA x) |>.fderiv
  have hh := (hd.clm_comp (hasFDerivAt_const L (0 : F))).congr_of_eventuallyEq he
  have hv := congrArg (fun T : F →L[ℝ] F →L[ℝ] ℝ => T v w) hh.fderiv
  simpa using hv

end RepulsiveCoulomb
