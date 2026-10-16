module

public import LeanResearch.RepulsiveCoulomb.PoleBranchDerivativeBounds
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

/-! Holomorphic parameter dependence of circle integration, for the actual
Frechet-holomorphic class. Compactness and the Schwarz derivative estimate
supply the domination internally; no analytic or C1 hypothesis is imposed. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology Interval
namespace RepulsiveCoulomb

theorem poleBranch_differentiableAt_circleIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} {s : Set (E × ℂ)} (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) {x₀ : E} {c : ℂ} {r : ℝ}
    (hc : ∀ z ∈ sphere c |r|, (x₀, z) ∈ s) :
    DifferentiableAt ℂ (fun x => ∮ z in C(c, r), f (x, z)) x₀ := by
  letI : ProperSpace E := FiniteDimensional.proper ℂ E
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let K : Set (E × ℂ) := {x₀} ×ˢ sphere c |r|
  have hK : IsCompact K := isCompact_singleton.prod (isCompact_sphere c |r|)
  have hKs : K ⊆ s := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    rcases mem_singleton_iff.mp hx with rfl
    exact hc z hz
  obtain ⟨δ, hδ, hδs⟩ := hK.exists_cthickening_subset_open hs hKs
  obtain ⟨M, hM⟩ := hK.cthickening.exists_bound_of_continuousOn
    (hf.continuousOn.mono hδs)
  have hball (z : ℂ) (hz : z ∈ sphere c |r|) :
      ball (x₀, z) δ ⊆ cthickening δ K := by
    intro p hp
    exact mem_cthickening_of_dist_le p (x₀, z) δ K ⟨rfl, hz⟩ (mem_ball.mp hp).le
  have hp (x : E) (hx : x ∈ ball x₀ (δ / 2)) (θ : ℝ) :
      (x, circleMap c r θ) ∈ ball (x₀, circleMap c r θ) (δ / 2) := by
    simpa only [mem_ball, dist_prod_same_right] using hx
  have hmem (x : E) (hx : x ∈ ball x₀ (δ / 2)) (θ : ℝ) :
      (x, circleMap c r θ) ∈ s := by
    apply hδs (hball _ (circleMap_mem_sphere' c r θ) ?_)
    exact ball_subset_ball (by linarith : δ / 2 ≤ δ) (hp x hx θ)
  have hdiff (x : E) (hx : x ∈ ball x₀ (δ / 2)) (θ : ℝ) :
      DifferentiableAt ℂ f (x, circleMap c r θ) :=
    hf.differentiableAt (hs.mem_nhds (hmem x hx θ))
  have hcont (x : E) (hx : x ∈ ball x₀ (δ / 2)) :
      Continuous (fun θ : ℝ => f (x, circleMap c r θ)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (hdiff x hx θ).continuousAt.comp (f := fun t : ℝ => (x, circleMap c r t))
      (show ContinuousAt (fun t : ℝ => (x, circleMap c r t)) θ from by fun_prop)
  let F : E → ℝ → ℂ := fun x θ =>
    (circleMap 0 r θ * Complex.I) • f (x, circleMap c r θ)
  let D : E → ℝ → E →L[ℂ] ℂ := fun x θ =>
    (circleMap 0 r θ * Complex.I) •
      (fderiv ℂ f (x, circleMap c r θ)).comp (ContinuousLinearMap.inl ℂ E ℂ)
  have hFcont (x : E) (hx : x ∈ ball x₀ (δ / 2)) : Continuous (F x) :=
    (show Continuous (fun θ : ℝ => circleMap 0 r θ * Complex.I) by fun_prop).smul (hcont x hx)
  have hx₀ : x₀ ∈ ball x₀ (δ / 2) := mem_ball_self (by positivity)
  have hDm : AEStronglyMeasurable (D x₀) (volume.restrict (Ι 0 (2 * Real.pi))) := by
    have hA : Measurable (fun θ : ℝ => fderiv ℂ f (x₀, circleMap c r θ)) :=
      (measurable_fderiv ℂ f).comp (by fun_prop)
    have hL : Continuous (fun A : (E × ℂ) →L[ℂ] ℂ =>
        A.comp (ContinuousLinearMap.inl ℂ E ℂ)) :=
      continuous_id.clm_comp continuous_const
    exact (show Continuous (fun θ : ℝ => circleMap 0 r θ * Complex.I) by fun_prop).aestronglyMeasurable.smul
      (hL.measurable.comp hA).aestronglyMeasurable
  have hbound (x : E) (hx : x ∈ ball x₀ (δ / 2)) (θ : ℝ) :
      ‖D x θ‖ ≤ |r| * ((2 * M) / (δ - δ / 2)) := by
    have hder := poleBranch_fderiv_norm_le_inner_ball
      (by linarith : δ / 2 < δ) (hp x hx θ)
      (hf.mono ((hball _ (circleMap_mem_sphere' c r θ)).trans hδs))
      (fun p hp => hM p (hball _ (circleMap_mem_sphere' c r θ) hp))
    have hcomp : ‖(fderiv ℂ f (x, circleMap c r θ)).comp (ContinuousLinearMap.inl ℂ E ℂ)‖ ≤
        ‖fderiv ℂ f (x, circleMap c r θ)‖ := by
      calc
        _ ≤ ‖fderiv ℂ f (x, circleMap c r θ)‖ * ‖ContinuousLinearMap.inl ℂ E ℂ‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖fderiv ℂ f (x, circleMap c r θ)‖ * 1 :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℂ E ℂ) (norm_nonneg _)
        _ = _ := mul_one _
    dsimp only [D]
    rw [norm_smul, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
    exact mul_le_mul_of_nonneg_left (hcomp.trans hder) (abs_nonneg r)
  have hFd (x : E) (hx : x ∈ ball x₀ (δ / 2)) (θ : ℝ) :
      HasFDerivAt (fun y => F y θ) (D x θ) x := by
    convert! ((hdiff x hx θ).hasFDerivAt.comp x
        (hasFDerivAt_prodMk_left (𝕜 := ℂ) x (circleMap c r θ))).const_smul
          (circleMap 0 r θ * Complex.I) using 1
  have h := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := F) (F' := D) (bound := fun _ => |r| * ((2 * M) / (δ - δ / 2)))
    (ball_mem_nhds x₀ (by positivity : 0 < δ / 2))
    (by filter_upwards [ball_mem_nhds x₀ (by positivity : 0 < δ / 2)] with x hx
        exact (hFcont x hx).aestronglyMeasurable)
    ((hFcont x₀ hx₀).intervalIntegrable 0 (2 * Real.pi)) hDm
    (Eventually.of_forall (fun θ _ x hx => hbound x hx θ))
    intervalIntegrable_const
    (Eventually.of_forall (fun θ _ x hx => hFd x hx θ))
  simpa only [circleIntegral, deriv_circleMap, F] using h.differentiableAt

end RepulsiveCoulomb
