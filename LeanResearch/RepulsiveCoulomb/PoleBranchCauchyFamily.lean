import LeanResearch.RepulsiveCoulomb.PoleBranchParametricCircle
import LeanResearch.RepulsiveCoulomb.PoleBranchCauchy
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The canonical removable extension is jointly holomorphic in all parameters.
Actual weighted product integrability initially gives only almost every fiber;
continuity and full support remove that exceptional set of parameters. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem poleBranch_differentiableOn_cauchy_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) {f : E × ℂ → ℂ} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (U ×ˢ (ball (0 : ℂ) R \ {0}))) :
    DifferentiableOn ℂ (fun p : E × ℂ => poleBranchCauchy (fun z => f (p.1, z)) r p.2)
      (U ×ˢ ball (0 : ℂ) r) := by
  let S : Set ((E × ℂ) × ℂ) :=
    (fun q => (q.1.1, q.2)) ⁻¹' (U ×ˢ (ball (0 : ℂ) R \ {0})) ∩
      {q | q.2 - q.1.2 ≠ 0}
  have hS : IsOpen S :=
    ((hU.prod (isOpen_ball.sdiff isClosed_singleton)).preimage (by fun_prop)).inter
      (isOpen_ne.preimage (by fun_prop))
  let g : (E × ℂ) × ℂ → ℂ := fun q => (q.2 - q.1.2)⁻¹ • f (q.1.1, q.2)
  have hg : DifferentiableOn ℂ g S := by
    dsimp only [g]
    simp only [smul_eq_mul]
    apply DifferentiableOn.mul
    · exact (differentiableOn_snd.sub differentiableOn_fst.snd).inv (fun q hq => hq.2)
    · exact hf.comp (differentiableOn_fst.fst.prodMk differentiableOn_snd) (fun _ hq => hq.1)
  intro p hp
  have hc : ∀ z ∈ sphere (0 : ℂ) |r|, (p, z) ∈ S := by
    intro z hz
    have hzr : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right, abs_of_pos hr] using hz
    have hzR : z ∈ ball (0 : ℂ) R := by simpa only [mem_ball, dist_zero_right, hzr] using hrR
    have hz0 : z ≠ 0 := by
      intro h
      have : r = 0 := by simpa only [h, norm_zero] using hzr.symm
      exact hr.ne' this
    refine ⟨⟨hp.1, hzR, by simpa only [mem_singleton_iff] using hz0⟩, ?_⟩
    apply sub_ne_zero.mpr
    intro heq
    have hp2 := mem_ball.mp hp.2
    rw [dist_zero_right, ← heq, hzr] at hp2
    exact lt_irrefl r hp2
  have hd := poleBranch_differentiableAt_circleIntegral hS hg hc
  exact (hd.const_smul (2 * Real.pi * Complex.I : ℂ)⁻¹).differentiableWithinAt

theorem weighted_even_puncture_removable_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [SFinite μ] [Measure.IsOpenPosMeasure μ]
    {U : Set E} (hU : IsOpen U) {f : E × ℂ → ℂ} {a R r : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 2) (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (U ×ˢ (ball (0 : ℂ) R \ {0})))
    (hi : Integrable (fun pz : E × ℂ => ‖pz.2‖ ^ a * ‖f pz‖ ^ 2)
      ((μ.restrict U).prod (volume.restrict (ball (0 : ℂ) R))))
    (heven : ∀ p ∈ U, ∀ z ∈ ball (0 : ℂ) R, f (p, -z) = f (p, z)) :
    ∃ F : E × ℂ → ℂ, DifferentiableOn ℂ F (U ×ˢ ball (0 : ℂ) r) ∧
      ∀ p ∈ U, ∀ z ∈ ball (0 : ℂ) r \ {0}, F (p, z) = f (p, z) := by
  let F : E × ℂ → ℂ := fun p => poleBranchCauchy (fun z => f (p.1, z)) r p.2
  have hF : DifferentiableOn ℂ F (U ×ˢ ball (0 : ℂ) r) :=
    poleBranch_differentiableOn_cauchy_family hU hr hrR hf
  have hfiber (p : E) (hp : p ∈ U) :
      DifferentiableOn ℂ (fun z => f (p, z)) (ball (0 : ℂ) R \ {0}) := by
    exact hf.comp ((differentiableOn_const p).prodMk differentiableOn_id) (fun z hz => ⟨hp, hz⟩)
  have hae := weighted_even_puncture_cauchy_ae (μ.restrict U) ha ha2 hr hrR
    (by filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
        exact hfiber p hp) hi
    (by filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
        exact heven p hp)
  refine ⟨F, hF, ?_⟩
  intro p hp z hz
  have heq : (fun q => F (q, z)) =ᵐ[μ.restrict U] (fun q => f (q, z)) := by
    filter_upwards [hae] with q hq
    exact hq.2 z hz
  have hFc : ContinuousOn (fun q => F (q, z)) U :=
    hF.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun q hq => ⟨hq, hz.1⟩)
  have hfc : ContinuousOn (fun q => f (q, z)) U :=
    hf.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun q hq => ⟨hq, ball_subset_ball hrR.le hz.1, hz.2⟩)
  exact Measure.eqOn_open_of_ae_eq heq hU hFc hfc hp

end RepulsiveCoulomb
