import LeanResearch.RepulsiveCoulomb.JordanSupportingPoint
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Genuine C0 periodization of the original, possibly cornered boundary.
One regular interior parameter can be moved to the seam with exact local
agreement, independently of any smoothing or winding classification. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

def pointContinuousPeriodize (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  AddCircle.liftIco (1 : ℝ) 0 f (t : AddCircle (1 : ℝ))

theorem pointContinuousPeriodize_periodic (f : ℝ → ℂ) :
    Function.Periodic (pointContinuousPeriodize f) 1 := by
  intro t
  unfold pointContinuousPeriodize
  rw [AddCircle.coe_add_period]

theorem pointContinuousPeriodize_eq_Ico (f : ℝ → ℂ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    pointContinuousPeriodize f t = f t := by
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  exact AddCircle.liftIco_zero_coe_apply ht

theorem pointContinuousPeriodize_eq_Icc {f : ℝ → ℂ} (hclose : f 0 = f 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : pointContinuousPeriodize f t = f t := by
  by_cases ht1 : t = 1
  · subst t
    have h := pointContinuousPeriodize_periodic f 0
    have h0 := pointContinuousPeriodize_eq_Ico f (t := 0) (by norm_num)
    simpa only [zero_add, h0, hclose] using h
  · exact pointContinuousPeriodize_eq_Ico f ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩

theorem pointContinuousPeriodize_continuous {f : ℝ → ℂ}
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) (hclose : f 0 = f 1) :
    Continuous (pointContinuousPeriodize f) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  exact (AddCircle.liftIco_zero_continuous hclose hc).comp (AddCircle.continuous_mk' (1 : ℝ))

theorem pointContinuousPeriodize_injOn {f : ℝ → ℂ} (hi : InjOn f (Ico (0 : ℝ) 1)) :
    InjOn (pointContinuousPeriodize f) (Ico (0 : ℝ) 1) := by
  intro s hs t ht he
  rw [pointContinuousPeriodize_eq_Ico f hs, pointContinuousPeriodize_eq_Ico f ht] at he
  exact hi hs ht he

theorem pointContinuousPeriodize_eventually_eq (f : ℝ → ℂ) {a : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) : pointContinuousPeriodize f =ᶠ[𝓝 a] f := by
  filter_upwards [Ioo_mem_nhds ha.1 ha.2] with t ht
  exact pointContinuousPeriodize_eq_Ico f ⟨ht.1.le, ht.2⟩

theorem periodic_closed_interval_image_shift {f : ℝ → ℂ}
    (hp : Function.Periodic f 1) (a : ℝ) :
    (fun t : ℝ => f (t + a)) '' Icc (0 : ℝ) 1 = f '' Icc (0 : ℝ) 1 := by
  have hp' : Function.Periodic (fun t : ℝ => f (t + a)) 1 := by
    intro t
    simpa only [add_assoc, add_comm, add_left_comm] using hp (t + a)
  apply Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    obtain ⟨s, hs, he⟩ := hp.exists_mem_Ico₀ (by norm_num) (t + a)
    exact ⟨s, ⟨hs.1, hs.2.le⟩, he.symm⟩
  · rintro z ⟨t, ht, rfl⟩
    obtain ⟨s, hs, he⟩ := hp'.exists_mem_Ico₀ (by norm_num) (t - a)
    refine ⟨s, ⟨hs.1, hs.2.le⟩, ?_⟩
    simpa only [sub_add_cancel] using he.symm

/-- The original simple loop, with no smoothing, admits a continuous periodic
representative with a genuine nonzero derivative at its new basepoint. -/
theorem exists_continuous_periodic_loop_regular_basepoint {f : ℝ → ℂ}
    (hc : ContinuousOn f (Icc (0 : ℝ) 1)) (hclose : f 0 = f 1)
    (hi : InjOn f (Ico (0 : ℝ) 1)) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hf : DifferentiableAt ℝ f a) (hreg : deriv f a ≠ 0) :
    ∃ Γ : ℝ → ℂ, Continuous Γ ∧ Function.Periodic Γ 1 ∧
      InjOn Γ (Ico (0 : ℝ) 1) ∧ DifferentiableAt ℝ Γ 0 ∧ deriv Γ 0 ≠ 0 ∧
      Γ 0 = f a ∧ Γ '' Icc (0 : ℝ) 1 = f '' Icc (0 : ℝ) 1 ∧
      Γ =ᶠ[𝓝 0] (fun t => f (t + a)) := by
  let Γ : ℝ → ℂ := fun t => pointContinuousPeriodize f (t + a)
  have hp := pointContinuousPeriodize_periodic f
  have hΓp : Function.Periodic Γ 1 := by
    intro t
    simpa only [Γ, add_assoc, add_comm, add_left_comm] using hp (t + a)
  have hshift : Tendsto (fun t : ℝ => t + a) (𝓝 0) (𝓝 a) := by
    simpa only [id_eq, zero_add] using (continuous_id.add_const a).tendsto 0
  have heq : Γ =ᶠ[𝓝 0] (fun t => f (t + a)) :=
    (pointContinuousPeriodize_eventually_eq f ha).comp_tendsto hshift
  have hf' : HasDerivAt f (deriv f a) (0 + a) := by simpa only [zero_add] using hf.hasDerivAt
  have hΓD : HasDerivAt Γ (deriv f a) 0 := (hf'.comp_add_const 0 a).congr_of_eventuallyEq heq
  refine ⟨Γ, (pointContinuousPeriodize_continuous hc hclose).comp (continuous_id.add_const a),
    hΓp, periodic_simple_loop_shift_injOn hp (pointContinuousPeriodize_injOn hi) ⟨ha.1.le, ha.2.le⟩,
    hΓD.differentiableAt, ?_, ?_, ?_, heq⟩
  · rw [hΓD.deriv]
    exact hreg
  · simpa only [zero_add] using heq.self_of_nhds
  · change (fun t => pointContinuousPeriodize f (t + a)) '' Icc (0 : ℝ) 1 = _
    rw [periodic_closed_interval_image_shift hp a]
    have heI : EqOn (pointContinuousPeriodize f) f (Icc (0 : ℝ) 1) :=
      fun t ht => pointContinuousPeriodize_eq_Icc hclose ht
    exact heI.image_eq

end RepulsiveCoulomb
