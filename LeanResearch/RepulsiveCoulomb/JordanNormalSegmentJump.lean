import LeanResearch.RepulsiveCoulomb.JordanNormalSegmentRatio
import LeanResearch.RepulsiveCoulomb.JordanNormalSegmentSeparation
import Mathlib.Topology.Order.ProjIcc

/-! The signed 2π argument jump across an actual isolated normal crossing.
The principal ratio argument is continuous on the open parameter interval and
has the proved limits −π,+π. Covering-lift uniqueness turns these actual limits
into the jump. Records-only phase-five candidate. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- The exact signed local jump, in a form separating concrete branch geometry
from the constructed simple-loop normal-segment margin. -/
theorem normal_segment_argument_jump
    {v : ℝ → ℂ} (hv : Continuous v) (hv0 : v 0 = 0) (hv1 : v 1 = 0)
    {ε : ℝ} (hε : 0 < ε)
    (haway : ∀ t ∈ Ioo (0 : ℝ) 1, (v t).re = 0 → ε < ‖v t‖)
    (hplus : ∀ t ∈ Icc (0 : ℝ) 1, v t - (ε : ℂ) * Complex.I ≠ 0)
    (hminus : ∀ t ∈ Icc (0 : ℝ) 1, v t + (ε : ℂ) * Complex.I ≠ 0)
    (hright : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < (v t).re)
    (hleft : ∀ᶠ t in 𝓝[<] (1 : ℝ), (v t).re < 0)
    {θp θm : ℝ → ℝ} (hθp : Continuous θp) (hθm : Continuous θm)
    (hliftp : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp ((θp t : ℂ) * Complex.I) =
      (v t - (ε : ℂ) * Complex.I) / (‖v t - (ε : ℂ) * Complex.I‖ : ℂ))
    (hliftm : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp ((θm t : ℂ) * Complex.I) =
      (v t + (ε : ℂ) * Complex.I) / (‖v t + (ε : ℂ) * Complex.I‖ : ℂ)) :
    (θp 1 - θp 0) - (θm 1 - θm 0) = 2 * Real.pi := by
  let α : ℝ → ℝ := fun t => θp t - θm t
  let β : ℝ → ℝ := fun t => Complex.arg (normalSegmentRatio ε (v t))
  have hα : Continuous α := hθp.sub hθm
  have hratio : ContinuousOn (fun t => normalSegmentRatio ε (v t)) (Ioo (0 : ℝ) 1) :=
    (hv.sub continuous_const).continuousOn.div (hv.add continuous_const).continuousOn
      (fun t ht => hminus t (Ioo_subset_Icc_self ht))
  have hβ : ContinuousOn β (Ioo (0 : ℝ) 1) :=
    Complex.continuousOn_arg.comp hratio (fun t ht => normalSegmentRatio_mem_slitPlane hε (haway t ht))
  have hexp (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : Circle.exp (α t) = Circle.exp (β t) := by
    have hp : Circle.exp (θp t) = euclideanDirection (v t - (ε : ℂ) * Complex.I)
        (hplus t (Ioo_subset_Icc_self ht)) := by
      apply Circle.ext
      exact hliftp t (Ioo_subset_Icc_self ht)
    have hm : Circle.exp (θm t) = euclideanDirection (v t + (ε : ℂ) * Complex.I)
        (hminus t (Ioo_subset_Icc_self ht)) := by
      apply Circle.ext
      exact hliftm t (Ioo_subset_Icc_self ht)
    change Circle.exp (θp t - θm t) = Circle.exp (Complex.arg _)
    rw [Circle.exp_sub, hp, hm]
    exact (circle_exp_arg_vector_ratio _ _
      (hplus t (Ioo_subset_Icc_self ht)) (hminus t (Ioo_subset_Icc_self ht))).symm
  let K := α (1 / 2) - β (1 / 2)
  have hconst (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : α t - β t = K := by
    exact Circle.isCoveringMap_exp.constOn_of_comp (convex_Ioo (0 : ℝ) 1).isPreconnected
      (hα.continuousOn.sub hβ)
      (by intro a ha b hb
          change Circle.exp (α a - β a) = Circle.exp (α b - β b)
          rw [Circle.exp_sub (α a) (β a), Circle.exp_sub (α b) (β b),
            hexp a ha, hexp b hb, div_self', div_self'])
      ht (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)
  have hvlim0 : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hfull : Tendsto v (𝓝 (0 : ℝ)) (𝓝 (v 0)) := hv.continuousAt.tendsto
    rw [hv0] at hfull
    exact hfull.mono_left nhdsWithin_le_nhds
  have hvlim1 : Tendsto v (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hfull : Tendsto v (𝓝 (1 : ℝ)) (𝓝 (v 1)) := hv.continuousAt.tendsto
    rw [hv1] at hfull
    exact hfull.mono_left nhdsWithin_le_nhds
  have hb0 : Tendsto β (𝓝[>] (0 : ℝ)) (𝓝 (-Real.pi)) :=
    normalSegmentRatio_arg_tendsto_right hε hvlim0 hright
  have hb1 : Tendsto β (𝓝[<] (1 : ℝ)) (𝓝 Real.pi) :=
    normalSegmentRatio_arg_tendsto_left hε hvlim1 hleft
  have ha0 : Tendsto α (𝓝[>] (0 : ℝ)) (𝓝 (α 0)) :=
    hα.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ha1 : Tendsto α (𝓝[<] (1 : ℝ)) (𝓝 (α 1)) :=
    hα.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hk0 : Tendsto (fun t => α t - β t) (𝓝[>] (0 : ℝ)) (𝓝 K) := by
    apply (Filter.tendsto_congr' (f₁ := fun _ => K) (f₂ := fun t => α t - β t) ?_).mp tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht0 ht1
    exact (hconst t ⟨ht0, ht1⟩).symm
  have hk1 : Tendsto (fun t => α t - β t) (𝓝[<] (1 : ℝ)) (𝓝 K) := by
    apply (Filter.tendsto_congr' (f₁ := fun _ => K) (f₂ := fun t => α t - β t) ?_).mp tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht1 ht0
    exact (hconst t ⟨ht0, ht1⟩).symm
  have he0 := tendsto_nhds_unique hk0 (ha0.sub hb0)
  have he1 := tendsto_nhds_unique hk1 (ha1.sub hb1)
  dsimp [α] at he0 he1
  linarith

/-- Constructed normal-segment geometry excludes both observation points from
an actual regular simple loop, and gives the signed jump for every pair of
actual continuous argument lifts. -/
theorem exists_simple_loop_signed_normal_jump {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) (hbase : deriv γ 0 = 1) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ γ 0 + (ε : ℂ) * Complex.I) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ γ 0 - (ε : ℂ) * Complex.I) ∧
      ∀ (θp θm : Icc (0 : ℝ) 1 → ℝ), Continuous θp → Continuous θm →
        (∀ t, Complex.exp ((θp t : ℂ) * Complex.I) =
          (γ t - (γ 0 + (ε : ℂ) * Complex.I)) /
            (‖γ t - (γ 0 + (ε : ℂ) * Complex.I)‖ : ℂ)) →
        (∀ t, Complex.exp ((θm t : ℂ) * Complex.I) =
          (γ t - (γ 0 - (ε : ℂ) * Complex.I)) /
            (‖γ t - (γ 0 - (ε : ℂ) * Complex.I)‖ : ℂ)) →
        (θp 1 - θp 0) - (θm 1 - θm 0) = 2 * Real.pi := by
  obtain ⟨ε, hε, hmargin, hright, hleft⟩ :=
    exists_simple_loop_normal_segment_margin hγ hp hinj hbase
  have hclose : γ 1 = γ 0 := by simpa using hp 0
  have hi : (ε : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hε.ne') Complex.I_ne_zero
  have havoid (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      γ t - γ 0 ≠ (ε : ℂ) * Complex.I ∧ γ t - γ 0 ≠ -(ε : ℂ) * Complex.I := by
    by_cases ht0 : t = 0
    · simp [ht0, hi, (neg_ne_zero.mpr hi).symm, hε.ne']
    by_cases ht1 : t = 1
    · simp [ht1, hclose, hi, (neg_ne_zero.mpr hi).symm, hε.ne']
    have htI : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    constructor <;> intro heq
    · have h := hmargin t htI (by rw [heq]; simp)
      rw [heq] at h
      simpa [norm_mul, Complex.norm_real, abs_of_pos hε] using h
    · have h := hmargin t htI (by rw [heq]; simp)
      rw [heq] at h
      simpa [norm_mul, Complex.norm_real, abs_of_pos hε] using h
  have havp : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ γ 0 + (ε : ℂ) * Complex.I := by
    intro t ht heq
    exact (havoid t ht).1 (by rw [heq]; ring)
  have havm : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ γ 0 - (ε : ℂ) * Complex.I := by
    intro t ht heq
    exact (havoid t ht).2 (by rw [heq]; ring)
  refine ⟨ε, hε, havp, havm, ?_⟩
  intro θp θm hθp hθm hliftp hliftm
  let Θp := Set.IccExtend (show (0 : ℝ) ≤ 1 by norm_num) θp
  let Θm := Set.IccExtend (show (0 : ℝ) ≤ 1 by norm_num) θm
  have hΘp : Continuous Θp := (continuous_IccExtend_iff).mpr hθp
  have hΘm : Continuous Θm := (continuous_IccExtend_iff).mpr hθm
  have hj := normal_segment_argument_jump (v := fun t => γ t - γ 0)
    (hγ.continuous.sub continuous_const) (by simp) (by simp [hclose]) hε hmargin
    (fun t ht => sub_ne_zero.mpr (havoid t ht).1)
    (fun t ht => by
      intro hzero
      apply (havoid t ht).2
      simpa only [neg_mul] using eq_neg_of_add_eq_zero_left hzero)
    hright hleft hΘp hΘm
    (fun t ht => by
      dsimp only [Θp]
      rw [Set.IccExtend_of_mem (show (0 : ℝ) ≤ 1 by norm_num) θp ht]
      simpa only [sub_add_eq_sub_sub] using hliftp ⟨t, ht⟩)
    (fun t ht => by
      dsimp only [Θm]
      rw [Set.IccExtend_of_mem (show (0 : ℝ) ≤ 1 by norm_num) θm ht]
      convert hliftm ⟨t, ht⟩ using 1 <;> congr 2 <;> ring)
  simpa [Θp, Θm] using hj

end RepulsiveCoulomb
