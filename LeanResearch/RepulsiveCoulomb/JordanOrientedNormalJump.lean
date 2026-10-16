module

public import LeanResearch.RepulsiveCoulomb.JordanNormalSegmentJump
public import LeanResearch.RepulsiveCoulomb.JordanSmoothTotalTurn

@[expose] public section

/-! Only global continuity and differentiability at one basepoint are needed.
A uniform interval of actual normal displacements has the same signed
argument jump. Rotation by the actual derivative identifies the plus point
with the geometric left normal, with no support-line assumption. Records-only
candidate, not compiled or admitted. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

/-- The normal segment radius is constructed from the actual simple loop.
The conclusion is stated as a strict distance margin at every other crossing
of the normal line, which directly implies branch-cut avoidance for the ratio. -/
theorem exists_locally_regular_simple_loop_normal_margin {γ : ℝ → ℂ}
    (hγ : Continuous γ) (hdiff : DifferentiableAt ℝ γ 0) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) (hbase : deriv γ 0 = 1) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, (γ t - γ 0).re = 0 → ε < ‖γ t - γ 0‖) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < (γ t - γ 0).re) ∧
      (∀ᶠ t in 𝓝[<] (1 : ℝ), (γ t - γ 0).re < 0) := by
  obtain ⟨δ, hδ, hδhalf, hright, hleft⟩ :=
    exists_horizontal_regular_crossing_radius
      hdiff hbase
  have hend (t : ℝ) (ht : t ∈ Ioo (1 - δ) 1) : (γ t - γ 0).re < 0 := by
    have h := hleft (t - 1) (by constructor <;> linarith [ht.1, ht.2])
    rwa [hp.sub_eq] at h
  let K := γ '' Icc δ (1 - δ)
  have hK : IsCompact K := isCompact_Icc.image hγ
  have hpK : γ 0 ∉ K := by
    rintro ⟨t, ht, heq⟩
    have htI : t ∈ Ico (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have he := hinj htI (show (0 : ℝ) ∈ Ico 0 1 by norm_num) heq
    linarith [ht.1]
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.mp (hK.isClosed.isOpen_compl.mem_nhds hpK)
  refine ⟨r / 2, by positivity, ?_, ?_, ?_⟩
  · intro t ht hre
    have htδ : δ ≤ t := by
      by_contra hn
      have h := hright t ⟨ht.1, lt_of_not_ge hn⟩
      rw [hre] at h
      exact (lt_irrefl 0) h
    have htend : t ≤ 1 - δ := by
      by_contra hn
      have h := hend t ⟨lt_of_not_ge hn, ht.2⟩
      rw [hre] at h
      exact (lt_irrefl 0) h
    have hrle : r ≤ dist (γ t) (γ 0) := by
      by_contra hn
      exact hrK (show γ t ∈ ball (γ 0) r from lt_of_not_ge hn) ⟨t, ⟨htδ, htend⟩, rfl⟩
    rw [dist_eq_norm] at hrle
    linarith
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hδ)] with t ht0 htδ
    exact hright t ⟨ht0, htδ⟩
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (lt_mem_nhds (show 1 - δ < (1 : ℝ) by linarith))] with t ht1 htδ
    exact hend t ⟨htδ, ht1⟩


/-- Constructed normal-segment geometry excludes both observation points from
an actual regular simple loop, and gives the signed jump for every pair of
actual continuous argument lifts. -/
theorem exists_simple_loop_uniform_normal_jump {γ : ℝ → ℂ}
    (hγ : Continuous γ) (hdiff : DifferentiableAt ℝ γ 0) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) (hbase : deriv γ 0 = 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
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
  obtain ⟨r, hr, hrmargin, hright, hleft⟩ :=
    exists_locally_regular_simple_loop_normal_margin hγ hdiff hp hinj hbase
  refine ⟨r, hr, ?_⟩
  intro ε hε hεr
  have hmargin : ∀ t ∈ Ioo (0 : ℝ) 1, (γ t - γ 0).re = 0 → ε < ‖γ t - γ 0‖ :=
    fun t ht he => hεr.trans_lt (hrmargin t ht he)
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
  refine ⟨havp, havm, ?_⟩
  intro θp θm hθp hθm hliftp hliftm
  let Θp := Set.IccExtend (show (0 : ℝ) ≤ 1 by norm_num) θp
  let Θm := Set.IccExtend (show (0 : ℝ) ≤ 1 by norm_num) θm
  have hΘp : Continuous Θp := (continuous_IccExtend_iff).mpr hθp
  have hΘm : Continuous Θm := (continuous_IccExtend_iff).mpr hθm
  have hj := normal_segment_argument_jump (v := fun t => γ t - γ 0)
    (hγ.sub continuous_const) (by simp) (by simp [hclose]) hε hmargin
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


/-- Subtracting the actual argument of a fixed nonzero divisor gives an
actual continuous argument lift for the quotient vector. -/
theorem argument_lift_div_constant {X : Type*} {v : X → ℂ} {θ : X → ℝ}
    {d : ℂ} (hd : d ≠ 0) (hv : ∀ x, v x ≠ 0)
    (hlift : ∀ x, Complex.exp ((θ x : ℂ) * Complex.I) = v x / (‖v x‖ : ℂ)) (x : X) :
    Complex.exp (((θ x - Complex.arg d : ℝ) : ℂ) * Complex.I) =
      (v x / d) / (‖v x / d‖ : ℂ) := by
  have hθ : Circle.exp (θ x) = euclideanDirection (v x) (hv x) := by
    apply Circle.ext
    exact hlift x
  have hdθ : Circle.exp (Complex.arg d) = euclideanDirection d hd := by
    rw [← euclideanDirection_arg d hd]
    exact Circle.exp_arg _
  have h : Circle.exp (θ x - Complex.arg d) = euclideanDirection (v x / d) (div_ne_zero (hv x) hd) := by
    rw [Circle.exp_sub, hθ, hdθ, euclideanDirection_div]
  exact congrArg (fun z : Circle => (z : ℂ)) h

/-- For the actual nonzero derivative `d`, the plus observation point is the
left normal `γ 0 + ε i d`. Every sufficiently small positive ε has signed jump
+2π from the right point to the left point. -/
theorem exists_simple_loop_oriented_normal_jump
    {γ : ℝ → ℂ} (hγ : Continuous γ) (hdiff : DifferentiableAt ℝ γ 0) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) (hd : deriv γ 0 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      let wp := γ 0 + (ε : ℂ) * Complex.I * deriv γ 0
      let wm := γ 0 - (ε : ℂ) * Complex.I * deriv γ 0
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ wp) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ wm) ∧
      ∀ (θp θm : Icc (0 : ℝ) 1 → ℝ), Continuous θp → Continuous θm →
        (∀ t, Complex.exp ((θp t : ℂ) * Complex.I) = (γ t - wp) / (‖γ t - wp‖ : ℂ)) →
        (∀ t, Complex.exp ((θm t : ℂ) * Complex.I) = (γ t - wm) / (‖γ t - wm‖ : ℂ)) →
        (θp 1 - θp 0) - (θm 1 - θm 0) = 2 * Real.pi := by
  let d := deriv γ 0
  let η : ℝ → ℂ := fun t => γ t / d
  have hη : Continuous η := hγ.div_const d
  have hdiffη : DifferentiableAt ℝ η 0 := hdiff.div_const d
  have hpη : Function.Periodic η 1 := by
    intro t
    change γ (t + 1) / d = γ t / d
    rw [hp]
  have hinjη : InjOn η (Ico (0 : ℝ) 1) := by
    intro s hs t ht heq
    apply hinj hs ht
    exact (div_left_inj' hd).mp heq
  have hbaseη : deriv η 0 = 1 := by
    change deriv (fun t => γ t / d) 0 = 1
    rw [deriv_div_const]
    exact div_self hd
  obtain ⟨r, hr, hall⟩ := exists_simple_loop_uniform_normal_jump hη hdiffη hpη hinjη hbaseη
  refine ⟨r, hr, ?_⟩
  intro ε hε hεr
  dsimp only
  let wp := γ 0 + (ε : ℂ) * Complex.I * deriv γ 0
  let wm := γ 0 - (ε : ℂ) * Complex.I * deriv γ 0
  obtain ⟨hpavoid, hmavoid, hjump⟩ := hall ε hε hεr
  have hep (t : ℝ) : (γ t - wp) / d = η t - (η 0 + (ε : ℂ) * Complex.I) := by
    dsimp [wp, d, η]
    field_simp [hd]
  have hem (t : ℝ) : (γ t - wm) / d = η t - (η 0 - (ε : ℂ) * Complex.I) := by
    dsimp [wm, d, η]
    field_simp [hd]
  have havp : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ wp := by
    intro t ht heq
    apply hpavoid t ht
    apply sub_eq_zero.mp
    rw [← hep, heq, sub_self, zero_div]
  have havm : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ wm := by
    intro t ht heq
    apply hmavoid t ht
    apply sub_eq_zero.mp
    rw [← hem, heq, sub_self, zero_div]
  refine ⟨havp, havm, ?_⟩
  intro θp θm hθp hθm hliftp hliftm
  have hj := hjump (fun t => θp t - Complex.arg d) (fun t => θm t - Complex.arg d)
    (hθp.sub continuous_const) (hθm.sub continuous_const)
    (fun t => by
      have hq := argument_lift_div_constant (v := fun s : Icc (0 : ℝ) 1 => γ s - wp)
        (θ := θp) hd (fun s => sub_ne_zero.mpr (havp s s.2)) hliftp t
      rw [hep] at hq
      exact hq)
    (fun t => by
      have hq := argument_lift_div_constant (v := fun s : Icc (0 : ℝ) 1 => γ s - wm)
        (θ := θm) hd (fun s => sub_ne_zero.mpr (havm s s.2)) hliftm t
      rw [hem] at hq
      exact hq)
  linarith

end RepulsiveCoulomb
