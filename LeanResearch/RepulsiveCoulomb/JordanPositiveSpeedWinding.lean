import LeanResearch.RepulsiveCoulomb.JordanSupportedWinding

/-! The actual signed inside/outside classification needs only positive real
velocity at the horizontal support, rather than velocity exactly 1. The
normal-segment radius and signed jump are reconstructed from that derivative.
This removes a spatial normalization and its component-transport bookkeeping.
Records-only draft, not compiled or admitted. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

/-- A positive horizontal derivative gives the actual oriented crossing signs
in a neighborhood of the basepoint. -/
theorem exists_positive_real_crossing_radius {γ : ℝ → ℂ}
    (hγ : DifferentiableAt ℝ γ 0) (hbase : 0 < (deriv γ 0).re) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      (∀ t ∈ Ioo (0 : ℝ) δ, 0 < (γ t - γ 0).re) ∧
      (∀ t ∈ Ioo (-δ) (0 : ℝ), (γ t - γ 0).re < 0) := by
  let f : ℝ → ℝ := fun t => (γ t).re
  have hdf : HasDerivAt f (deriv γ 0).re 0 := by
    simpa only [f, Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ.hasDerivAt
  have hlim : Tendsto (dslope f 0) (𝓝 0) (𝓝 (deriv γ 0).re) := by
    simpa only [dslope_same, hdf.deriv] using
      (continuousAt_dslope_same.mpr hdf.differentiableAt).tendsto
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < dslope f 0 t := hlim (Ioi_mem_nhds hbase)
  obtain ⟨r, hr, hnear⟩ := Metric.eventually_nhds_iff.mp hpos
  let δ := min r (1 / 4 : ℝ)
  have hδ : 0 < δ := lt_min hr (by norm_num)
  have hδr : δ ≤ r := min_le_left _ _
  have hδhalf : δ < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨δ, hδ, hδhalf, ?_, ?_⟩
  · intro t ht
    have hdist : dist t 0 < r := by rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]; exact ht.2.trans_le hδr
    have h := hnear hdist
    rw [dslope_of_ne _ ht.1.ne', slope_def_field, sub_zero] at h
    have hp := (div_pos_iff_of_pos_right ht.1).mp h
    simpa only [f, Complex.sub_re] using hp
  · intro t ht
    have hdist : dist t 0 < r := by rw [Real.dist_eq, sub_zero, abs_of_neg ht.2]; linarith [ht.1]
    have h := hnear hdist
    rw [dslope_of_ne _ ht.2.ne, slope_def_field, sub_zero] at h
    rcases div_pos_iff.mp h with hplus | hminus
    · exact (lt_asymm hplus.2 ht.2).elim
    · simpa only [f, Complex.sub_re] using hminus.1

/-- The normal segment radius is constructed from the actual simple loop.
The conclusion is stated as a strict distance margin at every other crossing
of the normal line, which directly implies branch-cut avoidance for the ratio. -/
theorem exists_positive_real_simple_loop_normal_margin {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) (hbase : 0 < (deriv γ 0).re) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, (γ t - γ 0).re = 0 → ε < ‖γ t - γ 0‖) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < (γ t - γ 0).re) ∧
      (∀ᶠ t in 𝓝[<] (1 : ℝ), (γ t - γ 0).re < 0) := by
  obtain ⟨δ, hδ, hδhalf, hright, hleft⟩ :=
    exists_positive_real_crossing_radius
      ((hγ.differentiable (by norm_num)) 0) hbase
  have hend (t : ℝ) (ht : t ∈ Ioo (1 - δ) 1) : (γ t - γ 0).re < 0 := by
    have h := hleft (t - 1) (by constructor <;> linarith [ht.1, ht.2])
    rwa [hp.sub_eq] at h
  let K := γ '' Icc δ (1 - δ)
  have hK : IsCompact K := isCompact_Icc.image hγ.continuous
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
theorem exists_positive_real_simple_loop_normal_jump {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) (hbase : 0 < (deriv γ 0).re) :
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
    exists_positive_real_simple_loop_normal_margin hγ hp hinj hbase
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


/-- Every actual argument lift about a point in the bounded Jordan component
has increment +2π for the same supported orientation whose tangent turn is+2π.
Every actual argument lift about the outside has increment0. -/
theorem positive_real_supported_loop_actual_winding
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) (hbase : 0 < (deriv γ 0).re)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (γ t - γ 0).im)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V)
    (hK : IsCompact (closure U))
    (hfront : frontier U = γ '' Icc (0 : ℝ) 1)
    (hcover : U ∪ V = (γ '' Icc (0 : ℝ) 1)ᶜ) :
    (∀ w ∈ U, ∀ θ : Icc (0 : ℝ) 1 → ℝ, Continuous θ →
      (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
        (γ t - w) / (‖γ t - w‖ : ℂ)) → θ 1 - θ 0 = 2 * Real.pi) ∧
    (∀ w ∈ V, ∀ θ : Icc (0 : ℝ) 1 → ℝ, Continuous θ →
      (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
        (γ t - w) / (‖γ t - w‖ : ℂ)) → θ 1 - θ 0 = 0) := by
  let Γ : Icc (0 : ℝ) 1 → ℂ := fun t => γ t
  have hΓ : Continuous Γ := hγ.continuous.comp continuous_subtype_val
  have hΓclose : Γ 0 = Γ 1 := by simpa [Γ] using (hp 0).symm
  have himage : range Γ = γ '' Icc (0 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  have hcoverΓ : U ∪ V = (range Γ)ᶜ := by rwa [himage]
  have houtside : ∀ w ∈ V, ∀ θ : Icc (0 : ℝ) 1 → ℝ, Continuous θ →
      (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
        (Γ t - w) / (‖Γ t - w‖ : ℂ)) → θ 1 - θ 0 = 0 := by
    intro w hw θ hθ hlift
    exact jordan_outside_argument_increment_zero Γ hΓ hΓclose hK hV hVc hcoverΓ hw θ hθ hlift
  refine ⟨?_, houtside⟩
  obtain ⟨ε, hε, havp, havm, hjump⟩ :=
    exists_positive_real_simple_loop_normal_jump hγ hp hinj hbase
  let wp := γ 0 + (ε : ℂ) * Complex.I
  let wm := γ 0 - (ε : ℂ) * Complex.I
  have hwpC : wp ∉ range Γ := by
    rintro ⟨t, heq⟩
    exact havp t t.2 heq
  have hwmC : wm ∉ range Γ := by
    rintro ⟨t, heq⟩
    exact havm t t.2 heq
  have hwmU : wm ∉ U := by
    intro hwm
    have hside := bounded_jordan_region_above_support hU hK hfront hsupport wm hwm
    simp only [wm, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero] at hside
    linarith
  have hwmV : wm ∈ V := by
    have h : wm ∈ U ∪ V := hcoverΓ.symm ▸ hwmC
    exact h.elim (fun hu => (hwmU hu).elim) id
  obtain ⟨θp, hθp, hθplift⟩ := exists_interval_euclidean_angle_lift
    (hΓ.sub continuous_const) (fun t => sub_ne_zero.mpr (havp t t.2))
  obtain ⟨θm, hθm, hθmlift⟩ := exists_interval_euclidean_angle_lift
    (hΓ.sub continuous_const) (fun t => sub_ne_zero.mpr (havm t t.2))
  have hθmzero := houtside wm hwmV θm hθm hθmlift
  have hj := hjump θp θm hθp hθm hθplift hθmlift
  have hθpturn : θp 1 - θp 0 = 2 * Real.pi := by linarith
  have hwpU : wp ∈ U := by
    have h : wp ∈ U ∪ V := hcoverΓ.symm ▸ hwpC
    rcases h with hu | hv
    · exact hu
    · have hz := houtside wp hv θp hθp hθplift
      nlinarith [Real.pi_pos]
  have havoid : ∀ w ∈ U, ∀ t, Γ t ≠ w := by
    intro w hw t heq
    have hnot : w ∈ (range Γ)ᶜ := hcoverΓ ▸ Or.inl hw
    exact hnot ⟨t, heq⟩
  intro w hw θ hθ hlift
  have heq := loop_argument_increment_constant_on_component Γ hΓ hΓclose
    hU hUc havoid hw hwpU θ θp hθ hθp hlift hθplift
  exact heq.trans hθpturn


end RepulsiveCoulomb
