module

public import LeanResearch.RepulsiveCoulomb.JordanSmoothSupportedTurn
public import Mathlib.Analysis.Calculus.DSlope

@[expose] public section

/-! An actual small normal segment at the basepoint of a regular simple
periodic loop meets its trace only at that basepoint. Near the two parameter
ends, the actual real coordinate has opposite signs; the rest of the trace is
excluded by compact separation. Records-only phase-five candidate. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

/-- A positive horizontal derivative gives the actual oriented crossing signs
in a neighborhood of the basepoint. -/
theorem exists_horizontal_regular_crossing_radius {γ : ℝ → ℂ}
    (hγ : DifferentiableAt ℝ γ 0) (hbase : deriv γ 0 = 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      (∀ t ∈ Ioo (0 : ℝ) δ, 0 < (γ t - γ 0).re) ∧
      (∀ t ∈ Ioo (-δ) (0 : ℝ), (γ t - γ 0).re < 0) := by
  let f : ℝ → ℝ := fun t => (γ t).re
  have hdγ : HasDerivAt γ 1 0 := by simpa only [hbase] using hγ.hasDerivAt
  have hdf : HasDerivAt f 1 0 := by
    simpa only [f, Function.comp_def, Complex.reCLM_apply, Complex.one_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hdγ
  have hlim : Tendsto (dslope f 0) (𝓝 0) (𝓝 (1 : ℝ)) := by
    simpa only [dslope_same, hdf.deriv] using
      (continuousAt_dslope_same.mpr hdf.differentiableAt).tendsto
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < dslope f 0 t := hlim (Ioi_mem_nhds zero_lt_one)
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
theorem exists_simple_loop_normal_segment_margin {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) (hbase : deriv γ 0 = 1) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, (γ t - γ 0).re = 0 → ε < ‖γ t - γ 0‖) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < (γ t - γ 0).re) ∧
      (∀ᶠ t in 𝓝[<] (1 : ℝ), (γ t - γ 0).re < 0) := by
  obtain ⟨δ, hδ, hδhalf, hright, hleft⟩ :=
    exists_horizontal_regular_crossing_radius
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

end RepulsiveCoulomb
