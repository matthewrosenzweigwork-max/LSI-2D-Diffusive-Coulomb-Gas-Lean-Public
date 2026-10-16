module

public import LeanResearch.RepulsiveCoulomb.PointLineCapJordan
public import LeanResearch.RepulsiveCoulomb.PointLineCapPositiveOrientation
public import LeanResearch.RepulsiveCoulomb.JordanFiniteCornerPointWinding

@[expose] public section

/-! Records-only, uncompiled. An explicit two-arc periodic realization of the
cap, based at the circle midpoint, proves its positive orientation before any
finite-corner smoothing. No winding/turn value is supplied as a hypothesis. -/
noncomputable section
open Set Filter Topology
namespace RepulsiveCoulomb

def lineCapTwoArcPaste (f g : ℝ → ℂ) (t : ℝ) : ℂ :=
  if t ≤ 1 / 2 then f (2 * t) else g (2 * t - 1)

theorem lineCapTwoArcPaste_left (f g : ℝ → ℂ) {t : ℝ} (ht : t ≤ 1 / 2) :
    lineCapTwoArcPaste f g t = f (2 * t) := if_pos ht

theorem lineCapTwoArcPaste_right {f g : ℝ → ℂ} (hjoin : f 1 = g 0)
    {t : ℝ} (ht : 1 / 2 ≤ t) : lineCapTwoArcPaste f g t = g (2 * t - 1) := by
  by_cases he : t = 1 / 2
  · subst t
    simpa [lineCapTwoArcPaste] using hjoin
  · exact if_neg (not_le.mpr (lt_of_le_of_ne ht (Ne.symm he)))

theorem lineCapTwoArcPaste_continuous {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hjoin : f 1 = g 0) :
    Continuous (lineCapTwoArcPaste f g) := by
  apply Continuous.if_le (hf.comp (continuous_const.mul continuous_id))
    (hg.comp ((continuous_const.mul continuous_id).sub continuous_const))
    continuous_id continuous_const
  intro t ht
  change t = 1 / 2 at ht
  subst t
  simpa using hjoin

theorem lineCapTwoArcPaste_injOn {f g : ℝ → ℂ} (hjoin : f 1 = g 0)
    (hf : InjOn f (Icc (0 : ℝ) 1)) (hg : InjOn g (Icc (0 : ℝ) 1))
    (hdisj : Disjoint (f '' Ico (0 : ℝ) 1) (g '' Ico (0 : ℝ) 1)) :
    InjOn (lineCapTwoArcPaste f g) (Ico (0 : ℝ) 1) := by
  intro s hs t ht he
  by_cases hsl : s < 1 / 2 <;> by_cases htl : t < 1 / 2
  · rw [lineCapTwoArcPaste_left f g hsl.le, lineCapTwoArcPaste_left f g htl.le] at he
    have h := hf (by constructor <;> linarith [hs.1])
      (by constructor <;> linarith [ht.1]) he
    linarith
  · rw [lineCapTwoArcPaste_left f g hsl.le,
      lineCapTwoArcPaste_right hjoin (le_of_not_gt htl)] at he
    exact False.elim (disjoint_left.mp hdisj
      ⟨2 * s, by constructor <;> linarith [hs.1], rfl⟩
      ⟨2 * t - 1, by constructor <;> linarith [ht.2], he.symm⟩)
  · rw [lineCapTwoArcPaste_right hjoin (le_of_not_gt hsl),
      lineCapTwoArcPaste_left f g htl.le] at he
    exact False.elim (disjoint_left.mp hdisj
      ⟨2 * t, by constructor <;> linarith [ht.1], he.symm⟩
      ⟨2 * s - 1, by constructor <;> linarith [hs.2], rfl⟩)
  · rw [lineCapTwoArcPaste_right hjoin (le_of_not_gt hsl),
      lineCapTwoArcPaste_right hjoin (le_of_not_gt htl)] at he
    have h := hg (by constructor <;> linarith [hs.2])
      (by constructor <;> linarith [ht.2]) he
    linarith

theorem lineCapTwoArcPaste_image {f g : ℝ → ℂ} (hjoin : f 1 = g 0) :
    lineCapTwoArcPaste f g '' Icc (0 : ℝ) 1 =
      f '' Icc (0 : ℝ) 1 ∪ g '' Icc (0 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases hl : t ≤ 1 / 2
    · exact Or.inl ⟨2 * t, by constructor <;> linarith [ht.1],
        (lineCapTwoArcPaste_left f g hl).symm⟩
    · exact Or.inr ⟨2 * t - 1, by constructor <;> linarith [ht.2],
        (lineCapTwoArcPaste_right hjoin (le_of_not_ge hl)).symm⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · refine ⟨t / 2, by constructor <;> linarith [ht.1, ht.2], ?_⟩
      rw [lineCapTwoArcPaste_left f g (by linarith [ht.2])]
      congr 1
      ring
    · refine ⟨(t + 1) / 2, by constructor <;> linarith [ht.1, ht.2], ?_⟩
      rw [lineCapTwoArcPaste_right hjoin (by linarith [ht.1])]
      congr 1
      ring

/-- The local derivative retains the positive parameter speed, a necessary
fact for transporting the physical left normal between cap parametrizations. -/
theorem lineCapTwoArcPaste_hasDerivAt_left {f g : ℝ → ℂ} {a : ℝ} {v : ℂ}
    (ha : a < 1 / 2) (hf : HasDerivAt f v (2 * a)) :
    HasDerivAt (lineCapTwoArcPaste f g) (2 • v) a := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 a := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id a).const_mul 2
  rw [← Nat.cast_smul_eq_nsmul ℝ 2 v]
  apply (hf.scomp a hlin).congr_of_eventuallyEq
  filter_upwards [gt_mem_nhds ha] with t ht
  exact lineCapTwoArcPaste_left f g ht.le

theorem lineCapTwoArcPaste_hasDerivAt_right {f g : ℝ → ℂ} {a : ℝ} {v : ℂ}
    (ha : 1 / 2 < a) (hg : HasDerivAt g v (2 * a - 1)) :
    HasDerivAt (lineCapTwoArcPaste f g) (2 • v) a := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * t - 1) 2 a := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id a).const_mul 2).sub_const 1
  rw [← Nat.cast_smul_eq_nsmul ℝ 2 v]
  apply (hg.scomp a hlin).congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ha] with t ht
  exact if_neg (not_le.mpr ht)

def lineCapPeriodic (c : ℝ → ℂ) (tm tp R α β b t : ℝ) : ℂ :=
  pointContinuousPeriodize
    (lineCapTwoArcPaste (pointCircleCapArc R α β) (fun u => c (tm + u * (tp - tm))))
    (t + b)

/-- A literal cap supplies a positively oriented continuous simple periodic
loop. Circle smoothness alone supplies its regular basepoint, even when the
line passes through positive atoms. -/
theorem exists_lineCap_positive_periodic_realization {c : ℝ → ℂ}
    (hc : Continuous c) (hi : Function.Injective c)
    {tm tp R α β : ℝ} (ht : tm < tp) (hR : 0 < R)
    (hab : α < β) (hwidth : β < α + 2 * Real.pi)
    (hcross : ∀ t, ‖c t‖ = R ↔ t = tm ∨ t = tp)
    (hzero : pointCircleCapArc R α β 0 = c tp)
    (hone : pointCircleCapArc R α β 1 = c tm)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hK : IsCompact (closure U))
    (hcover : U ∪ V = (c '' Icc tm tp ∪ pointCircleCapArc R α β '' Icc (0 : ℝ) 1)ᶜ)
    (hball : U ⊆ Metric.ball (0 : ℂ) R) :
    ∃ Γ : ℝ → ℂ, Γ = lineCapPeriodic c tm tp R α β (1 / 4) ∧
      Continuous Γ ∧ Function.Periodic Γ 1 ∧
      InjOn Γ (Ico (0 : ℝ) 1) ∧ DifferentiableAt ℝ Γ 0 ∧ deriv Γ 0 ≠ 0 ∧
      Γ '' Icc (0 : ℝ) 1 = c '' Icc tm tp ∪ pointCircleCapArc R α β '' Icc (0 : ℝ) 1 ∧
      (∀ w ∈ U, ∀ θ : Icc (0 : ℝ) 1 → ℝ, Continuous θ →
        (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
          (Γ t - w) / (‖Γ t - w‖ : ℂ)) → θ 1 - θ 0 = 2 * Real.pi) := by
  let f := pointCircleCapArc R α β
  let g : ℝ → ℂ := fun t => c (tm + t * (tp - tm))
  have hf : Continuous f := (pointCircleCapArc_smooth R α β).continuous
  have hg : Continuous g := hc.comp (continuous_const.add (continuous_id.mul continuous_const))
  have hj : f 1 = g 0 := by simpa [f, g] using hone
  have hcl : g 1 = f 0 := by simpa [f, g] using hzero.symm
  have hgi : InjOn g (Icc (0 : ℝ) 1) := by
    intro s hs t ht' he
    have h := hi he
    nlinarith [sub_pos.mpr ht]
  have hfi := lineCapArc_injOn hR hab hwidth
  have hmeet := lineCapSegment_circle_intersection hR ht hcross hzero hone
  have hd0 := lineCap_halfOpen_disjoint (lineCapSegment_injective hi ht) hfi
    (lineCapSegment_zero c tm tp) (lineCapSegment_one c tm tp) hzero hone hmeet
  have hdg : Disjoint (f '' Ico (0 : ℝ) 1) (g '' Ico (0 : ℝ) 1) := by
    apply hd0.symm.mono_right
    rintro z ⟨t, ht', rfl⟩
    exact ⟨⟨t, ht'.1, ht'.2.le⟩, ht', rfl⟩
  let F := lineCapTwoArcPaste f g
  have hF := lineCapTwoArcPaste_continuous hf hg hj
  have hFi := lineCapTwoArcPaste_injOn hj hfi hgi hdg
  have hFcl : F 0 = F 1 := by
    change lineCapTwoArcPaste f g 0 = lineCapTwoArcPaste f g 1
    rw [lineCapTwoArcPaste_left f g (t := 0) (by norm_num),
      lineCapTwoArcPaste_right hj (t := 1) (by norm_num)]
    simpa only [mul_zero, mul_one, show (2 - 1 : ℝ) = 1 by norm_num] using hcl.symm
  have hgimage : g '' Icc (0 : ℝ) 1 = c '' Icc tm tp := by
    rw [← lineCapSegment_range c ht]
    ext z
    constructor
    · rintro ⟨t, ht', rfl⟩; exact ⟨⟨t, ht'⟩, rfl⟩
    · rintro ⟨t, rfl⟩; exact ⟨t.1, t.2, rfl⟩
  have hFimage : F '' Icc (0 : ℝ) 1 =
      c '' Icc tm tp ∪ pointCircleCapArc R α β '' Icc (0 : ℝ) 1 := by
    rw [lineCapTwoArcPaste_image hj, hgimage, union_comm]
  have hDf : HasDerivAt f ((β - α) • (Complex.I * f (1 / 2))) (2 * (1 / 4)) := by
    convert hasDerivAt_pointCircleCapArc R α β (1 / 2) using 1 <;> norm_num
  have hDF := lineCapTwoArcPaste_hasDerivAt_left (g := g) (by norm_num : (1 / 4 : ℝ) < 1 / 2) hDf
  have hDFne : deriv F (1 / 4) ≠ 0 := by
    rw [hDF.deriv]
    exact smul_ne_zero (by norm_num) (smul_ne_zero (sub_pos.mpr hab).ne'
      (mul_ne_zero Complex.I_ne_zero (norm_pos_iff.mp (by
        rw [pointCircleCapArc_norm hR.le]; exact hR))))
  let Γ : ℝ → ℂ := fun t => pointContinuousPeriodize F (t + 1 / 4)
  have hΓ : Continuous Γ := (pointContinuousPeriodize_continuous hF.continuousOn hFcl).comp
    (continuous_id.add_const (1 / 4))
  have hpP := pointContinuousPeriodize_periodic F
  have hpΓ : Function.Periodic Γ 1 := by
    intro t
    change pointContinuousPeriodize F (t + 1 + 1 / 4) = pointContinuousPeriodize F (t + 1 / 4)
    rw [show t + 1 + 1 / 4 = (t + 1 / 4) + 1 by ring, hpP]
  have hiΓ : InjOn Γ (Ico (0 : ℝ) 1) := periodic_simple_loop_shift_injOn hpP
    (pointContinuousPeriodize_injOn hFi) (by norm_num : (1 / 4 : ℝ) ∈ Icc 0 1)
  have hshift : Tendsto (fun t : ℝ => t + 1 / 4) (𝓝 0) (𝓝 (1 / 4)) := by
    simpa only [id_eq, zero_add] using (continuous_id.add_const (1 / 4 : ℝ)).tendsto 0
  have hlocal : Γ =ᶠ[𝓝 0] (fun t => F (t + 1 / 4)) :=
    (pointContinuousPeriodize_eventually_eq F (by norm_num : (1 / 4 : ℝ) ∈ Ioo 0 1)).comp_tendsto hshift
  have hbasef : Γ 0 = f (1 / 2) := by
    rw [hlocal.self_of_nhds]
    change lineCapTwoArcPaste f g (0 + 1 / 4) = f (1 / 2)
    rw [zero_add, lineCapTwoArcPaste_left f g (t := 1 / 4) (by norm_num)]
    congr 1
    norm_num
  have himΓ : Γ '' Icc (0 : ℝ) 1 = F '' Icc (0 : ℝ) 1 := by
    rw [periodic_closed_interval_image_shift hpP (1 / 4)]
    exact (show EqOn (pointContinuousPeriodize F) F (Icc (0 : ℝ) 1) from
      fun t ht' => pointContinuousPeriodize_eq_Icc hFcl ht').image_eq
  have hDΓ : HasDerivAt Γ (2 • ((β - α) • (Complex.I * f (1 / 2)))) 0 := by
    have hd' : HasDerivAt F (2 • ((β - α) • (Complex.I * f (1 / 2)))) (0 + 1 / 4) := by
      simpa only [zero_add] using hDF
    exact (hd'.comp_add_const 0 (1 / 4)).congr_of_eventuallyEq hlocal
  have hdΓ : DifferentiableAt ℝ Γ 0 := hDΓ.differentiableAt
  have hnΓ : deriv Γ 0 ≠ 0 := by
    rw [hDΓ.deriv]
    rw [hDF.deriv] at hDFne
    exact hDFne
  have hvel : deriv Γ 0 = (2 * (β - α)) • (Complex.I * Γ 0) := by
    rw [hDΓ.deriv, hbasef, ← Nat.cast_smul_eq_nsmul ℝ 2 ((β - α) • (Complex.I * f (1 / 2))), smul_smul]
    norm_num
  have hnorm : ‖Γ 0‖ = R := by rw [hbasef]; exact pointCircleCapArc_norm hR.le α β (1 / 2)
  have him : Γ '' Icc (0 : ℝ) 1 =
      c '' Icc tm tp ∪ pointCircleCapArc R α β '' Icc (0 : ℝ) 1 := himΓ.trans hFimage
  refine ⟨Γ, rfl, hΓ, hpΓ, hiΓ, hdΓ, hnΓ, him, ?_⟩
  exact lineCap_positive_inside_winding_of_circle_basepoint hΓ hdΓ hpΓ hiΓ hnΓ hR
    (mul_pos (by norm_num) (sub_pos.mpr hab)) hnorm hvel hU hUc hV hVc hK
    (by rwa [him]) hball

end RepulsiveCoulomb
