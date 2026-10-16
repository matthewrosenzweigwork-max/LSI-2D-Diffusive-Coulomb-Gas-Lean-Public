module

public import LeanResearch.RepulsiveCoulomb.PointLineCapPeriodization
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! Records-only, uncompiled. Positive winding is transported from the actual
circle midpoint to a fixed regular point of the oriented line. The resulting
normal interval is constructed, not supplied as a cap-side certificate. -/
noncomputable section
open Set Filter Topology
namespace RepulsiveCoulomb

/-- Every actual cap contains an interval of the SAME physical left normal
at any fixed regular line parameter between its two crossings. The radius may
depend on the cap; overlap suffices to identify the fixed global side. -/
theorem exists_lineCap_fixed_left_normal {c : ℝ → ℂ}
    (hc : Continuous c) (hi : Function.Injective c)
    {tm tp R α β s : ℝ} (ht : tm < tp) (hR : 0 < R)
    (hab : α < β) (hwidth : β < α + 2 * Real.pi)
    (hcross : ∀ t, ‖c t‖ = R ↔ t = tm ∨ t = tp)
    (hzero : pointCircleCapArc R α β 0 = c tp)
    (hone : pointCircleCapArc R α β 1 = c tm)
    (hs : s ∈ Ioo tm tp) (hds : DifferentiableAt ℝ c s) (hvs : deriv c s ≠ 0)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hK : IsCompact (closure U))
    (hcover : U ∪ V = (c '' Icc tm tp ∪ pointCircleCapArc R α β '' Icc (0 : ℝ) 1)ᶜ)
    (hball : U ⊆ Metric.ball (0 : ℂ) R) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε, 0 < ε → ε ≤ r →
      c s + (ε : ℂ) * Complex.I * deriv c s ∈ U := by
  obtain ⟨Γ, hΓdef, hΓ, hpΓ, hiΓ, _, _, himΓ, hpositive⟩ :=
    exists_lineCap_positive_periodic_realization hc hi ht hR hab hwidth hcross
      hzero hone hU hUc hV hVc hK hcover hball
  let d := tp - tm
  have hd : 0 < d := sub_pos.mpr ht
  let u := (s - tm) / d
  have hu : u ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr hs.1) hd, (div_lt_one hd).mpr (by dsimp [d]; linarith [hs.2])⟩
  let b := (1 + u) / 2
  have hb : b ∈ Ioo (0 : ℝ) 1 := by dsimp [b]; constructor <;> linarith [hu.1, hu.2]
  have hhalf : 1 / 2 < b := by dsimp [b]; linarith [hu.1]
  let δ := b - 1 / 4
  have hδ : δ ∈ Icc (0 : ℝ) 1 := by dsimp [δ]; constructor <;> linarith [hb.2]
  let Λ : ℝ → ℂ := fun t => Γ (t + δ)
  have hΛ : Continuous Λ := hΓ.comp (continuous_id.add_const δ)
  have hpΛ : Function.Periodic Λ 1 := by
    intro t
    change Γ (t + 1 + δ) = Γ (t + δ)
    rw [show t + 1 + δ = (t + δ) + 1 by ring, hpΓ]
  have hiΛ : InjOn Λ (Ico (0 : ℝ) 1) := periodic_simple_loop_shift_injOn hpΓ hiΓ hδ
  have himΛ : Λ '' Icc (0 : ℝ) 1 = Γ '' Icc (0 : ℝ) 1 :=
    periodic_closed_interval_image_shift hpΓ δ
  let f := pointCircleCapArc R α β
  let g : ℝ → ℂ := fun t => c (tm + t * d)
  let F := lineCapTwoArcPaste f g
  have htime : tm + (2 * b - 1) * d = s := by
    dsimp [b, u]
    field_simp [hd.ne']
    ring
  have hlin : HasDerivAt (fun t : ℝ => tm + t * d) d (2 * b - 1) := by
    simpa only [id_eq, one_mul] using ((hasDerivAt_id (2 * b - 1)).mul_const d).const_add tm
  have hcg : HasDerivAt c (deriv c s) (tm + (2 * b - 1) * d) := by
    rw [htime]
    exact hds.hasDerivAt
  have hgD : HasDerivAt g (d • deriv c s) (2 * b - 1) := hcg.scomp (h := fun t : ℝ => tm + t * d) (2 * b - 1) hlin
  have hFD : HasDerivAt F (2 • (d • deriv c s)) b :=
    lineCapTwoArcPaste_hasDerivAt_right hhalf hgD
  have hΛeq : Λ =ᶠ[𝓝 0] (fun t => F (t + b)) := by
    have hshift : Tendsto (fun t : ℝ => t + b) (𝓝 0) (𝓝 b) := by
      simpa only [id_eq, zero_add] using (continuous_id.add_const b).tendsto 0
    have hlocal := (pointContinuousPeriodize_eventually_eq F hb).comp_tendsto hshift
    filter_upwards [hlocal] with t ht'
    change Γ (t + δ) = F (t + b)
    rw [hΓdef]
    change pointContinuousPeriodize F ((t + δ) + 1 / 4) = F (t + b)
    rw [show (t + δ) + 1 / 4 = t + b by dsimp [δ]; ring]
    exact ht'
  have hΛD : HasDerivAt Λ (2 • (d • deriv c s)) 0 := by
    have hFD' : HasDerivAt F (2 • (d • deriv c s)) (0 + b) := by simpa only [zero_add] using hFD
    exact (hFD'.comp_add_const 0 b).congr_of_eventuallyEq hΛeq
  have hΛbase : Λ 0 = c s := by
    rw [hΛeq.self_of_nhds]
    change lineCapTwoArcPaste f g (0 + b) = c s
    rw [zero_add, lineCapTwoArcPaste, if_neg (not_le.mpr hhalf)]
    exact congrArg c htime
  have hΛne : deriv Λ 0 ≠ 0 := by
    rw [hΛD.deriv]
    exact smul_ne_zero (by norm_num) (smul_ne_zero hd.ne' hvs)
  obtain ⟨w, hw⟩ := hUc.nonempty
  have hwΓ : w ∉ Γ '' Icc (0 : ℝ) 1 := by
    rw [himΓ]
    have hwUV : w ∈ U ∪ V := Or.inl hw
    rw [hcover] at hwUV
    exact hwUV
  have hwΛ : w ∉ Λ '' Icc (0 : ℝ) 1 := by rwa [himΛ]
  obtain ⟨θ, hθ, hθl⟩ := exists_interval_euclidean_angle_lift
    ((hΓ.comp continuous_subtype_val).sub continuous_const)
    (fun t => sub_ne_zero.mpr (fun he => hwΓ ⟨t, t.2, he⟩))
  obtain ⟨ψ, hψ, hψl⟩ := exists_interval_euclidean_angle_lift
    ((hΛ.comp continuous_subtype_val).sub continuous_const)
    (fun t => sub_ne_zero.mpr (fun he => hwΛ ⟨t, t.2, he⟩))
  have hturn : ψ 1 - ψ 0 = 2 * Real.pi :=
    (periodic_point_argument_increment_shift Γ hΓ hpΓ δ hwΓ θ ψ hθ hψ hθl hψl).symm.trans
      (hpositive w hw θ hθ hθl)
  obtain ⟨r, hr, hnormal⟩ := positive_inside_argument_forces_left_normal hΛ hΛD.differentiableAt
    hpΛ hiΛ hΛne hU hUc hV hVc hK (by rwa [himΛ, himΓ]) hw hψ hψl hturn
  let k := 2 * d
  have hk : 0 < k := mul_pos (by norm_num) hd
  refine ⟨r * k, mul_pos hr hk, ?_⟩
  intro ε hε hεr
  have hη : 0 < ε / k := div_pos hε hk
  have hηr : ε / k ≤ r := (div_le_iff₀ hk).mpr hεr
  have h := (hnormal (ε / k) hη hηr).1
  rw [hΛbase, hΛD.deriv, ← Nat.cast_smul_eq_nsmul ℝ 2 (d • deriv c s), smul_smul] at h
  convert h using 1
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul]
  dsimp [k]
  field_simp [Complex.ofReal_ne_zero.mpr hd.ne'] <;> push_cast <;> ring

end RepulsiveCoulomb
