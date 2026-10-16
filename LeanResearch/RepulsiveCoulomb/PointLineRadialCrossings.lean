module

public import LeanResearch.RepulsiveCoulomb.PointMetricRaySegments
public import LeanResearch.RepulsiveCoulomb.CircleTransverseCorner
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Records-only, uncompiled. Large-circle crossings are constructed from actual
radial-component inequalities. No crossing, cap, or turning certificate is an
input. The tail inequalities themselves are deliberately explicit hypotheses. -/
noncomputable section
open Set Filter Topology
namespace RepulsiveCoulomb

theorem lineCap_hasDerivAt_norm_sq {c : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (h : HasDerivAt c v t) :
    HasDerivAt (fun s => ‖c s‖ ^ 2) (2 * physicalRadialProjection (c t) v) t := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h
  convert (hr.mul hr).add (hi.mul hi) using 1
  · ext s
    change ‖c s‖ ^ 2 = (c s).re * (c s).re + (c s).im * (c s).im
    simp only [Complex.sq_norm, Complex.normSq_apply]
  · change 2 * ((c t).re * v.re + (c t).im * v.im) =
      (v.re * (c t).re + (c t).re * v.re) + (v.im * (c t).im + (c t).im * v.im)
    ring

theorem lineCap_strictMono_norm_of_radial_pos {c : ℝ → ℂ} (hc : Continuous c)
    {T : ℝ} (hd : ∀ t, T < t → DifferentiableAt ℝ c t)
    (hr : ∀ t, T < t → 0 < physicalRadialProjection (c t) (deriv c t)) :
    StrictMonoOn (fun t => ‖c t‖) (Ici T) := by
  have hs : StrictMonoOn (fun t => ‖c t‖ ^ 2) (Ici T) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici T) (hc.norm.pow 2).continuousOn
    intro t ht
    have hT : T < t := by simpa only [interior_Ici, mem_Ioi] using ht
    change 0 < deriv (fun s => ‖c s‖ ^ 2) t
    rw [(lineCap_hasDerivAt_norm_sq (hd t hT).hasDerivAt).deriv]
    exact mul_pos (by norm_num) (hr t hT)
  intro s hs' t ht' hst
  have h := hs hs' ht' hst
  nlinarith [norm_nonneg (c s), norm_nonneg (c t)]

theorem lineCap_strictAnti_norm_of_radial_neg {c : ℝ → ℂ} (hc : Continuous c)
    {T : ℝ} (hd : ∀ t, t < T → DifferentiableAt ℝ c t)
    (hr : ∀ t, t < T → physicalRadialProjection (c t) (deriv c t) < 0) :
    StrictAntiOn (fun t => ‖c t‖) (Iic T) := by
  have hs : StrictAntiOn (fun t => ‖c t‖ ^ 2) (Iic T) := by
    apply strictAntiOn_of_deriv_neg (convex_Iic T) (hc.norm.pow 2).continuousOn
    intro t ht
    have hT : t < T := by simpa only [interior_Iic, mem_Iio] using ht
    change deriv (fun s => ‖c s‖ ^ 2) t < 0
    rw [(lineCap_hasDerivAt_norm_sq (hd t hT).hasDerivAt).deriv]
    exact mul_neg_of_pos_of_neg (by norm_num) (hr t hT)
  intro s hs' t ht' hst
  have h := hs hs' ht' hst
  nlinarith [norm_nonneg (c s), norm_nonneg (c t)]

/-- The outputs include the exact entire preimage of the open disk and circle;
there cannot be an unnoticed third crossing in the compact middle. -/
theorem exists_lineCap_crossings_of_radial_tails {c : ℝ → ℂ} (hc : Continuous c)
    {T : ℝ} (hT : 0 < T)
    (hpos : StrictMonoOn (fun t => ‖c t‖) (Ici T))
    (hneg : StrictAntiOn (fun t => ‖c t‖) (Iic (-T)))
    (hescapePos : Tendsto (fun t => ‖c t‖) atTop atTop)
    (hescapeNeg : Tendsto (fun t => ‖c t‖) atBot atTop) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R, R₀ < R →
      ∃ tMinus tPlus : ℝ, tMinus < -T ∧ T < tPlus ∧
        ‖c tMinus‖ = R ∧ ‖c tPlus‖ = R ∧
        (∀ t, ‖c t‖ < R ↔ t ∈ Ioo tMinus tPlus) ∧
        (∀ t, ‖c t‖ = R ↔ t = tMinus ∨ t = tPlus) := by
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (-T) T).Nonempty from ⟨0, by constructor <;> linarith⟩)
    hc.norm.continuousOn
  let R₀ := ‖c s‖ + 1
  have hR₀ : 0 < R₀ := by dsimp [R₀]; positivity
  have hcore : ∀ t ∈ Icc (-T) T, ‖c t‖ < R₀ := by
    intro t ht
    have h : ‖c t‖ ≤ ‖c s‖ := hmax ht
    dsimp [R₀]
    linarith
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR
  have hcoreR : ∀ t ∈ Icc (-T) T, ‖c t‖ < R :=
    fun t ht => (hcore t ht).trans hR
  obtain ⟨b, hbT, hbR⟩ := ((eventually_ge_atTop T).and
    (hescapePos.eventually_gt_atTop R)).exists
  obtain ⟨tp, htp, htpR⟩ := intermediate_value_Icc hbT hc.norm.continuousOn
    (show R ∈ Icc ‖c T‖ ‖c b‖ from
      ⟨(hcoreR T ⟨by linarith, le_rfl⟩).le, hbR.le⟩)
  change ‖c tp‖ = R at htpR
  have hTp : T < tp := by
    apply lt_of_le_of_ne htp.1
    intro he
    have h := hcoreR T ⟨by linarith, le_rfl⟩
    rw [he, htpR] at h
    exact lt_irrefl _ h
  obtain ⟨b, hbT, hbR⟩ := ((eventually_le_atBot (-T)).and
    (hescapeNeg.eventually_gt_atTop R)).exists
  obtain ⟨tm, htm, htmR⟩ := intermediate_value_Icc' hbT hc.norm.continuousOn
    (show R ∈ Icc ‖c (-T)‖ ‖c b‖ from
      ⟨(hcoreR (-T) ⟨le_rfl, by linarith⟩).le, hbR.le⟩)
  change ‖c tm‖ = R at htmR
  have hmT : tm < -T := by
    apply lt_of_le_of_ne htm.2
    intro he
    have h := hcoreR (-T) ⟨le_rfl, by linarith⟩
    rw [← he, htmR] at h
    exact lt_irrefl _ h
  have hinside : ∀ t ∈ Ioo tm tp, ‖c t‖ < R := by
    intro t ht
    by_cases hn : t ≤ -T
    · have h := hneg (show tm ∈ Iic (-T) from hmT.le) hn ht.1
      change ‖c t‖ < ‖c tm‖ at h
      rwa [htmR] at h
    · by_cases hp : T ≤ t
      · have h := hpos hp (show tp ∈ Ici T from hTp.le) ht.2
        change ‖c t‖ < ‖c tp‖ at h
        rwa [htpR] at h
      · exact hcoreR t ⟨(lt_of_not_ge hn).le, (lt_of_not_ge hp).le⟩
  have hleft : ∀ t, t < tm → R < ‖c t‖ := by
    intro t ht
    have h := hneg (show t ∈ Iic (-T) from (ht.trans hmT).le) hmT.le ht
    change ‖c tm‖ < ‖c t‖ at h
    rwa [htmR] at h
  have hright : ∀ t, tp < t → R < ‖c t‖ := by
    intro t ht
    have h := hpos hTp.le (show t ∈ Ici T from (hTp.trans ht).le) ht
    change ‖c tp‖ < ‖c t‖ at h
    rwa [htpR] at h
  refine ⟨tm, tp, hmT, hTp, htmR, htpR, ?_, ?_⟩
  · intro t
    constructor
    · intro ht
      constructor
      · rcases lt_trichotomy t tm with h | rfl | h
        · exact False.elim ((not_lt_of_ge (hleft t h).le) ht)
        · exact False.elim (ht.ne htmR)
        · exact h
      · rcases lt_trichotomy t tp with h | rfl | h
        · exact h
        · exact False.elim (ht.ne htpR)
        · exact False.elim ((not_lt_of_ge (hright t h).le) ht)
    · exact hinside t
  · intro t
    constructor
    · intro ht
      by_cases hm : t = tm
      · exact Or.inl hm
      by_cases hp : t = tp
      · exact Or.inr hp
      have htm' : tm < t := by
        by_contra hn
        have h := hleft t (lt_of_le_of_ne (le_of_not_gt hn) hm)
        rw [ht] at h
        exact lt_irrefl _ h
      have htp' : t < tp := by
        by_contra hn
        have h := hright t (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hp))
        rw [ht] at h
        exact lt_irrefl _ h
      have h := hinside t ⟨htm', htp'⟩
      rw [ht] at h
      exact False.elim (lt_irrefl _ h)
    · rintro (rfl | rfl) <;> assumption

/-- Actual metric data supply continuity and properness. The only analytic
inputs left are differentiability and the two literal radial signs. -/
theorem exists_pointMetricLine_transverse_large_circle_crossings
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {T : ℝ} (hT : 0 < T)
    (hdpos : ∀ t, T < t → DifferentiableAt ℝ c t)
    (hdneg : ∀ t, t < -T → DifferentiableAt ℝ c t)
    (hrpos : ∀ t, T < t → 0 < physicalRadialProjection (c t) (deriv c t))
    (hrneg : ∀ t, t < -T → physicalRadialProjection (c t) (deriv c t) < 0) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R, R₀ < R →
      ∃ tMinus tPlus : ℝ, tMinus < -T ∧ T < tPlus ∧
        ‖c tMinus‖ = R ∧ ‖c tPlus‖ = R ∧
        (∀ t, ‖c t‖ < R ↔ t ∈ Ioo tMinus tPlus) ∧
        (∀ t, ‖c t‖ = R ↔ t = tMinus ∨ t = tPlus) ∧
        physicalRadialProjection (c tMinus) (deriv c tMinus) < 0 ∧
        0 < physicalRadialProjection (c tPlus) (deriv c tPlus) := by
  have he := pointMetricLine_isClosedEmbedding ha y c hd
  have hp := he.tendsto_cocompact
  have hpTop : Tendsto c atTop (cocompact ℂ) := hp.mono_left atTop_le_cocompact
  have hpBot : Tendsto c atBot (cocompact ℂ) := hp.mono_left atBot_le_cocompact
  obtain ⟨R₀, hR₀, hcross⟩ := exists_lineCap_crossings_of_radial_tails he.continuous hT
    (lineCap_strictMono_norm_of_radial_pos he.continuous hdpos hrpos)
    (lineCap_strictAnti_norm_of_radial_neg he.continuous hdneg hrneg)
    (tendsto_norm_cocompact_atTop.comp hpTop) (tendsto_norm_cocompact_atTop.comp hpBot)
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR
  obtain ⟨tm, tp, hm, hp, hmR, hpR, hi, heq⟩ := hcross R hR
  exact ⟨tm, tp, hm, hp, hmR, hpR, hi, heq, hrneg tm hm, hrpos tp hp⟩

end RepulsiveCoulomb
