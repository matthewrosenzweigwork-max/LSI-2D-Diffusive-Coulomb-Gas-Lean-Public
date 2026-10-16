import LeanResearch.RepulsiveCoulomb.PointLineCapArc
import LeanResearch.RepulsiveCoulomb.PointMetricLineSideRegions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Records-only, uncompiled. Literal line restriction plus the constructed
circle arc is proved Jordan using the accepted two-arc theorem. The bounded
Jordan region is constructed here, never assumed. Fixed-line-side identity
and exhaustion are separate remaining topological obligations. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

def lineCapSegment (c : ℝ → ℂ) (s t : ℝ) (u : Icc (0 : ℝ) 1) : ℂ :=
  c (s + u.1 * (t - s))

@[simp] theorem lineCapSegment_zero (c : ℝ → ℂ) (s t : ℝ) :
    lineCapSegment c s t 0 = c s := by simp [lineCapSegment]

@[simp] theorem lineCapSegment_one (c : ℝ → ℂ) (s t : ℝ) :
    lineCapSegment c s t 1 = c t := by simp [lineCapSegment]

theorem lineCapSegment_continuous {c : ℝ → ℂ} (hc : Continuous c) (s t : ℝ) :
    Continuous (lineCapSegment c s t) :=
  hc.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))

theorem lineCapSegment_injective {c : ℝ → ℂ} (hi : Function.Injective c)
    {s t : ℝ} (hst : s < t) : Function.Injective (lineCapSegment c s t) := by
  intro u v huv
  apply Subtype.ext
  have h := hi huv
  nlinarith [sub_pos.mpr hst]

theorem lineCapSegment_range (c : ℝ → ℂ) {s t : ℝ} (hst : s < t) :
    range (lineCapSegment c s t) = c '' Icc s t := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨s + u.1 * (t - s), ?_, rfl⟩
    have hlo := mul_nonneg u.2.1 (sub_pos.mpr hst).le
    have hhi := mul_le_mul_of_nonneg_right u.2.2 (sub_pos.mpr hst).le
    constructor <;> nlinarith
  · rintro ⟨r, hr, rfl⟩
    let u : Icc (0 : ℝ) 1 := ⟨(r - s) / (t - s),
      div_nonneg (sub_nonneg.mpr hr.1) (sub_pos.mpr hst).le,
      (div_le_one (sub_pos.mpr hst)).mpr (by linarith [hr.2])⟩
    refine ⟨u, congrArg c ?_⟩
    change s + (r - s) / (t - s) * (t - s) = r
    rw [div_mul_cancel₀ _ (sub_pos.mpr hst).ne']
    ring

/-- The restriction is a genuine minimizing interval with exactly the metric
normalization needed by the existing finite radial-C1 assembly theorem. -/
theorem lineCapSegment_metric {m : ℕ} {a : Fin m → ℝ} (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    (s t : ℝ) :
    ∀ u v, (pointSmoothConformalEDist a y (lineCapSegment c s t u)
      (lineCapSegment c s t v)).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y (c s) (c t)).toReal := by
  intro u v
  rw [lineCapSegment, lineCapSegment, hd, hd, Real.dist_eq, Real.dist_eq]
  have he : s + u.1 * (t - s) - (s + v.1 * (t - s)) =
      (u.1 - v.1) * (t - s) := by ring
  rw [he, abs_mul, abs_sub_comm u.1 v.1, abs_sub_comm t s]

/-- Exact crossing uniqueness gives the two-arc intersection, including both
endpoints. The two-edge case is therefore handled without a false disjointness
claim at the closing endpoint. -/
theorem lineCapSegment_circle_intersection {c : ℝ → ℂ} {tm tp R α β : ℝ}
    (hR : 0 < R) (ht : tm < tp)
    (hcross : ∀ t, ‖c t‖ = R ↔ t = tm ∨ t = tp)
    (hzero : pointCircleCapArc R α β 0 = c tp)
    (hone : pointCircleCapArc R α β 1 = c tm) :
    range (lineCapSegment c tm tp) ∩
      pointCircleCapArc R α β '' Icc (0 : ℝ) 1 = {c tm, c tp} := by
  ext z
  constructor
  · rintro ⟨⟨u, huz⟩, v, hv, hvz⟩
    have hn : ‖c (tm + u.1 * (tp - tm))‖ = R := by
      change ‖lineCapSegment c tm tp u‖ = R
      rw [huz, ← hvz, pointCircleCapArc_norm hR.le]
    rcases (hcross _).mp hn with h | h
    · exact Or.inl (huz.symm.trans (congrArg c h))
    · exact Or.inr (mem_singleton_iff.mpr (huz.symm.trans (congrArg c h)))
  · rintro (hz | hz)
    · subst z
      exact ⟨⟨0, lineCapSegment_zero c tm tp⟩, 1, by norm_num, hone⟩
    · have hz' := mem_singleton_iff.mp hz
      subst z
      exact ⟨⟨1, lineCapSegment_one c tm tp⟩, 0, by norm_num, hzero⟩

/-- Both arcs are oriented consecutively, and their left-closed/right-open
images are disjoint. Each join is assigned to exactly one arc. -/
theorem lineCap_halfOpen_disjoint {γ : Icc (0 : ℝ) 1 → ℂ} {f : ℝ → ℂ}
    {p q : ℂ} (hγ : Function.Injective γ) (hf : InjOn f (Icc (0 : ℝ) 1))
    (hγ0 : γ 0 = p) (hγ1 : γ 1 = q) (hf0 : f 0 = q) (hf1 : f 1 = p)
    (hmeet : range γ ∩ f '' Icc (0 : ℝ) 1 = {p, q}) :
    Disjoint (γ '' Ico (0 : Icc (0 : ℝ) 1) 1) (f '' Ico (0 : ℝ) 1) := by
  apply disjoint_left.mpr
  rintro z ⟨s, hs, hsz⟩ ⟨t, ht, htz⟩
  have hz : z ∈ range γ ∩ f '' Icc (0 : ℝ) 1 :=
    ⟨⟨s, hsz⟩, t, ⟨ht.1, ht.2.le⟩, htz⟩
  rw [hmeet] at hz
  rcases mem_insert_iff.mp hz with hzp | hzq
  · have he : t = 1 := hf ⟨ht.1, ht.2.le⟩ (by norm_num)
      ((htz.trans hzp).trans hf1.symm)
    exact ht.2.ne he
  · have he : s = 1 := hγ ((hsz.trans (mem_singleton_iff.mp hzq)).trans hγ1.symm)
    exact hs.2.ne he

/-- A true Jordan cap is constructed from the line and its two circle
crossings. No Jordan-region or winding hypothesis occurs. -/
theorem lineCap_jordan {c : ℝ → ℂ} (hc : Continuous c) (hi : Function.Injective c)
    {tm tp R α β : ℝ} (hR : 0 < R) (ht : tm < tp)
    (hab : α < β) (hwidth : β < α + 2 * Real.pi)
    (hcross : ∀ t, ‖c t‖ = R ↔ t = tm ∨ t = tp)
    (hzero : pointCircleCapArc R α β 0 = c tp)
    (hone : pointCircleCapArc R α β 1 = c tm) :
    Schoenflies.IsJordanCurve (Complex.orthonormalBasisOneI.repr ''
      (range (lineCapSegment c tm tp) ∪ pointCircleCapArc R α β '' Icc (0 : ℝ) 1)) := by
  let γ := lineCapSegment c tm tp
  let f : Icc (0 : ℝ) 1 → ℂ := fun u => pointCircleCapArc R α β u.1
  let e := Complex.orthonormalBasisOneI.repr
  have hγ := isArcBetween_of_continuous_injective_interval (e ∘ γ)
    (e.continuous.comp (lineCapSegment_continuous hc tm tp))
    (e.injective.comp (lineCapSegment_injective hi ht))
  have hf := isArcBetween_of_continuous_injective_interval (e ∘ f)
    (e.continuous.comp ((pointCircleCapArc_smooth R α β).continuous.comp continuous_subtype_val))
    (e.injective.comp (fun u v huv => Subtype.ext
      (lineCapArc_injOn hR hab hwidth u.2 v.2 huv)))
  have hfim : range f = pointCircleCapArc R α β '' Icc (0 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩; exact ⟨u.1, u.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨⟨u, hu⟩, rfl⟩
  have hmeet : range (e ∘ γ) ∩ range (e ∘ f) = {e (c tm), e (c tp)} := by
    rw [range_comp, range_comp, ← image_inter e.injective, hfim,
      lineCapSegment_circle_intersection hR ht hcross hzero hone,
      image_insert_eq, image_singleton]
  have hγ0 : γ 0 = c tm := lineCapSegment_zero c tm tp
  have hγ1 : γ 1 = c tp := lineCapSegment_one c tm tp
  have hf0 : f 0 = c tp := hzero
  have hf1 : f 1 = c tm := hone
  have hγ' : Schoenflies.IsArcBetween (range (e ∘ γ)) (e (c tm)) (e (c tp)) := by
    simpa [γ, lineCapSegment] using hγ
  have hf' : Schoenflies.IsArcBetween (range (e ∘ f)) (e (c tp)) (e (c tm)) := by
    simpa [f, hzero, hone] using hf
  have hJ := Schoenflies.IsJordanCurve.two_arcs_of_two_arcs hγ' hf'.reverse hmeet
  rw [range_comp, range_comp, hfim, ← image_union] at hJ
  exact hJ

/-- The actual bounded complementary region and its exact frontier are outputs
of Jordan separation, rather than cap certificates in the hypotheses. -/
theorem exists_lineCap_actual_regions {c : ℝ → ℂ} (hc : Continuous c)
    (hi : Function.Injective c) {tm tp R α β : ℝ} (hR : 0 < R) (ht : tm < tp)
    (hab : α < β) (hwidth : β < α + 2 * Real.pi)
    (hcross : ∀ t, ‖c t‖ = R ↔ t = tm ∨ t = tp)
    (hzero : pointCircleCapArc R α β 0 = c tp)
    (hone : pointCircleCapArc R α β 1 = c tm) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V =
        (c '' Icc tm tp ∪ pointCircleCapArc R α β '' Icc (0 : ℝ) 1)ᶜ ∧
      frontier U = c '' Icc tm tp ∪ pointCircleCapArc R α β '' Icc (0 : ℝ) 1 ∧
      frontier V = c '' Icc tm tp ∪ pointCircleCapArc R α β '' Icc (0 : ℝ) 1 ∧
      IsCompact (closure U) := by
  have hJ := lineCap_jordan hc hi hR ht hab hwidth hcross hzero hone
  rw [lineCapSegment_range c ht] at hJ
  exact complex_jordan_regions_of_image hJ

end RepulsiveCoulomb
