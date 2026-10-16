import LeanResearch.RepulsiveCoulomb.PointLineCapFiniteChain
import Mathlib.Data.List.Chain
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Order

/-! Records-only, uncompiled. Literal finite cap lists are converted to the
n-bounded natural-index family used by mixed Gauss--Bonnet. The radial pieces
and the appended circle remain the original functions, with no reparametrized
or replaced germ. This module supplies indexing and geometry, not GB. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

namespace LineCapCurveChain

theorem head_start {p q : ℂ} {L : List (ℝ → ℂ)}
    (h : LineCapCurveChain p q L) (hne : L ≠ []) : (L.head hne) 0 = p := by
  cases h with
  | nil => contradiction
  | cons f ht => rfl

theorem last_finish {p q : ℂ} {L : List (ℝ → ℂ)}
    (h : LineCapCurveChain p q L) (hne : L ≠ []) : (L.getLast hne) 1 = q := by
  have hnil : ∀ p q : ℂ, LineCapCurveChain p q [] → p = q := by
    intro p q hpq
    cases hpq
    rfl
  induction h with
  | nil => contradiction
  | @cons f q fs h ih =>
    by_cases hfs : fs = []
    · subst fs
      simpa using hnil (f 1) q h
    · rw [List.getLast_cons hfs]
      exact ih hfs

theorem actual_isChain {p q : ℂ} {L : List (ℝ → ℂ)}
    (h : LineCapCurveChain p q L) : L.IsChain (fun f g => f 1 = g 0) := by
  induction h with
  | nil => exact .nil
  | @cons f q fs h ih =>
    cases fs with
    | nil => exact .singleton f
    | cons g gs => exact .cons_cons (h.head_start (by simp)).symm ih

end LineCapCurveChain

def lineCapNatCurve (L : List (ℝ → ℂ)) (k : ℕ) : ℝ → ℂ := L.getD k (fun _ => 0)

theorem lineCapNatCurve_eq_get {L : List (ℝ → ℂ)} {k : ℕ} (hk : k < L.length) :
    lineCapNatCurve L k = L.get ⟨k, hk⟩ := by
  change L.getD k (fun _ => 0) = L.get ⟨k, hk⟩
  exact List.getD_eq_get L (fun _ => 0) ⟨k, hk⟩

theorem lineCapNatCurve_mem {L : List (ℝ → ℂ)} {k : ℕ} (hk : k < L.length) :
    lineCapNatCurve L k ∈ L := by
  rw [lineCapNatCurve_eq_get hk]
  exact List.get_mem L _

theorem lineCapNatCurve_carrier (L : List (ℝ → ℂ)) (hL : 0 < L.length) :
    (⋃ k ≤ L.length - 1, lineCapNatCurve L k '' Icc (0 : ℝ) 1) =
      ⋃ f ∈ L, f '' Icc (0 : ℝ) 1 := by
  ext z
  simp only [mem_iUnion]
  constructor
  · rintro ⟨k, hk, hz⟩
    exact ⟨lineCapNatCurve L k, lineCapNatCurve_mem (by omega), hz⟩
  · rintro ⟨f, hf, hz⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hf
    refine ⟨i.val, by omega, ?_⟩
    rw [lineCapNatCurve_eq_get i.isLt, hi]
    exact hz

/-- The complete elementary natural-index part of the mixed-GB interface. -/
theorem lineCapNatCurve_properties {p : ℂ} {L : List (ℝ → ℂ)}
    (hc : LineCapCurveChain p p L) (hlen : 2 ≤ L.length)
    (hf : ∀ f ∈ L, ContDiff ℝ 1 f ∧ InjOn f (Icc (0 : ℝ) 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, deriv f t ≠ 0)
    (hpair : L.Pairwise (fun f g =>
      Disjoint (f '' Ico (0 : ℝ) 1) (g '' Ico (0 : ℝ) 1))) :
    let n := L.length - 1
    let f := lineCapNatCurve L
    0 < n ∧ (∀ k ≤ n, ContDiff ℝ 1 (f k)) ∧
      (∀ k < n, f k 1 = f (k + 1) 0) ∧ f n 1 = f 0 0 ∧
      (∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1, deriv (f k) t ≠ 0) ∧
      (∀ i j, i ≤ n → j ≤ n → ∀ s t,
        s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t) := by
  dsimp only
  have hne : L ≠ [] := List.length_pos_iff.mp (by omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact (hf _ (lineCapNatCurve_mem (by omega))).1
  · intro k hk
    rw [lineCapNatCurve, lineCapNatCurve,
      List.getD_eq_getElem _ _ (by omega : k < L.length),
      List.getD_eq_getElem _ _ (by omega : k + 1 < L.length)]
    exact hc.actual_isChain.getElem k (by omega)
  · have hlast : lineCapNatCurve L (L.length - 1) = L.getLast hne := by
      rw [lineCapNatCurve, List.getD_eq_getElem _ _ (by omega), List.getLast_eq_getElem]
    have hhead : lineCapNatCurve L 0 = L.head hne := by
      rw [lineCapNatCurve, List.getD_eq_getElem _ _ (by omega), List.head_eq_getElem]
    rw [hlast, hhead, hc.last_finish hne, hc.head_start hne]
  · intro k hk
    exact (hf _ (lineCapNatCurve_mem (by omega))).2.2
  · intro i j hi hj s t hs ht he
    have hiL : i < L.length := by omega
    have hjL : j < L.length := by omega
    have hij : i = j := by
      by_contra hij
      have hdisj : Disjoint (lineCapNatCurve L i '' Ico (0 : ℝ) 1)
          (lineCapNatCurve L j '' Ico (0 : ℝ) 1) := by
        rw [lineCapNatCurve_eq_get hiL, lineCapNatCurve_eq_get hjL]
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · exact hpair.rel_get_of_lt (show (⟨i, hiL⟩ : Fin L.length) < ⟨j, hjL⟩ from hlt)
        · exact (hpair.rel_get_of_lt (show (⟨j, hjL⟩ : Fin L.length) < ⟨i, hiL⟩ from hgt)).symm
      exact disjoint_left.mp hdisj ⟨s, hs, rfl⟩ ⟨t, ht, he.symm⟩
    subst j
    exact ⟨rfl, (hf _ (lineCapNatCurve_mem hiL)).2.1
      (Ico_subset_Icc_self hs) (Ico_subset_Icc_self ht) he⟩

/-- The final edge is literally the circle; the earlier edges are literally
the retained source radial pieces, at the same indices and parameters. -/
theorem lineCapNatCurve_append_circle
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {γ : Icc (0 : ℝ) 1 → ℂ} (es : List (PointRadialC1ArcPiece ha y γ)) (g : ℝ → ℂ) :
    lineCapNatCurve (es.map (fun e => e.curve) ++ [g]) es.length = g ∧
      ∀ k (hk : k < es.length),
        lineCapNatCurve (es.map (fun e => e.curve) ++ [g]) k = (es.get ⟨k, hk⟩).curve := by
  constructor
  · unfold lineCapNatCurve
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  · intro k hk
    rw [lineCapNatCurve, List.getD_append _ _ _ _ (by simpa using hk)]
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.get_eq_getElem]

/-- Construct the actual natural-indexed family directly from a metric line
and its actual cap. No family or cycle certificate is requested from callers. -/
theorem exists_pointMetricLine_cap_nat_family
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {tm tp R α β : ℝ} (ht : tm < tp) (hR : 0 < R)
    (hab : α < β) (hwidth : β < α + 2 * Real.pi)
    (hcross : ∀ t, ‖c t‖ = R ↔ t = tm ∨ t = tp)
    (hzero : pointCircleCapArc R α β 0 = c tp)
    (hone : pointCircleCapArc R α β 1 = c tm) :
    ∃ es : List (PointRadialC1ArcPiece ha y (lineCapSegment c tm tp)),
      PointRadialC1ArcChain ha y (lineCapSegment c tm tp) 0 1 es ∧
      let n := es.length
      let f := lineCapNatCurve (es.map (fun e => e.curve) ++ [pointCircleCapArc R α β])
      0 < n ∧ f n = pointCircleCapArc R α β ∧
      (∀ k (hk : k < n), f k = (es.get ⟨k, hk⟩).curve) ∧
      (∀ k ≤ n, ContDiff ℝ 1 (f k)) ∧
      (∀ k < n, f k 1 = f (k + 1) 0) ∧ f n 1 = f 0 0 ∧
      (∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1, deriv (f k) t ≠ 0) ∧
      (∀ i j, i ≤ n → j ≤ n → ∀ s t,
        s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t) ∧
      (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1) =
        c '' Icc tm tp ∪ pointCircleCapArc R α β '' Icc (0 : ℝ) 1 := by
  obtain ⟨es, hes, hne, hc, hf, hpair, hcarrier⟩ :=
    exists_pointMetricLine_cap_finite_chain ha y c hd ht hR hab hwidth hcross hzero hone
  let L := es.map (fun e => e.curve) ++ [pointCircleCapArc R α β]
  have hlen : 2 ≤ L.length := by
    have he : 0 < es.length := List.length_pos_iff.mpr hne
    simp only [L, List.length_append, List.length_map, List.length_singleton]
    omega
  have hn : L.length - 1 = es.length := by simp [L]
  obtain ⟨hnpos, hsm, hv, hcl, hreg, hinj⟩ := lineCapNatCurve_properties hc hlen hf hpair
  rw [hn] at hnpos hsm hv hcl hreg hinj
  obtain ⟨hcircle, hpieces⟩ := lineCapNatCurve_append_circle es (pointCircleCapArc R α β)
  refine ⟨es, hes, hnpos, hcircle, hpieces, hsm, hv, hcl, hreg, hinj, ?_⟩
  have hi := lineCapNatCurve_carrier L (by omega)
  rw [hn, hcarrier] at hi
  exact hi

end RepulsiveCoulomb
