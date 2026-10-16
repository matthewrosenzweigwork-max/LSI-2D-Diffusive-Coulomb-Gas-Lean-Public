import LeanResearch.RepulsiveCoulomb.PointLineCapJordan
import LeanResearch.RepulsiveCoulomb.PointRadialC1ChainHalfOpen
import Mathlib.Data.List.Pairwise

/-! Records-only, uncompiled. Construct the actual finite radial-geodesic
macro-chain and append the curved circle as an ordinary C1 edge. In particular
we do not falsely force the circular edge to have radial chart germs. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

inductive LineCapCurveChain : ℂ → ℂ → List (ℝ → ℂ) → Prop
  | nil (p) : LineCapCurveChain p p []
  | cons (f : ℝ → ℂ) {q fs} :
      LineCapCurveChain (f 1) q fs → LineCapCurveChain (f 0) q (f :: fs)

namespace LineCapCurveChain

theorem append {p q r : ℂ} {fs gs : List (ℝ → ℂ)}
    (hf : LineCapCurveChain p q fs) (hg : LineCapCurveChain q r gs) :
    LineCapCurveChain p r (fs ++ gs) := by
  induction hf with
  | nil => exact hg
  | cons f _ ih => exact .cons f (ih hg)

end LineCapCurveChain

theorem PointRadialC1ArcChain.toLineCapCurveChain
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {γ : Icc (0 : ℝ) 1 → ℂ} {s t : Icc (0 : ℝ) 1}
    {es : List (PointRadialC1ArcPiece ha y γ)}
    (h : PointRadialC1ArcChain ha y γ s t es) :
    LineCapCurveChain (γ s) (γ t) (es.map (fun e => e.curve)) := by
  induction h with
  | nil => exact .nil _
  | cons e _ ih =>
    have htail := ih
    rw [← e.at_one] at htail
    have hout := LineCapCurveChain.cons e.curve htail
    rw [e.at_zero] at hout
    exact hout

/-- The original radial pieces are retained as witnesses, alongside the
ordinary C1 circle. Every half-open point has a unique edge owner. -/
theorem exists_pointMetricLine_cap_finite_chain
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {tm tp R α β : ℝ} (ht : tm < tp) (hR : 0 < R)
    (hab : α < β) (hwidth : β < α + 2 * Real.pi)
    (hcross : ∀ t, ‖c t‖ = R ↔ t = tm ∨ t = tp)
    (hzero : pointCircleCapArc R α β 0 = c tp)
    (hone : pointCircleCapArc R α β 1 = c tm) :
    ∃ es : List (PointRadialC1ArcPiece ha y (lineCapSegment c tm tp)),
      PointRadialC1ArcChain ha y (lineCapSegment c tm tp) 0 1 es ∧ es ≠ [] ∧
      let L := es.map (fun e => e.curve) ++ [pointCircleCapArc R α β]
      LineCapCurveChain (c tm) (c tm) L ∧
      (∀ f ∈ L, ContDiff ℝ 1 f ∧ InjOn f (Icc (0 : ℝ) 1) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, deriv f t ≠ 0) ∧
      L.Pairwise (fun f g => Disjoint (f '' Ico (0 : ℝ) 1) (g '' Ico (0 : ℝ) 1)) ∧
      (⋃ f ∈ L, f '' Icc (0 : ℝ) 1) =
        c '' Icc tm tp ∪ pointCircleCapArc R α β '' Icc (0 : ℝ) 1 := by
  have he := pointMetricLine_isClosedEmbedding ha y c hd
  have hpq : c tm ≠ c tp := fun h => ht.ne (he.injective h)
  let γ := lineCapSegment c tm tp
  have hγi : Function.Injective γ := lineCapSegment_injective he.injective ht
  obtain ⟨es, hes, _, hne, him⟩ := exists_pointConformal_finite_radial_C1_arc_chain
    ha y hpq γ (lineCapSegment_metric y c hd tm tp)
  have hf := lineCapArc_injOn hR hab hwidth
  have hmeet := lineCapSegment_circle_intersection hR ht hcross hzero hone
  have hdisj := lineCap_halfOpen_disjoint hγi hf
    (lineCapSegment_zero c tm tp) (lineCapSegment_one c tm tp) hzero hone hmeet
  refine ⟨es, hes, hne, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hline := hes.toLineCapCurveChain
    have hline' : LineCapCurveChain (c tm) (c tp) (es.map (fun e => e.curve)) := by
      simpa [γ, lineCapSegment] using hline
    have hcircle : LineCapCurveChain (c tp) (c tm) [pointCircleCapArc R α β] := by
      have h := LineCapCurveChain.cons (pointCircleCapArc R α β)
        (LineCapCurveChain.nil (pointCircleCapArc R α β 1))
      rwa [hzero, hone] at h
    exact hline'.append hcircle
  · intro f hfmem
    rcases List.mem_append.mp hfmem with hfmem | hfmem
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hfmem
      exact ⟨e.smooth, e.injective, e.regular⟩
    · have heq : f = pointCircleCapArc R α β := by simpa only [List.mem_singleton] using hfmem
      subst f
      exact ⟨pointCircleCapArc_smooth R α β, hf, fun t _ => pointCircleCapArc_regular hR hab t⟩
  · rw [List.pairwise_append]
    refine ⟨?_, by simp, ?_⟩
    · rw [List.pairwise_map]
      exact hes.nodup.pairwise_of_forall_ne
        (fun e he f hf hef => hes.halfOpen_pairwise_disjoint hγi he hf hef)
    · intro f hfmem g hgmem
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hfmem
      have heq : g = pointCircleCapArc R α β := by simpa only [List.mem_singleton] using hgmem
      subst g
      exact hdisj.mono_left (hes.halfOpen_subset_total hγi he)
  · rw [← lineCapSegment_range c ht, ← him]
    ext z
    simp only [mem_iUnion, List.mem_append, List.mem_map, List.mem_singleton, mem_union]
    constructor
    · rintro ⟨f, (⟨e, he, rfl⟩ | rfl), hz⟩
      · exact Or.inl ⟨e, he, hz⟩
      · exact Or.inr hz
    · rintro (⟨e, he, hz⟩ | hz)
      · exact ⟨e.curve, Or.inl ⟨e, he, rfl⟩, hz⟩
      · exact ⟨pointCircleCapArc R α β, Or.inr rfl, hz⟩

end RepulsiveCoulomb
