module

public import LeanResearch.RepulsiveCoulomb.PointGeodesicSmoothArc
public import LeanResearch.RepulsiveCoulomb.PointGeodesicBigonExtraction

@[expose] public section

/-! Ordered finite lists of actual smooth regular representatives of subarcs.
All source intervals have positive length, every endpoint and image is explicit,
and list concatenation preserves order. No existence of such a decomposition
for an arbitrary curve is assumed by the definitions. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

structure PointSmoothArcPiece (γ : Icc (0 : ℝ) 1 → ℂ) where
  start : Icc (0 : ℝ) 1
  finish : Icc (0 : ℝ) 1
  increasing : start < finish
  curve : ℝ → ℂ
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) curve
  injective : InjOn curve (Icc (0 : ℝ) 1)
  regular : ∀ u ∈ Icc (0 : ℝ) 1, deriv curve u ≠ 0
  at_zero : curve 0 = γ start
  at_one : curve 1 = γ finish
  image : curve '' Icc (0 : ℝ) 1 = γ '' Icc start finish

inductive PointSmoothArcChain (γ : Icc (0 : ℝ) 1 → ℂ) :
    Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 → List (PointSmoothArcPiece γ) → Prop
  | nil (s) : PointSmoothArcChain γ s s []
  | cons (e : PointSmoothArcPiece γ) {t} {es} :
      PointSmoothArcChain γ e.finish t es → PointSmoothArcChain γ e.start t (e :: es)

namespace PointSmoothArcChain

variable {γ : Icc (0 : ℝ) 1 → ℂ}

theorem endpoints_le {s t : Icc (0 : ℝ) 1} {es : List (PointSmoothArcPiece γ)}
    (h : PointSmoothArcChain γ s t es) : s ≤ t := by
  induction h with
  | nil => exact le_rfl
  | cons e _ ih => exact e.increasing.le.trans ih

theorem append {s r t : Icc (0 : ℝ) 1} {es fs : List (PointSmoothArcPiece γ)}
    (he : PointSmoothArcChain γ s r es) (hf : PointSmoothArcChain γ r t fs) :
    PointSmoothArcChain γ s t (es ++ fs) := by
  induction he with
  | nil => exact hf
  | cons e h ih => exact .cons e (ih hf)

theorem piece_bounds {s t : Icc (0 : ℝ) 1} {es : List (PointSmoothArcPiece γ)}
    (h : PointSmoothArcChain γ s t es) {e : PointSmoothArcPiece γ} (he : e ∈ es) :
    s ≤ e.start ∧ e.finish ≤ t := by
  induction h with
  | nil => simp at he
  | cons f h ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨le_rfl, h.endpoints_le⟩
    · obtain ⟨hs, ht⟩ := ih he
      exact ⟨f.increasing.le.trans hs, ht⟩

/-- Every parameter is either the initial endpoint or belongs to an actual
piece interval. This formulation also covers the empty zero-length chain. -/
theorem interval_covered {s t : Icc (0 : ℝ) 1} {es : List (PointSmoothArcPiece γ)}
    (h : PointSmoothArcChain γ s t es) {u : Icc (0 : ℝ) 1} (hu : u ∈ Icc s t) :
    u = s ∨ ∃ e ∈ es, u ∈ Icc e.start e.finish := by
  induction h with
  | nil => exact Or.inl (le_antisymm hu.2 hu.1)
  | cons e h ih =>
    by_cases hue : u ≤ e.finish
    · exact Or.inr ⟨e, List.mem_cons_self, hu.1, hue⟩
    · have heus : e.finish ≤ u := (lt_of_not_ge hue).le
      rcases ih ⟨heus, hu.2⟩ with hu0 | ⟨f, hf, huf⟩
      · exact False.elim (hue hu0.le)
      · exact Or.inr ⟨f, List.mem_cons_of_mem e hf, huf⟩

theorem pair_order {s t : Icc (0 : ℝ) 1} {es : List (PointSmoothArcPiece γ)}
    (h : PointSmoothArcChain γ s t es) :
    ∀ e ∈ es, ∀ f ∈ es, e ≠ f → e.finish ≤ f.start ∨ f.finish ≤ e.start := by
  induction h with
  | nil => simp
  | cons g h ih =>
    intro e he f hf hef
    rcases List.mem_cons.mp he with heg | hetail
    · subst e
      rcases List.mem_cons.mp hf with hfg | hftail
      · subst f
        exact False.elim (hef rfl)
      · exact Or.inl (h.piece_bounds hftail).1
    · rcases List.mem_cons.mp hf with hfg | hftail
      · subst f
        exact Or.inr (h.piece_bounds hetail).1
      · exact ih e hetail f hftail hef

theorem nodup {s t : Icc (0 : ℝ) 1} {es : List (PointSmoothArcPiece γ)}
    (h : PointSmoothArcChain γ s t es) : es.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | cons e h ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_, ih⟩
    intro he
    exact (not_le_of_gt e.increasing) (h.piece_bounds he).1

/-- The union is the exact original interval image, with no added points and
no uncovered endpoint, for every positive-length chain. -/
theorem exact_image {s t : Icc (0 : ℝ) 1} {es : List (PointSmoothArcPiece γ)}
    (h : PointSmoothArcChain γ s t es) (hst : s < t) :
    (⋃ e ∈ es, e.curve '' Icc (0 : ℝ) 1) = γ '' Icc s t := by
  have hstart : γ s ∈ ⋃ e ∈ es, e.curve '' Icc (0 : ℝ) 1 := by
    cases h with
    | nil => exact False.elim ((lt_irrefl s) hst)
    | cons e h =>
      exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨List.mem_cons_self,
        ⟨0, by norm_num, e.at_zero⟩⟩⟩
  apply Subset.antisymm
  · intro z hz
    rcases mem_iUnion.mp hz with ⟨e, hz⟩
    rcases mem_iUnion.mp hz with ⟨he, hz⟩
    rw [e.image] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    obtain ⟨hs, ht⟩ := h.piece_bounds he
    exact ⟨u, ⟨hs.trans hu.1, hu.2.trans ht⟩, rfl⟩
  · rintro z ⟨u, hu, rfl⟩
    rcases h.interval_covered hu with rfl | ⟨e, he, hue⟩
    · exact hstart
    · apply mem_iUnion.mpr
      refine ⟨e, mem_iUnion.mpr ⟨he, ?_⟩⟩
      rw [e.image]
      exact ⟨u, hue, rfl⟩

/-- Distinct ordered pieces of a simple original arc can intersect only at a
common endpoint. Source order, rather than an assumed drawing, proves this. -/
theorem piece_intersection_endpoints {s t : Icc (0 : ℝ) 1} {es : List (PointSmoothArcPiece γ)}
    (h : PointSmoothArcChain γ s t es) (hγ : Function.Injective γ)
    {e f : PointSmoothArcPiece γ} (he : e ∈ es) (hf : f ∈ es) (hef : e ≠ f) :
    e.curve '' Icc (0 : ℝ) 1 ∩ f.curve '' Icc (0 : ℝ) 1 ⊆
      {γ e.finish, γ f.finish} := by
  intro z hz
  rw [e.image, f.image] at hz
  obtain ⟨⟨u, hu, huz⟩, ⟨v, hv, hvz⟩⟩ := hz
  have huv := hγ (huz.trans hvz.symm)
  subst v
  rcases h.pair_order e he f hf hef with hef | hfe
  · have hue : u = e.finish := le_antisymm hu.2 (hef.trans hv.1)
    have hze : z = γ e.finish := huz.symm.trans (congrArg γ hue)
    simp only [hze, mem_insert_iff, mem_singleton_iff, true_or]
  · have huf : u = f.finish := le_antisymm hv.2 (hfe.trans hu.1)
    have hzf : z = γ f.finish := huz.symm.trans (congrArg γ huf)
    simp only [hzf, mem_insert_iff, mem_singleton_iff, or_true]

end PointSmoothArcChain
end RepulsiveCoulomb
