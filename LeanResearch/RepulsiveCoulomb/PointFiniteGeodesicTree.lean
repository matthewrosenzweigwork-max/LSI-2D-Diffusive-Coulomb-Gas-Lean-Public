import LeanResearch.RepulsiveCoulomb.PointGeodesicNearestAttachment

/-! Actual finite geodesic trees connecting any finite point set. Every new
simple arc attaches to the previously constructed compact tree at exactly one
endpoint. No claim that the complement of a compact tree is simply connected
is made; a proper ray to infinity is a separate subsequent construction. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

structure PointGeodesicTreeEdge {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) where
  start : ℂ
  finish : ℂ
  distinct : start ≠ finish
  curve : Icc (0 : ℝ) 1 → ℂ
  curve_start : curve ⟨0, by norm_num⟩ = start
  curve_finish : curve ⟨1, by norm_num⟩ = finish
  continuous : Continuous curve
  geodesic : ∀ s t, (pointSmoothConformalEDist a y (curve s) (curve t)).toReal =
    |t.1 - s.1| * (pointSmoothConformalEDist a y start finish).toReal

/-- Edges are stored in reverse order of attachment. -/
def pointGeodesicTreeCarrier {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} (p : ℂ) :
    List (PointGeodesicTreeEdge a y) → Set ℂ
  | [] => {p}
  | e :: es => pointGeodesicTreeCarrier p es ∪ range e.curve

/-- Finite attachment data for an embedded geodesic tree. The singleton
intersection is a proved geometric condition, not an abstract acyclicity tag. -/
inductive PointGeodesicTree {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (p : ℂ) :
    List (PointGeodesicTreeEdge a y) → Prop
  | root : PointGeodesicTree a y p []
  | attach {es : List (PointGeodesicTreeEdge a y)} (e : PointGeodesicTreeEdge a y)
      (previous : PointGeodesicTree a y p es)
      (new_start : e.start ∉ pointGeodesicTreeCarrier p es)
      (old_finish : e.finish ∈ pointGeodesicTreeCarrier p es)
      (intersection : range e.curve ∩ pointGeodesicTreeCarrier p es = {e.finish}) :
      PointGeodesicTree a y p (e :: es)

theorem pointGeodesicTree_root_mem {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (p : ℂ) (es : List (PointGeodesicTreeEdge a y)) : p ∈ pointGeodesicTreeCarrier p es := by
  induction es with
  | nil => exact mem_singleton p
  | cons e es ih => exact Or.inl ih

theorem pointGeodesicTree_compact {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (p : ℂ) (es : List (PointGeodesicTreeEdge a y)) : IsCompact (pointGeodesicTreeCarrier p es) := by
  induction es with
  | nil => exact isCompact_singleton
  | cons e es ih => exact ih.union (isCompact_range e.continuous)

theorem pointGeodesicTree_connected {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {p : ℂ} {es : List (PointGeodesicTreeEdge a y)} (h : PointGeodesicTree a y p es) :
    IsConnected (pointGeodesicTreeCarrier p es) := by
  induction h with
  | root => exact isConnected_singleton
  | @attach es e previous hnew hold hmeet ih =>
    have hcurve : IsConnected (range e.curve) := isConnected_range e.continuous
    exact IsConnected.union ⟨e.finish, hold, ⟨⟨1, by norm_num⟩, e.curve_finish⟩⟩ ih hcurve

theorem pointGeodesicTree_edges_injective {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (e : PointGeodesicTreeEdge a y) :
    Function.Injective e.curve :=
  pointConformal_geodesic_injective ha y e.distinct e.curve e.geodesic

/-- Every finite set is contained in an actual finite embedded geodesic tree.
The construction uses at most one new arc per input point and works without
separation assumptions, curvature certificates, or global geodesic uniqueness. -/
theorem exists_pointConformal_finite_geodesic_tree {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) (S : Finset ℂ) :
    ∃ es : List (PointGeodesicTreeEdge a y), PointGeodesicTree a y p es ∧
      (S : Set ℂ) ⊆ pointGeodesicTreeCarrier p es ∧ es.length ≤ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨[], PointGeodesicTree.root, by simp, by simp⟩
  | @insert z S hzS ih =>
    obtain ⟨es, htree, hS, hn⟩ := ih
    by_cases hz : z ∈ pointGeodesicTreeCarrier p es
    · refine ⟨es, htree, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hz
        · exact hS hw
      · rw [Finset.card_insert_of_notMem hzS]
        omega
    · obtain ⟨q, hq, γ, h0, h1, hγ, hd, hinj, hmeet⟩ :=
        exists_pointConformal_nearest_attachment ha y (pointGeodesicTree_compact p es)
          ⟨p, pointGeodesicTree_root_mem p es⟩ hz
      have hzq : z ≠ q := by intro he; apply hz; rwa [he]
      let e : PointGeodesicTreeEdge a y := ⟨z, q, hzq, γ, h0, h1, hγ, hd⟩
      refine ⟨e :: es, PointGeodesicTree.attach e htree hz hq hmeet, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Or.inr ⟨⟨0, by norm_num⟩, h0⟩
        · exact Or.inl (hS hw)
      · rw [List.length_cons, Finset.card_insert_of_notMem hzS]
        omega

/-- In particular the finite tree contains every positive-exponent puncture. -/
theorem exists_pointConformal_puncture_tree {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ es : List (PointGeodesicTreeEdge a y), PointGeodesicTree a y p es ∧
      pointPunctures a y ⊆ pointGeodesicTreeCarrier p es ∧
      es.length ≤ (positivePointLocations a y).card := by
  obtain ⟨es, ht, hsub, hn⟩ := exists_pointConformal_finite_geodesic_tree ha y p (positivePointLocations a y)
  rw [positivePointLocations_eq_punctures] at hsub
  exact ⟨es, ht, hsub, hn⟩

end RepulsiveCoulomb
