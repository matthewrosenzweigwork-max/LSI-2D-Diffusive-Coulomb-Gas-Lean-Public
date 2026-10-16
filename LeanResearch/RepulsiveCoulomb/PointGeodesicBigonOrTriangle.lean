module

public import LeanResearch.RepulsiveCoulomb.PointGeodesicTriangleJordan
public import LeanResearch.RepulsiveCoulomb.PointGeodesicJordanBigon

@[expose] public section

/-! A genuinely shorter shortcut across two locally separated minimizing germs
produces an actual simple minimizing bigon or an actual simple minimizing
triangle. This reduction assumes no global geodesic uniqueness theorem. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

structure PointSimpleGeodesicBigon {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) where
  left : PointGeodesicTreeEdge a y
  right : PointGeodesicTreeEdge a y
  start_eq : left.start = right.start
  finish_eq : left.finish = right.finish
  intersection : range left.curve ∩ range right.curve = {left.start, left.finish}
  jordan : Schoenflies.IsJordanCurve
    (Complex.orthonormalBasisOneI.repr '' (range left.curve ∪ range right.curve))

theorem pointGeodesic_separated_prefixes_ne {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (A B : PointGeodesicTreeEdge a y)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ s t : Icc (0 : ℝ) 1, 0 < s.1 → s.1 ≤ ε → 0 < t.1 → t.1 ≤ ε →
      A.curve s ≠ B.curve t)
    (u v : Icc (0 : ℝ) 1) (hu : 0 < u.1) (hv : 0 < v.1) :
    (pointGeodesicSubedge ha y A ⟨0, by norm_num⟩ u hu).curve ≠
      (pointGeodesicSubedge ha y B ⟨0, by norm_num⟩ v hv).curve := by
  have hτpos : 0 < min (ε / 2) (1 / 2 : ℝ) := lt_min (by positivity) (by norm_num)
  have hτ1 : min (ε / 2) (1 / 2 : ℝ) ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let τ : Icc (0 : ℝ) 1 := ⟨min (ε / 2) (1 / 2 : ℝ), hτpos.le, hτ1⟩
  have hτε : τ.1 ≤ ε := (min_le_left _ _).trans (by linarith)
  let s := pointEdgeSubparam ⟨0, by norm_num⟩ u τ
  let t := pointEdgeSubparam ⟨0, by norm_num⟩ v τ
  have hs : s.1 = τ.1 * u.1 := by
    simp [s, pointEdgeSubparam, AffineMap.lineMap_apply_module', smul_eq_mul]
  have ht : t.1 = τ.1 * v.1 := by
    simp [t, pointEdgeSubparam, AffineMap.lineMap_apply_module', smul_eq_mul]
  have hs0 : 0 < s.1 := hs.symm ▸ mul_pos hτpos hu
  have ht0 : 0 < t.1 := ht.symm ▸ mul_pos hτpos hv
  have hsε : s.1 ≤ ε := by rw [hs]; exact (mul_le_of_le_one_right hτpos.le u.2.2).trans hτε
  have htε : t.1 ≤ ε := by rw [ht]; exact (mul_le_of_le_one_right hτpos.le v.2.2).trans hτε
  intro he
  have hh := congrFun he τ
  exact hsep s t hs0 hsε ht0 htε hh

/-- Any additional intersection of two locally separated minimizing legs gives
a simple Jordan bigon by the already constructed synchronized extraction. -/
theorem pointGeodesic_shared_point_yields_bigon {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (A B : PointGeodesicTreeEdge a y)
    (q : ℂ) (hA : A.start = q) (hB : B.start = q) {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ s t : Icc (0 : ℝ) 1, 0 < s.1 → s.1 ≤ ε → 0 < t.1 → t.1 ≤ ε →
      A.curve s ≠ B.curve t)
    {w : ℂ} (hwA : w ∈ range A.curve) (hwB : w ∈ range B.curve) (hwq : w ≠ q) :
    Nonempty (PointSimpleGeodesicBigon a y) := by
  obtain ⟨u, hu⟩ := hwA
  obtain ⟨v, hv⟩ := hwB
  have hu0 : 0 < u.1 := by
    apply lt_of_le_of_ne u.2.1
    intro h
    apply hwq
    have he : u = ⟨0, by norm_num⟩ := Subtype.ext h.symm
    rw [← hu, he, A.curve_start, hA]
  have hv0 : 0 < v.1 := by
    apply lt_of_le_of_ne v.2.1
    intro h
    apply hwq
    have he : v = ⟨0, by norm_num⟩ := Subtype.ext h.symm
    rw [← hv, he, B.curve_start, hB]
  let A' := pointGeodesicSubedge ha y A ⟨0, by norm_num⟩ u hu0
  let B' := pointGeodesicSubedge ha y B ⟨0, by norm_num⟩ v hv0
  have hA'0 : A'.curve ⟨0, by norm_num⟩ = q := A'.curve_start.trans (A.curve_start.trans hA)
  have hB'0 : B'.curve ⟨0, by norm_num⟩ = q := B'.curve_start.trans (B.curve_start.trans hB)
  have hA'1 : A'.curve ⟨1, by norm_num⟩ = w := A'.curve_finish.trans hu
  have hB'1 : B'.curve ⟨1, by norm_num⟩ = w := B'.curve_finish.trans hv
  have hdA := A'.geodesic
  have hdB := B'.geodesic
  change ∀ s t, (pointSmoothConformalEDist a y (A'.curve s) (A'.curve t)).toReal =
    |t.1 - s.1| * (pointSmoothConformalEDist a y (A.curve ⟨0, by norm_num⟩) (A.curve u)).toReal at hdA
  change ∀ s t, (pointSmoothConformalEDist a y (B'.curve s) (B'.curve t)).toReal =
    |t.1 - s.1| * (pointSmoothConformalEDist a y (B.curve ⟨0, by norm_num⟩) (B.curve v)).toReal at hdB
  rw [A.curve_start, hA, hu] at hdA
  rw [B.curve_start, hB, hv] at hdB
  obtain ⟨p, z, hpz, δ₁, δ₂, h10, h11, h20, h21, hd₁, hd₂, hmeet, hj⟩ :=
    exists_pointConformal_jordan_geodesic_bigon ha y hwq.symm A'.curve B'.curve
      hA'0 hA'1 hB'0 hB'1 hdA hdB
      (pointGeodesic_separated_prefixes_ne ha y A B hε hsep u v hu0 hv0)
  let E₁ : PointGeodesicTreeEdge a y :=
    ⟨p, z, hpz, δ₁, h10, h11, pointConformal_geodesic_continuous ha y δ₁ hd₁, hd₁⟩
  let E₂ : PointGeodesicTreeEdge a y :=
    ⟨p, z, hpz, δ₂, h20, h21, pointConformal_geodesic_continuous ha y δ₂ hd₂, hd₂⟩
  refine ⟨⟨E₁, E₂, rfl, rfl, hmeet, ?_⟩⟩
  simpa only [image_union, range_comp] using hj

/-- A shorter shortcut across locally separated actual minimizing legs forces
one of two concrete Jordan configurations. Neither global uniqueness nor a
Gauss--Bonnet conclusion is assumed to obtain this geometric alternative. -/
theorem pointGeodesic_shortcut_bigon_or_triangle {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (A B : PointGeodesicTreeEdge a y)
    (q : ℂ) (hA : A.start = q) (hB : B.start = q) {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ s t : Icc (0 : ℝ) 1, 0 < s.1 → s.1 ≤ ε → 0 < t.1 → t.1 ≤ ε →
      A.curve s ≠ B.curve t)
    (hshort : (pointSmoothConformalEDist a y A.finish B.finish).toReal <
      (pointSmoothConformalEDist a y A.finish q).toReal +
        (pointSmoothConformalEDist a y q B.finish).toReal) :
    Nonempty (PointSimpleGeodesicBigon a y) ∨
      ∃ T : PointSimpleGeodesicTriangle a y q,
        range T.left.curve ⊆ range A.curve ∧ range T.right.curve ⊆ range B.curve ∧
        Schoenflies.IsJordanCurve (Complex.orthonormalBasisOneI.repr ''
          (range T.left.curve ∪ range T.right.curve ∪ range T.cross.curve)) := by
  classical
  by_cases hmeet : range A.curve ∩ range B.curve = {q}
  · have hneq : A.finish ≠ B.finish := by
      intro he
      have hm : A.finish ∈ range A.curve ∩ range B.curve :=
        ⟨⟨⟨1, by norm_num⟩, A.curve_finish⟩,
          ⟨⟨1, by norm_num⟩, B.curve_finish.trans he.symm⟩⟩
      have hq : A.finish = q := mem_singleton_iff.mp (hmeet ▸ hm)
      exact A.distinct (hA.trans hq.symm)
    obtain ⟨γ, h0, h1, hc, hd⟩ := exists_pointConformal_geodesic ha y A.finish B.finish
    let E : PointGeodesicTreeEdge a y := ⟨A.finish, B.finish, hneq, γ, h0, h1, hc, hd⟩
    obtain ⟨T, hTA, hTB, hTC⟩ := exists_pointGeodesic_simple_triangle_subedges ha y A B E q
      hA hB rfl rfl hmeet hshort
    exact Or.inr ⟨T, hTA, hTB, pointSimpleGeodesicTriangle_jordan ha y T⟩
  · have hqmem : q ∈ range A.curve ∩ range B.curve :=
      ⟨⟨⟨0, by norm_num⟩, A.curve_start.trans hA⟩,
        ⟨⟨0, by norm_num⟩, B.curve_start.trans hB⟩⟩
    have hnot : ¬ range A.curve ∩ range B.curve ⊆ {q} := fun h ↦
      hmeet (Subset.antisymm h (singleton_subset_iff.mpr hqmem))
    obtain ⟨w, hw, hwq⟩ := Set.not_subset.mp hnot
    exact Or.inl (pointGeodesic_shared_point_yields_bigon ha y A B q hA hB hε hsep
      hw.1 hw.2 (by simpa only [mem_singleton_iff] using hwq))

end RepulsiveCoulomb
