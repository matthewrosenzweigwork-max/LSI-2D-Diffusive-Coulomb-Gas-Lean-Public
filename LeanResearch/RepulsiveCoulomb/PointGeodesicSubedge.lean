import LeanResearch.RepulsiveCoulomb.PointFiniteGeodesicTree

/-! Actual geodesic subedges obtained by affine reparametrization of the original
unit interval. These preserve the literal endpoint distance and parameter speed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def pointEdgeSubparam (s t u : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨AffineMap.lineMap s.1 t.1 u.1, (convex_Icc (0 : ℝ) 1).lineMap_mem s.2 t.2 u.2⟩

@[simp] theorem pointEdgeSubparam_zero (s t : Icc (0 : ℝ) 1) :
    pointEdgeSubparam s t ⟨0, by norm_num⟩ = s := by
  apply Subtype.ext
  simp [pointEdgeSubparam]

@[simp] theorem pointEdgeSubparam_one (s t : Icc (0 : ℝ) 1) :
    pointEdgeSubparam s t ⟨1, by norm_num⟩ = t := by
  apply Subtype.ext
  simp [pointEdgeSubparam]

theorem pointEdgeSubparam_continuous (s t : Icc (0 : ℝ) 1) :
    Continuous (pointEdgeSubparam s t) := by
  apply Continuous.subtype_mk
  simp only [pointEdgeSubparam, AffineMap.lineMap_apply_module']
  fun_prop

theorem pointEdgeSubparam_sub (s t u v : Icc (0 : ℝ) 1) :
    (pointEdgeSubparam s t v).1 - (pointEdgeSubparam s t u).1 = (v.1 - u.1) * (t.1 - s.1) := by
  simp only [pointEdgeSubparam, AffineMap.lineMap_apply_module', smul_eq_mul]
  ring

theorem pointEdgeSubparam_mem {s t : Icc (0 : ℝ) 1} (hst : s ≤ t) (u : Icc (0 : ℝ) 1) :
    pointEdgeSubparam s t u ∈ Icc s t := by
  change AffineMap.lineMap s.1 t.1 u.1 ∈ Icc s.1 t.1
  exact (convex_Icc s.1 t.1).lineMap_mem ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ u.2

theorem pointEdgeSubparam_range {s t : Icc (0 : ℝ) 1} (hst : s < t) :
    range (pointEdgeSubparam s t) = Icc s t := by
  apply Subset.antisymm
  · rintro _ ⟨u, rfl⟩
    exact pointEdgeSubparam_mem hst.le u
  · intro r hr
    have hst' : 0 < t.1 - s.1 := sub_pos.mpr hst
    have hu0 : 0 ≤ (r.1 - s.1) / (t.1 - s.1) := div_nonneg (sub_nonneg.mpr hr.1) hst'.le
    have hu1 : (r.1 - s.1) / (t.1 - s.1) ≤ 1 :=
      (div_le_one hst').mpr (sub_le_sub_right (show r.1 ≤ t.1 from hr.2) s.1)
    refine ⟨⟨(r.1 - s.1) / (t.1 - s.1), hu0, hu1⟩, ?_⟩
    apply Subtype.ext
    simp only [pointEdgeSubparam, AffineMap.lineMap_apply_module', smul_eq_mul]
    field_simp
    ring

/-- No new path is postulated: this edge is a subarc of the existing geodesic. -/
def pointGeodesicSubedge {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (y : Fin m → ℂ) (e : PointGeodesicTreeEdge a y) (s t : Icc (0 : ℝ) 1)
    (hst : s < t) : PointGeodesicTreeEdge a y where
  start := e.curve s
  finish := e.curve t
  distinct := (pointGeodesicTree_edges_injective ha y e).ne hst.ne
  curve := e.curve ∘ pointEdgeSubparam s t
  curve_start := by simp only [Function.comp_apply, pointEdgeSubparam_zero]
  curve_finish := by simp only [Function.comp_apply, pointEdgeSubparam_one]
  continuous := e.continuous.comp (pointEdgeSubparam_continuous s t)
  geodesic := by
    intro u v
    simp only [Function.comp_apply, e.geodesic, pointEdgeSubparam_sub, abs_mul]
    ring

theorem pointGeodesicSubedge_range {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (y : Fin m → ℂ) (e : PointGeodesicTreeEdge a y) (s t : Icc (0 : ℝ) 1)
    (hst : s < t) : range (pointGeodesicSubedge ha y e s t hst).curve = e.curve '' Icc s t := by
  change range (e.curve ∘ pointEdgeSubparam s t) = _
  rw [range_comp, pointEdgeSubparam_range hst]

end RepulsiveCoulomb
