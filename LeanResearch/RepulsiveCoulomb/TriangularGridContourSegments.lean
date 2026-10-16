module

public import LeanResearch.RepulsiveCoulomb.TriangularGridAffineLevels
public import LeanResearch.RepulsiveCoulomb.TriangularGridIndependence
public import LeanResearch.RepulsiveCoulomb.AffineTriangleNondegenerate
public import LeanResearch.RepulsiveCoulomb.FiniteSegmentUnion

@[expose] public section

/-! Actual finite nondegenerate segment representation of every grid-interpolant
level outside its finite exceptional value set. Loops/incidence are not assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def gridExceptionalLevels (v : (ℤ × ℤ) →₀ ℝ) : Finset ℝ := by
  classical
  exact insert 0 (v.support.image v)

theorem grid_regular_level_ne_zero (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) : t ≠ 0 := by
  intro h
  apply ht
  simp [gridExceptionalLevels, h]

theorem grid_regular_level_ne_node (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (p : ℤ × ℤ) : v p ≠ t := by
  classical
  intro he
  by_cases hz : v p = 0
  · exact grid_regular_level_ne_zero v ht (he.symm.trans hz)
  · apply ht
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨p, Finsupp.mem_support_iff.mpr hz, he⟩

theorem range_fin3_eq_triple (p : Fin 3 → ℂ) : range p = {p 0, p 1, p 2} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact mem_range_self 0
    · exact mem_range_self 1
    · exact mem_range_self 2

def gridTriangleSlice (v : (ℤ × ℤ) →₀ ℝ) (i : (ℤ × ℤ) × Bool) (t : ℝ) : Set ℂ :=
  if i.2 then gridUpperTriangle i.1 ∩ (gridUpperAffine v i.1) ⁻¹' {t}
  else gridLowerTriangle i.1 ∩ (gridLowerAffine v i.1) ⁻¹' {t}

def gridTriangleIndices (v : (ℤ × ℤ) →₀ ℝ) : Finset ((ℤ × ℤ) × Bool) :=
  (gridActiveCells v).product Finset.univ

theorem gridTriangleSlice_empty_or_segment (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (i : (ℤ × ℤ) × Bool) :
    gridTriangleSlice v i t = ∅ ∨
      ∃ p q : ℂ, p ≠ q ∧ gridTriangleSlice v i t = segment ℝ p q := by
  rcases i with ⟨b, k⟩
  cases k
  · change (gridLowerTriangle b ∩ (gridLowerAffine v b) ⁻¹' {t} = ∅) ∨
      ∃ p q : ℂ, p ≠ q ∧ gridLowerTriangle b ∩ (gridLowerAffine v b) ⁻¹' {t} = segment ℝ p q
    rw [gridLowerTriangle_eq_convexHull, range_fin3_eq_triple]
    apply affine_triangle_regular_level_nondegenerate _ _ (gridLowerVertices_affineIndependent b)
    intro j
    rw [gridLowerAffine_vertex_values]
    fin_cases j <;> exact grid_regular_level_ne_node v ht _
  · change (gridUpperTriangle b ∩ (gridUpperAffine v b) ⁻¹' {t} = ∅) ∨
      ∃ p q : ℂ, p ≠ q ∧ gridUpperTriangle b ∩ (gridUpperAffine v b) ⁻¹' {t} = segment ℝ p q
    rw [gridUpperTriangle_eq_convexHull, range_fin3_eq_triple]
    apply affine_triangle_regular_level_nondegenerate _ _ (gridUpperVertices_affineIndependent b)
    intro j
    rw [gridUpperAffine_vertex_values]
    fin_cases j <;> exact grid_regular_level_ne_node v ht _

theorem triangularGridInterpolant_level_union_slices (v : (ℤ × ℤ) →₀ ℝ)
    {t : ℝ} (ht : t ≠ 0) :
    (triangularGridInterpolant v) ⁻¹' {t} =
      ⋃ i ∈ gridTriangleIndices v, gridTriangleSlice v i t := by
  rw [triangularGridInterpolant_level_finite_affine_slices v ht]
  ext z
  constructor
  · intro hz
    obtain ⟨b, hb⟩ := mem_iUnion.mp hz
    obtain ⟨ha, hz⟩ := mem_iUnion.mp hb
    rcases hz with hl | hu
    · exact mem_iUnion.mpr ⟨(b, false), mem_iUnion.mpr
        ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_univ _⟩, hl⟩⟩
    · exact mem_iUnion.mpr ⟨(b, true), mem_iUnion.mpr
        ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_univ _⟩, hu⟩⟩
  · intro hz
    obtain ⟨⟨b, k⟩, hb⟩ := mem_iUnion.mp hz
    obtain ⟨ha, hz⟩ := mem_iUnion.mp hb
    have hba := (Finset.mem_product.mp ha).1
    refine mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hba, ?_⟩⟩
    cases k
    · exact Or.inl hz
    · exact Or.inr hz

theorem triangularGridInterpolant_regular_level_finite_segments (v : (ℤ × ℤ) →₀ ℝ)
    {t : ℝ} (ht : t ∉ gridExceptionalLevels v) :
    ∃ T : Finset (ℂ × ℂ), (∀ e ∈ T, e.1 ≠ e.2) ∧
      (triangularGridInterpolant v) ⁻¹' {t} = ⋃ e ∈ T, segment ℝ e.1 e.2 := by
  obtain ⟨T, hT, heq⟩ := finite_union_empty_or_segments (gridTriangleIndices v)
    (fun i => gridTriangleSlice v i t) (fun i _ => gridTriangleSlice_empty_or_segment v ht i)
  refine ⟨T, hT, ?_⟩
  rw [triangularGridInterpolant_level_union_slices v (grid_regular_level_ne_zero v ht), heq]

end RepulsiveCoulomb
