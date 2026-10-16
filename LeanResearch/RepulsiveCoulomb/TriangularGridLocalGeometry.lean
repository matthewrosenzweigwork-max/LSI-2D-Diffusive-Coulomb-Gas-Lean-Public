module

public import LeanResearch.RepulsiveCoulomb.TriangularContourGeometry

@[expose] public section

/-! Local uniqueness of the actual regular-grid triangle away from its edges. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem int_cell_fraction_unique (k m : ℤ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hl : 0 ≤ (k : ℝ) + r - m) (hu : (k : ℝ) + r - m ≤ 1) : m = k := by
  have hlo : (k : ℝ) - 1 < m := by linarith
  have hhi : (m : ℝ) < k + 1 := by linarith
  have hlo' : k - 1 < m := by exact_mod_cast hlo
  have hhi' : m < k + 1 := by exact_mod_cast hhi
  omega

theorem int_cell_integer_options (k m : ℤ)
    (hl : 0 ≤ (k : ℝ) - m) (hu : (k : ℝ) - m ≤ 1) : m = k ∨ m = k - 1 := by
  have hl' : (0 : ℤ) ≤ k - m := by exact_mod_cast hl
  have hu' : k - m ≤ (1 : ℤ) := by exact_mod_cast hu
  omega

theorem gridTriangleRegion_coordinate_bounds {i : GridTriangle} {z : ℂ}
    (hz : z ∈ gridTriangleRegion i) :
    0 ≤ z.re - (i.1.1 : ℝ) ∧ z.re - (i.1.1 : ℝ) ≤ 1 ∧
    0 ≤ z.im - (i.1.2 : ℝ) ∧ z.im - (i.1.2 : ℝ) ≤ 1 := by
  rcases i with ⟨b, k⟩
  cases k
  · change 0 ≤ z.im - (b.2 : ℝ) ∧ z.im - (b.2 : ℝ) ≤ z.re - (b.1 : ℝ) ∧
      z.re - (b.1 : ℝ) ≤ 1 at hz
    exact ⟨hz.1.trans hz.2.1, hz.2.2, hz.1, hz.2.1.trans hz.2.2⟩
  · change 0 ≤ z.re - (b.1 : ℝ) ∧ z.re - (b.1 : ℝ) ≤ z.im - (b.2 : ℝ) ∧
      z.im - (b.2 : ℝ) ≤ 1 at hz
    exact ⟨hz.1, hz.2.1.trans hz.2.2, hz.1.trans hz.2.1, hz.2.2⟩

def gridOpenTriangle (i : GridTriangle) : Set ℂ :=
  if i.2 then {z | 0 < z.re - (i.1.1 : ℝ) ∧ z.re - (i.1.1 : ℝ) < z.im - (i.1.2 : ℝ) ∧
    z.im - (i.1.2 : ℝ) < 1}
  else {z | 0 < z.im - (i.1.2 : ℝ) ∧ z.im - (i.1.2 : ℝ) < z.re - (i.1.1 : ℝ) ∧
    z.re - (i.1.1 : ℝ) < 1}

theorem gridOpenTriangle_coordinate_bounds {i : GridTriangle} {z : ℂ}
    (hz : z ∈ gridOpenTriangle i) :
    0 < z.re - (i.1.1 : ℝ) ∧ z.re - (i.1.1 : ℝ) < 1 ∧
    0 < z.im - (i.1.2 : ℝ) ∧ z.im - (i.1.2 : ℝ) < 1 := by
  rcases i with ⟨b, k⟩
  cases k
  · exact ⟨hz.1.trans hz.2.1, hz.2.2, hz.1, hz.2.1.trans hz.2.2⟩
  · exact ⟨hz.1, hz.2.1.trans hz.2.2, hz.1.trans hz.2.1, hz.2.2⟩

theorem gridOpenTriangle_subset_region (i : GridTriangle) :
    gridOpenTriangle i ⊆ gridTriangleRegion i := by
  rcases i with ⟨b, k⟩
  cases k <;> intro z hz <;> exact ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩

theorem gridOpenTriangle_region_unique {i j : GridTriangle} {z : ℂ}
    (hi : z ∈ gridOpenTriangle i) (hj : z ∈ gridTriangleRegion j) : i = j := by
  have hiB := gridOpenTriangle_coordinate_bounds hi
  have hjB := gridTriangleRegion_coordinate_bounds hj
  have hx : j.1.1 = i.1.1 := int_cell_fraction_unique i.1.1 j.1.1 hiB.1 hiB.2.1
    (by linarith [hjB.1]) (by linarith [hjB.2.1])
  have hy : j.1.2 = i.1.2 := int_cell_fraction_unique i.1.2 j.1.2 hiB.2.2.1 hiB.2.2.2
    (by linarith [hjB.2.2.1]) (by linarith [hjB.2.2.2])
  have hb : j.1 = i.1 := Prod.ext hx hy
  rcases i with ⟨b, k⟩
  rcases j with ⟨c, l⟩
  change c = b at hb
  subst c
  cases k <;> cases l <;> first
    | rfl
    | (exfalso
       simp [gridOpenTriangle, gridTriangleRegion, gridLowerTriangle, gridUpperTriangle,
         complexLatticePoint] at hi hj
       linarith [hi.2.1, hj.2.1])

end RepulsiveCoulomb
