module

public import LeanResearch.RepulsiveCoulomb.TriangularGridHatCell

@[expose] public section

/-! Exact lattice nodal values and local support of the regular triangular hats. -/
noncomputable section
namespace RepulsiveCoulomb

def complexLatticePoint (p : ℤ × ℤ) : ℂ := ⟨p.1, p.2⟩

theorem complexLatticePoint_sub (p q : ℤ × ℤ) :
    complexLatticePoint (p - q) = complexLatticePoint p - complexLatticePoint q := by
  apply Complex.ext <;> simp [complexLatticePoint]

theorem triangularGridHat_ne_zero_coordinates {z : ℂ} (hz : triangularGridHat z ≠ 0) :
    |z.re| < 1 ∧ |z.im| < 1 := by
  have hm : max |z.re| (max |z.im| |z.re - z.im|) < 1 := by
    by_contra h
    have hh : 1 - max |z.re| (max |z.im| |z.re - z.im|) ≤ 0 := by linarith
    exact hz (max_eq_left hh)
  exact ⟨(le_max_left _ _).trans_lt hm,
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hm⟩

theorem triangularGridHat_lattice (p : ℤ × ℤ) :
    triangularGridHat (complexLatticePoint p) = if p = 0 then 1 else 0 := by
  classical
  by_cases hp : p = 0
  · subst p
    simp [complexLatticePoint, triangularGridHat]
  · rw [if_neg hp]
    by_contra h
    obtain ⟨hx, hy⟩ := triangularGridHat_ne_zero_coordinates h
    change |(p.1 : ℝ)| < 1 at hx
    change |(p.2 : ℝ)| < 1 at hy
    have hx' : |p.1| < (1 : ℤ) := by exact_mod_cast hx
    have hy' : |p.2| < (1 : ℤ) := by exact_mod_cast hy
    have h1 : p.1 = 0 := by have hh := abs_lt.mp hx'; omega
    have h2 : p.2 = 0 := by have hh := abs_lt.mp hy'; omega
    exact hp (Prod.ext h1 h2)

theorem triangularGridHat_lattice_difference (p q : ℤ × ℤ) :
    triangularGridHat (complexLatticePoint p - complexLatticePoint q) =
      if p = q then 1 else 0 := by
  rw [← complexLatticePoint_sub]
  simpa only [sub_eq_zero] using triangularGridHat_lattice (p - q)

theorem triangularGridHat_unit_cell_indices {z : ℂ}
    (hx0 : 0 ≤ z.re) (hx1 : z.re ≤ 1) (hy0 : 0 ≤ z.im) (hy1 : z.im ≤ 1)
    (p : ℤ × ℤ) (hp : triangularGridHat (z - complexLatticePoint p) ≠ 0) :
    (p.1 = 0 ∨ p.1 = 1) ∧ (p.2 = 0 ∨ p.2 = 1) := by
  obtain ⟨hx, hy⟩ := triangularGridHat_ne_zero_coordinates hp
  simp only [Complex.sub_re, Complex.sub_im, complexLatticePoint] at hx hy
  have hxl : (-1 : ℝ) < (p.1 : ℝ) := by have := (abs_lt.mp hx).2; linarith
  have hxu : (p.1 : ℝ) < 2 := by have := (abs_lt.mp hx).1; linarith
  have hyl : (-1 : ℝ) < (p.2 : ℝ) := by have := (abs_lt.mp hy).2; linarith
  have hyu : (p.2 : ℝ) < 2 := by have := (abs_lt.mp hy).1; linarith
  have hxl' : (-1 : ℤ) < p.1 := by exact_mod_cast hxl
  have hxu' : p.1 < (2 : ℤ) := by exact_mod_cast hxu
  have hyl' : (-1 : ℤ) < p.2 := by exact_mod_cast hyl
  have hyu' : p.2 < (2 : ℤ) := by exact_mod_cast hyu
  omega

end RepulsiveCoulomb
