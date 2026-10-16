module

public import LeanResearch.RepulsiveCoulomb.PointActualBalancedSideLimit
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Uncompiled records-only successor. Genuine finitely supported signed
curvature coefficients on the fixed ambient complex plane. Boundary values
are pi minus the actual full physical side width; interior values are minus
pi times the coalesced original exponent. Both actual side masses are derived. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

def pointLineSignedSideCurvature {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (c : ℝ → ℂ) (A : Set ℂ) (Λ : ℂ → ℝ) : ℂ →₀ ℝ :=
  Finsupp.onFinset (positivePointLocations a y)
    (fun p => if p ∈ positivePointLocations a y then
      if p ∈ range c then Real.pi - Λ p else
        if p ∈ A then -(Real.pi * coalescedPointExponent a y p) else 0
      else 0)
    (by intro p hp; by_contra hn; simp only [if_neg hn] at hp; exact hp rfl)

def pointLineSignedSideMass {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (ν : ℂ →₀ ℝ) : ℝ := ∑ p ∈ positivePointLocations a y, ν p

@[simp] theorem pointLineSignedSideCurvature_apply
    {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (c : ℝ → ℂ) (A : Set ℂ) (Λ : ℂ → ℝ) (p : ℂ) :
    pointLineSignedSideCurvature a y c A Λ p =
      if p ∈ positivePointLocations a y then
        if p ∈ range c then Real.pi - Λ p else
          if p ∈ A then -(Real.pi * coalescedPointExponent a y p) else 0
      else 0 := rfl

theorem pointLineSignedSideCurvature_support
    {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (c : ℝ → ℂ) (A : Set ℂ) (Λ : ℂ → ℝ) :
    (pointLineSignedSideCurvature a y c A Λ).support ⊆ positivePointLocations a y := by
  intro p hp
  have hp' := Finsupp.mem_support_iff.mp hp
  by_contra h
  exact hp' (by simp [h])

/-- The finite-support mass equals the actual interior curvature sum plus
actual boundary turns, with original-source exponents coalesced exactly. -/
theorem pointLineSignedSideMass_eq
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ) (A : Set ℂ) (Λ : ℂ → ℝ) (hA : Disjoint A (range c)) :
    pointLineSignedSideMass a y (pointLineSignedSideCurvature a y c A Λ) =
      -((∑ j, if y j ∈ A then Real.pi * a j else 0) +
        ∑ p ∈ pointLinePositiveAtomLocations a y c, (Λ p - Real.pi)) := by
  have hterm (p : ℂ) (hp : p ∈ positivePointLocations a y) :
      pointLineSignedSideCurvature a y c A Λ p =
        -(if p ∈ A then Real.pi * coalescedPointExponent a y p else 0) -
        (if p ∈ range c then Λ p - Real.pi else 0) := by
    by_cases hl : p ∈ range c
    · have hpA : p ∉ A := fun h => disjoint_left.mp hA h hl
      simp [hp, hl, hpA]
    · by_cases hpA : p ∈ A <;> simp [hp, hl, hpA]
  have hinterior : (∑ p ∈ positivePointLocations a y,
      if p ∈ A then Real.pi * coalescedPointExponent a y p else 0) =
      ∑ j, if y j ∈ A then Real.pi * a j else 0 := by
    have h := pointCoalesced_location_weight_sum ha y (fun p => if p ∈ A then Real.pi else 0)
    simp only [mul_ite, mul_zero] at h
    simpa only [mul_comm] using h
  have hboundary : (∑ p ∈ positivePointLocations a y,
      if p ∈ range c then Λ p - Real.pi else 0) =
      ∑ p ∈ pointLinePositiveAtomLocations a y c, (Λ p - Real.pi) := by
    rw [pointLinePositiveAtomLocations, Finset.sum_filter]
  unfold pointLineSignedSideMass
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    hinterior, hboundary]
  ring

/-- The complementary interval is the actual other side. Pointwise summation
is the full ambient curvature, including every on-line atom exactly once. -/
theorem pointLineSignedSideCurvature_complement_split
    {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (c : ℝ → ℂ) {A B : Set ℂ} (hAB : Disjoint A B)
    (hcover : A ∪ B = (range c)ᶜ) (Λ : ℂ → ℝ) (p : ℂ) :
    pointLineSignedSideCurvature a y c A Λ p +
      pointLineSignedSideCurvature a y c B
        (fun z => 2 * Real.pi + Real.pi * coalescedPointExponent a y z - Λ z) p =
      -(Real.pi * coalescedPointExponent a y p) := by
  by_cases hp : p ∈ positivePointLocations a y
  · by_cases hl : p ∈ range c
    · simp only [pointLineSignedSideCurvature_apply, if_pos hp, if_pos hl]
      ring
    · have hside : p ∈ A ∪ B := by rw [hcover]; exact hl
      rcases hside with hA | hB
      · have hnB : p ∉ B := fun h => disjoint_left.mp hAB hA h
        simp [hp, hl, hA, hnB]
      · have hnA : p ∉ A := fun h => disjoint_left.mp hAB h hB
        simp [hp, hl, hnA, hB]
  · simp [hp, coalescedPointExponent_eq_zero_of_not_mem a y hp]

theorem pointLineSignedSideMass_complement_total
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ) {A B : Set ℂ} (hAB : Disjoint A B)
    (hcover : A ∪ B = (range c)ᶜ) (Λ : ℂ → ℝ) :
    pointLineSignedSideMass a y (pointLineSignedSideCurvature a y c A Λ) +
      pointLineSignedSideMass a y (pointLineSignedSideCurvature a y c B
        (fun z => 2 * Real.pi + Real.pi * coalescedPointExponent a y z - Λ z)) =
      -(2 * Real.pi * pointExteriorHalfMass a) := by
  unfold pointLineSignedSideMass
  rw [← Finset.sum_add_distrib]
  simp_rw [pointLineSignedSideCurvature_complement_split a y c hAB hcover Λ]
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, sum_coalescedPointExponent ha y]
  unfold pointExteriorHalfMass
  rw [← Finset.sum_div]
  ring

/-- Original finite nonnegative data and positive B construct an actual
metric line, its actual complementary sides and genuine signed coefficients
with both total masses -pi*B. The reference H records the full actual physical
side intervals; its geometry is available from fixed_side_physical_interval. -/
theorem exists_pointConformal_actual_balanced_signed_sides
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hB : 0 < pointExteriorHalfMass a) :
    ∃ c : ℝ → ℂ, Continuous c ∧
      (∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t) ∧
      ∃ A B : Set ℂ, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
        Disjoint A B ∧ A ∪ B = (range c)ᶜ ∧ frontier A = range c ∧ frontier B = range c ∧
        ∃ R : ℝ, ∃ D : LineCapGeometry c R, ∃ H : PointActualCapGBData ha y c D,
          D.inside ⊆ A ∧ (∀ j, ‖y j‖ < R) ∧
          let Λ := fun p => (1 + coalescedPointExponent a y p / 2) * pointActualCapAngleAt H p
          let νA := pointLineSignedSideCurvature a y c A Λ
          let νB := pointLineSignedSideCurvature a y c B
            (fun p => 2 * Real.pi + Real.pi * coalescedPointExponent a y p - Λ p)
          νA.support ⊆ positivePointLocations a y ∧ νB.support ⊆ positivePointLocations a y ∧
          pointLineSignedSideMass a y νA = -(Real.pi * pointExteriorHalfMass a) ∧
          pointLineSignedSideMass a y νB = -(Real.pi * pointExteriorHalfMass a) ∧
          ∀ p, νA p + νB p = -(Real.pi * coalescedPointExponent a y p) := by
  obtain ⟨c, hc, hd, A, B, hA, hBo, hAc, hBc, hAB, hcover, hfA, hfB, R, D, H, hDA, hy, hbal⟩ :=
    exists_pointConformal_actual_balanced_line_side ha y hB
  let Λ := fun p => (1 + coalescedPointExponent a y p / 2) * pointActualCapAngleAt H p
  have hAline : Disjoint A (range c) := by
    apply disjoint_left.mpr
    intro p hp hl
    have hpUV : p ∈ A ∪ B := Or.inl hp
    rw [hcover] at hpUV
    exact hpUV hl
  have hmassA : pointLineSignedSideMass a y (pointLineSignedSideCurvature a y c A Λ) =
      -(Real.pi * pointExteriorHalfMass a) := by
    rw [pointLineSignedSideMass_eq ha y c A Λ hAline]
    exact congrArg Neg.neg hbal
  have htotal := pointLineSignedSideMass_complement_total ha y c hAB hcover Λ
  refine ⟨c, hc, hd, A, B, hA, hBo, hAc, hBc, hAB, hcover, hfA, hfB, R, D, H, hDA, hy,
    pointLineSignedSideCurvature_support a y c A Λ,
    pointLineSignedSideCurvature_support a y c B _, hmassA, ?_,
    pointLineSignedSideCurvature_complement_split a y c hAB hcover Λ⟩
  linarith

end RepulsiveCoulomb
