module

public import LeanResearch.RepulsiveCoulomb.PointActualSignedLineSides
public import LeanResearch.RepulsiveCoulomb.PointActualLinePhysicalAngleBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Uncompiled records-only successor. Actual full intervals of the fixed
sides, their nonpositive curvature coefficients and both balanced signed
masses are constructed together from the original positive-mass inputs. -/
noncomputable section
open Set
open scoped Classical
namespace RepulsiveCoulomb

/-- A geometric local model of the two actual sides in a common oriented
chart. It contains no Gauss--Bonnet equation or total-mass field. -/
def PointLinePhysicalSideWidths {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (A B : Set ℂ) (p : ℂ) (widthA widthB : ℝ) : Prop :=
  ∃ E F : OpenPartialHomeomorph ℂ ℂ, ∃ δ r θ : ℝ,
    0 < r ∧ r ≤ δ ∧ 0 < θ ∧ θ < 2 * Real.pi ∧
    widthA = (1 + coalescedPointExponent a y p / 2) * θ ∧
    widthB = (1 + coalescedPointExponent a y p / 2) * (2 * Real.pi - θ) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) r,
      (E.symm z ∈ closure A ↔ z ∈ lineClosedInitialSector δ θ) ∧
      (E.symm z ∈ closure B ↔ z ∈ lineClosedTerminalSector δ θ)) ∧
    p ∈ F.source ∧ F p = 0 ∧ F.source ⊆ E.source ∧
    (∀ z, F z = coneRadialEquiv (coalescedPointExponent a y p / 2)
      (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)) (E z)) ∧
    (∀ u ∈ F.source, ∀ v ∈ F.source,
      (pointSmoothConformalEDist a y u v).toReal = pointClassicalConeDist a y p (F u) (F v))

theorem PointActualCapGBData.fixed_side_atom_widths
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {c : ℝ → ℂ}
    (hd : ∀ u v, (pointSmoothConformalEDist a y (c u) (c v)).toReal = dist u v)
    {R : ℝ} {D : LineCapGeometry c R} (H : PointActualCapGBData ha y c D)
    (hy : ∀ j, ‖y j‖ < R)
    {A B : Set ℂ} (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hcover : A ∪ B = (range c)ᶜ) (hfA : frontier A = range c) (hfB : frontier B = range c)
    (hDA : D.inside ⊆ A) {p : ℂ} (hp : p ∈ pointLinePositiveAtomLocations a y c) :
    let Λ := (1 + coalescedPointExponent a y p / 2) * pointActualCapAngleAt H p
    PointLinePhysicalSideWidths a y A B p Λ
      (2 * Real.pi + Real.pi * coalescedPointExponent a y p - Λ) ∧
      Real.pi ≤ Λ ∧ Real.pi ≤ 2 * Real.pi + Real.pi * coalescedPointExponent a y p - Λ := by
  obtain ⟨k, hk, hpk, hκ⟩ := H.exists_vertex_at_line_atom hy hp
  obtain ⟨E, F, δ, r, hr, hrδ, hside, hpF, hF0, hFsrc, hF, hmetric⟩ :=
    H.fixed_side_physical_interval hd hy hA hB hAB hcover hfA hfB hDA hk hκ
  have hθ := H.angle_range k hk
  have hpLine : H.curve k 0 ∈ range c := by
    rw [← hpk]
    exact (Finset.mem_filter.mp hp).2
  have hbounds := pointMetricLine_full_physical_side_widths_ge_pi ha y c hd hA hB hAB hfA hfB
    hpLine E F hr hrδ hθ.1 hθ.2 hside hpF hF0 hFsrc hF hmetric
  have hcomp : 2 * Real.pi + Real.pi * coalescedPointExponent a y (H.curve k 0) -
      (1 + coalescedPointExponent a y (H.curve k 0) / 2) * H.angle k =
      (1 + coalescedPointExponent a y (H.curve k 0) / 2) * (2 * Real.pi - H.angle k) := by ring
  dsimp only
  rw [hpk, pointActualCapAngleAt_vertex H hk, hcomp]
  exact ⟨⟨E, F, δ, r, H.angle k, hr, hrδ, hθ.1, hθ.2, rfl, rfl,
    hside, hpF, hF0, hFsrc, hF, hmetric⟩, hbounds⟩

/-- This endpoint has no tail, cap, orientation, interval-angle, atom-mass
or desired-balance hypothesis. All of them are constructed from ha,y,hB. -/
theorem exists_pointConformal_actual_curvature_balanced_line_positive
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hB : 0 < pointExteriorHalfMass a) :
    ∃ c : ℝ → ℂ, Continuous c ∧
      (∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t) ∧
      ∃ A B : Set ℂ, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
        Disjoint A B ∧ A ∪ B = (range c)ᶜ ∧ frontier A = range c ∧ frontier B = range c ∧
        ∃ Λ : ℂ → ℝ,
          (∀ p ∈ pointLinePositiveAtomLocations a y c,
            PointLinePhysicalSideWidths a y A B p (Λ p)
              (2 * Real.pi + Real.pi * coalescedPointExponent a y p - Λ p) ∧
            Real.pi ≤ Λ p ∧ Real.pi ≤ 2 * Real.pi + Real.pi * coalescedPointExponent a y p - Λ p) ∧
          let νA := pointLineSignedSideCurvature a y c A Λ
          let νB := pointLineSignedSideCurvature a y c B
            (fun p => 2 * Real.pi + Real.pi * coalescedPointExponent a y p - Λ p)
          νA.support ⊆ positivePointLocations a y ∧ νB.support ⊆ positivePointLocations a y ∧
          (∀ p, νA p ≤ 0 ∧ νB p ≤ 0) ∧
          pointLineSignedSideMass a y νA = -(Real.pi * pointExteriorHalfMass a) ∧
          pointLineSignedSideMass a y νB = -(Real.pi * pointExteriorHalfMass a) ∧
          ∀ p, νA p + νB p = -(Real.pi * coalescedPointExponent a y p) := by
  obtain ⟨c, hc, hd, A, B, hA, hBo, hAc, hBc, hAB, hcover, hfA, hfB, R, D, H, hDA, hy,
      hsA, hsB, hmA, hmB, hsplit⟩ := exists_pointConformal_actual_balanced_signed_sides ha y hB
  let Λ := fun p => (1 + coalescedPointExponent a y p / 2) * pointActualCapAngleAt H p
  have hwidth (p : ℂ) (hp : p ∈ pointLinePositiveAtomLocations a y c) :=
    H.fixed_side_atom_widths hd hy hA hBo hAB hcover hfA hfB hDA hp
  have hnonpos (p : ℂ) : pointLineSignedSideCurvature a y c A Λ p ≤ 0 ∧
      pointLineSignedSideCurvature a y c B
        (fun z => 2 * Real.pi + Real.pi * coalescedPointExponent a y z - Λ z) p ≤ 0 := by
    by_cases hp : p ∈ positivePointLocations a y
    · by_cases hl : p ∈ range c
      · have hw := hwidth p (Finset.mem_filter.mpr ⟨hp, hl⟩)
        simp only [pointLineSignedSideCurvature_apply, if_pos hp, if_pos hl]
        exact ⟨sub_nonpos.mpr hw.2.1, sub_nonpos.mpr hw.2.2⟩
      · have hκ : 0 ≤ Real.pi * coalescedPointExponent a y p :=
          mul_nonneg Real.pi_pos.le (coalescedPointExponent_nonneg a y p)
        simp only [pointLineSignedSideCurvature_apply, if_pos hp, if_neg hl]
        constructor <;> split_ifs <;> linarith
    · simp [hp]
  exact ⟨c, hc, hd, A, B, hA, hBo, hAc, hBc, hAB, hcover, hfA, hfB, Λ,
    hwidth, hsA, hsB, hnonpos, hmA, hmB, hsplit⟩

end RepulsiveCoulomb
