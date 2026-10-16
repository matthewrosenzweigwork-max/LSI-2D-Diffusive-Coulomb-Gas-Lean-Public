import LeanResearch.RepulsiveCoulomb.PointActualCapAngleStability
import LeanResearch.RepulsiveCoulomb.PointLineCapCoalescedVertices
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

/-! Uncompiled records-only successor. Exact signed cap balance at actual
coalesced atom locations, including on-line atoms. No physical boundary mass
is assumed: it is read from the constructed full positive-side interval. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

def pointActualCapAngleAt
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {c : ℝ → ℂ} {R : ℝ} {D : LineCapGeometry c R}
    (H : PointActualCapGBData ha y c D) (p : ℂ) : ℝ :=
  ∑ k ∈ Finset.range (H.pieces.length + 1), if p = H.curve k 0 then H.angle k else 0

theorem pointActualCapAngleAt_vertex
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {c : ℝ → ℂ} {R : ℝ} {D : LineCapGeometry c R}
    (H : PointActualCapGBData ha y c D) {k : ℕ} (hk : k ≤ H.pieces.length) :
    pointActualCapAngleAt H (H.curve k 0) = H.angle k :=
  finite_boundary_selector_eq_vertex_angle H.curve H.pieces.length H.angle H.simple hk

theorem PointActualCapGBData.exists_vertex_at_line_atom
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {c : ℝ → ℂ} {R : ℝ} {D : LineCapGeometry c R}
    (H : PointActualCapGBData ha y c D) (hy : ∀ j, ‖y j‖ < R)
    {p : ℂ} (hp : p ∈ pointLinePositiveAtomLocations a y c) :
    ∃ k ≤ H.pieces.length, p = H.curve k 0 ∧
      0 < coalescedPointExponent a y (H.curve k 0) := by
  have him := pointLineCap_positive_vertex_image ha y D hy H.curve H.pieces.length
    H.consecutive H.closing H.avoid H.carrier
  rw [← him] at hp
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hp
  obtain ⟨hkrange, hkpos⟩ := Finset.mem_filter.mp hk
  exact ⟨k, by have := Finset.mem_range.mp hkrange; omega, he.symm,
    coalescedPointExponent_pos a y hkpos⟩

/-- Actual full side angles are pointwise constant on the fixed coalesced
on-line support across all sufficiently enclosing caps. -/
theorem pointActualCapAngleAt_stable
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {R S : ℝ} {D : LineCapGeometry c R} {E : LineCapGeometry c S}
    (H : PointActualCapGBData ha y c D) (J : PointActualCapGBData ha y c E)
    (hyR : ∀ j, ‖y j‖ < R) (hyS : ∀ j, ‖y j‖ < S)
    {p : ℂ} (hp : p ∈ pointLinePositiveAtomLocations a y c) :
    pointActualCapAngleAt H p = pointActualCapAngleAt J p := by
  obtain ⟨k, hk, hpk, hκ⟩ := H.exists_vertex_at_line_atom hyR hp
  obtain ⟨l, hl, hpl, _⟩ := J.exists_vertex_at_line_atom hyS hp
  have hθ := pointActualCap_same_atom_full_angle ha y c hd H J hyR hyS hk hl hκ (hpk.symm.trans hpl)
  calc
    pointActualCapAngleAt H p = H.angle k := by rw [hpk]; exact pointActualCapAngleAt_vertex H hk
    _ = J.angle l := hθ
    _ = pointActualCapAngleAt J p := by rw [hpl]; exact (pointActualCapAngleAt_vertex J hl).symm

/-- All ordinary internal turns are zero; only the two actual circle joins
and positive coalesced line atoms survive in the finite corner sum. -/
theorem PointActualCapGBData.corner_sum_decomposition
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {c : ℝ → ℂ}
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {R : ℝ} {D : LineCapGeometry c R} (H : PointActualCapGBData ha y c D)
    (hy : ∀ j, ‖y j‖ < R) :
    (∑ k ∈ Finset.range (H.pieces.length + 1), (Real.pi -
      (1 + coalescedPointExponent a y (H.curve k 0) / 2) * H.angle k)) =
      Complex.arg (deriv c D.minus / deriv (pointCircleCapArc R D.alpha D.beta) 1) +
      Complex.arg (deriv (pointCircleCapArc R D.alpha D.beta) 0 / deriv c D.plus) +
      (∑ k ∈ Finset.range (H.pieces.length + 1),
        if 0 < coalescedPointExponent a y (H.curve k 0) then
          Real.pi - (1 + coalescedPointExponent a y (H.curve k 0) / 2) * H.angle k else 0) := by
  let κ := fun k => coalescedPointExponent a y (H.curve k 0)
  let T := fun k => Real.pi - (1 + κ k / 2) * H.angle k
  let τm := Complex.arg (deriv c D.minus / deriv (pointCircleCapArc R D.alpha D.beta) 1)
  let τp := Complex.arg (deriv (pointCircleCapArc R D.alpha D.beta) 0 / deriv c D.plus)
  obtain ⟨harg0, hargN⟩ := pointLineCap_representative_join_arguments ha y c hd D hy H.pieces H.curve
    H.length_pos H.piece_eq H.circle_eq H.consecutive H.closing
  have hκ0 : κ 0 = 0 := by
    dsimp [κ]
    rw [← H.closing, H.circle_eq]
    exact lineCap_exponent_zero_of_enclosed_atoms a y hy (by rw [pointCircleCapArc_norm D.radius_pos.le])
  have hκN : κ H.pieces.length = 0 := by
    dsimp [κ]
    rw [H.circle_eq]
    exact lineCap_exponent_zero_of_enclosed_atoms a y hy (by rw [pointCircleCapArc_norm D.radius_pos.le])
  have hT0 : T 0 = τm := by
    have h := H.principal_turn 0 (Nat.zero_le _)
    simpa only [T, hκ0, zero_div, add_zero, one_mul, ite_true, harg0] using h.symm
  have hTN : T H.pieces.length = τp := by
    have h := H.principal_turn H.pieces.length le_rfl
    simpa only [T, hκN, zero_div, add_zero, one_mul,
      if_neg (Nat.ne_of_gt H.length_pos), hargN] using h.symm
  have hterm (k : ℕ) (hk : k ∈ Finset.range (H.pieces.length + 1)) :
      T k = (if k = 0 then τm else 0) + (if k = H.pieces.length then τp else 0) +
        (if 0 < κ k then T k else 0) := by
    by_cases hk0 : k = 0
    · subst k
      simp [hT0, hκ0, Nat.ne_of_gt H.length_pos, (Nat.ne_of_gt H.length_pos).symm]
    by_cases hkN : k = H.pieces.length
    · subst k
      simp [hTN, hκN, Nat.ne_of_gt H.length_pos]
    by_cases hκ : 0 < κ k
    · simp [hk0, hkN, hκ]
    · have hκzero : κ k = 0 := le_antisymm (le_of_not_gt hκ) (coalescedPointExponent_nonneg a y _)
      have hzero : T k = 0 := pointLineCap_internal_zero_mass_turn ha y c hd D.time_lt
        H.pieces H.curve H.piece_eq H.consecutive (by omega)
        (by have := Finset.mem_range.mp hk; omega) hκzero
        (by simpa only [if_neg hk0] using H.principal_turn k (by have := Finset.mem_range.mp hk; omega))
      simp [hzero, hk0, hkN, hκ]
  change (∑ k ∈ Finset.range (H.pieces.length + 1), T k) = τm + τp + _
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp [T, κ]

/-- Actual cap balance on coalesced physical atom locations, before taking
any limit or identifying the eventual interior selector. -/
theorem PointActualCapGBData.atomic_cap_balance
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {c : ℝ → ℂ}
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {R : ℝ} {D : LineCapGeometry c R} (H : PointActualCapGBData ha y c D)
    (hy : ∀ j, ‖y j‖ < R) :
    (∑ j, if y j ∈ D.inside then Real.pi * a j else 0) +
      (∑ p ∈ pointLinePositiveAtomLocations a y c,
        ((1 + coalescedPointExponent a y p / 2) * pointActualCapAngleAt H p - Real.pi)) =
      pointLineCapTurnDefect a y D := by
  let W := fun p => (1 + coalescedPointExponent a y p / 2) * pointActualCapAngleAt H p - Real.pi
  have htransport := pointLineCap_positive_vertex_sum ha y D hy H.curve H.pieces.length
    H.consecutive H.closing H.simple H.avoid H.carrier W
  have hboundary : (∑ k ∈ Finset.range (H.pieces.length + 1),
      if 0 < coalescedPointExponent a y (H.curve k 0) then
        Real.pi - (1 + coalescedPointExponent a y (H.curve k 0) / 2) * H.angle k else 0) =
      -(∑ p ∈ pointLinePositiveAtomLocations a y c, W p) := by
    rw [← htransport, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [W]
    rw [pointActualCapAngleAt_vertex H (by have := Finset.mem_range.mp hk; omega)]
    split_ifs <;> ring
  have hinterior : 2 * Real.pi * (∑ j, if y j ∈ D.inside then a j / 2 else 0) =
      ∑ j, if y j ∈ D.inside then Real.pi * a j else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hGB := H.gauss_bonnet
  rw [H.corner_sum_decomposition hd hy, hboundary, hinterior] at hGB
  dsimp [pointLineCapTurnDefect, W] at *
  linarith

end RepulsiveCoulomb
