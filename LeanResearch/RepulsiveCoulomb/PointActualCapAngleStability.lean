module

public import LeanResearch.RepulsiveCoulomb.PointActualCapGaussBonnetData
public import LeanResearch.RepulsiveCoulomb.PointLineAtomEndpointTangents
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order

@[expose] public section

/-! Uncompiled records-only successor. The full ORIGINAL radial-corner angle
is independent of the enclosing cap radius. Atom-safe equality of outgoing
and incoming normalized representative derivatives is proved from the same
oriented metric line, not assumed. The actual positive-side interval already
has width in (0,2pi), so its exact pi-minus-width turn recovers the full width. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem PointActualCapGBData.positive_vertex_internal
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {c : ℝ → ℂ} {R : ℝ} {D : LineCapGeometry c R}
    (H : PointActualCapGBData ha y c D) (hy : ∀ j, ‖y j‖ < R)
    {k : ℕ} (hk : k ≤ H.pieces.length)
    (hκ : 0 < coalescedPointExponent a y (H.curve k 0)) : 0 < k ∧ k < H.pieces.length := by
  have hfirst : coalescedPointExponent a y (H.curve 0 0) = 0 := by
    rw [← H.closing, H.circle_eq]
    exact lineCap_exponent_zero_of_enclosed_atoms a y hy (by rw [pointCircleCapArc_norm D.radius_pos.le])
  have hlast : coalescedPointExponent a y (H.curve H.pieces.length 0) = 0 := by
    rw [H.circle_eq]
    exact lineCap_exponent_zero_of_enclosed_atoms a y hy (by rw [pointCircleCapArc_norm D.radius_pos.le])
  have hk0 : k ≠ 0 := by intro he; rw [he, hfirst] at hκ; exact lt_irrefl _ hκ
  have hkn : k ≠ H.pieces.length := by intro he; rw [he, hlast] at hκ; exact lt_irrefl _ hκ
  omega

/-- Both endpoint directions are compared on the literal original line, even
at a positive atom. This preserves the incoming/outgoing order, so it cannot
replace a reflex interval by its complement. -/
theorem pointActualCap_same_atom_full_angle
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {R S : ℝ} {D : LineCapGeometry c R} {E : LineCapGeometry c S}
    (H : PointActualCapGBData ha y c D) (J : PointActualCapGBData ha y c E)
    (hyR : ∀ j, ‖y j‖ < R) (hyS : ∀ j, ‖y j‖ < S)
    {k l : ℕ} (hk : k ≤ H.pieces.length) (hl : l ≤ J.pieces.length)
    (hκ : 0 < coalescedPointExponent a y (H.curve k 0))
    (hp : H.curve k 0 = J.curve l 0) : H.angle k = J.angle l := by
  obtain ⟨hk0, hkn⟩ := H.positive_vertex_internal hyR hk hκ
  obtain ⟨hl0, hln⟩ := J.positive_vertex_internal hyS hl (by rwa [← hp])
  let e := H.pieces.get ⟨k, hkn⟩
  let d := H.pieces.get ⟨k - 1, by omega⟩
  let e' := J.pieces.get ⟨l, hln⟩
  let d' := J.pieces.get ⟨l - 1, by omega⟩
  have he : H.curve k = e.curve := H.piece_eq k hkn
  have hd0 : H.curve (k - 1) = d.curve := H.piece_eq _ (by omega)
  have he' : J.curve l = e'.curve := J.piece_eq l hln
  have hd' : J.curve (l - 1) = d'.curve := J.piece_eq _ (by omega)
  have hbase : e.curve 0 = e'.curve 0 := by rw [← he, ← he']; exact hp
  have hj : H.curve (k - 1) 1 = H.curve k 0 := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using H.consecutive (k - 1) (by omega)
  have hj' : J.curve (l - 1) 1 = J.curve l 0 := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ l)] using J.consecutive (l - 1) (by omega)
  have hfinish : d.curve 1 = d'.curve 1 := by rw [← hd0, ← hd', hj, hj']; exact hp
  have hout := e.same_line_start_tangent hd D.time_lt E.time_lt e' hbase
  have hin := d.same_line_finish_tangent hd D.time_lt E.time_lt d' hfinish
  have harg : Complex.arg (deriv (H.curve k) 0 / deriv (H.curve (k - 1)) 1) =
      Complex.arg (deriv (J.curve l) 0 / deriv (J.curve (l - 1)) 1) := by
    calc
      _ = Complex.arg ((deriv (H.curve k) 0 / (‖deriv (H.curve k) 0‖ : ℂ)) /
          (deriv (H.curve (k - 1)) 1 / (‖deriv (H.curve (k - 1)) 1‖ : ℂ))) :=
        (lineCap_arg_normalized_quotient _ _).symm
      _ = Complex.arg ((deriv (J.curve l) 0 / (‖deriv (J.curve l) 0‖ : ℂ)) /
          (deriv (J.curve (l - 1)) 1 / (‖deriv (J.curve (l - 1)) 1‖ : ℂ))) := by
        rw [he, hd0, he', hd', hout, hin]
      _ = _ := lineCap_arg_normalized_quotient _ _
  have hθH := H.principal_turn k hk
  have hθJ := J.principal_turn l hl
  rw [if_neg (by omega : k ≠ 0)] at hθH
  rw [if_neg (by omega : l ≠ 0)] at hθJ
  linarith

end RepulsiveCoulomb
