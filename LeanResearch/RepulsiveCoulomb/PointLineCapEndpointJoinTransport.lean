module

public import LeanResearch.RepulsiveCoulomb.PointLinePieceEndpointTangents
public import LeanResearch.RepulsiveCoulomb.PointLineCapNatGerms
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order

@[expose] public section

/-! Uncompiled records-only successor. Close the two ordinary endpoint
representative conditions of the mixed cap consumer. The actual tangent
quotients are identified, not merely bounded or assumed noncuspidal. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointLineCap_representative_join_arguments
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {R : ℝ} (D : LineCapGeometry c R) (hy : ∀ j, ‖y j‖ < R)
    (es : List (PointRadialC1ArcPiece ha y (lineCapSegment c D.minus D.plus)))
    (f : ℕ → ℝ → ℂ) (hn : 0 < es.length)
    (hpieces : ∀ k (hk : k < es.length), f k = (es.get ⟨k, hk⟩).curve)
    (hcircle : f es.length = pointCircleCapArc R D.alpha D.beta)
    (hv : ∀ k < es.length, f k 1 = f (k + 1) 0)
    (hclose : f es.length 1 = f 0 0) :
    Complex.arg (deriv (f 0) 0 / deriv (f es.length) 1) =
      Complex.arg (deriv c D.minus / deriv (pointCircleCapArc R D.alpha D.beta) 1) ∧
    Complex.arg (deriv (f es.length) 0 / deriv (f (es.length - 1)) 1) =
      Complex.arg (deriv (pointCircleCapArc R D.alpha D.beta) 0 / deriv c D.plus) := by
  let e := es.get ⟨0, hn⟩
  let d := es.get ⟨es.length - 1, by omega⟩
  have he : f 0 = e.curve := hpieces 0 hn
  have hdt : f (es.length - 1) = d.curve := hpieces _ (by omega)
  have he0 : e.curve 0 = c D.minus := by rw [← he, ← hclose, hcircle, D.circle_one]
  have hd1 : d.curve 1 = c D.plus := by
    rw [← hdt, hv _ (by omega)]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ es.length), hcircle, D.circle_zero]
  have heP : e.curve 0 ∉ pointPunctures a y := by
    rw [he0]
    exact lineCap_not_puncture_of_enclosed_atoms a y hy
      (by rw [(D.crosses D.minus).mpr (Or.inl rfl)])
  have hdP : d.curve 1 ∉ pointPunctures a y := by
    rw [hd1]
    exact lineCap_not_puncture_of_enclosed_atoms a y hy
      (by rw [(D.crosses D.plus).mpr (Or.inr rfl)])
  have hi := (pointMetricLine_isClosedEmbedding ha y c hd).injective
  have heclock : D.minus + e.start.1 * (D.plus - D.minus) = D.minus :=
    hi (e.at_zero.symm.trans he0)
  have hdclock : D.minus + d.finish.1 * (D.plus - D.minus) = D.plus :=
    hi (d.at_one.symm.trans hd1)
  have hen := (e.actual_line_endpoint_tangents hd D.time_lt).1 heP
  have hdn := (d.actual_line_endpoint_tangents hd D.time_lt).2 hdP
  rw [heclock] at hen
  rw [hdclock] at hdn
  constructor
  · rw [he, hcircle, ← lineCap_arg_normalized_quotient, hen, lineCap_arg_normalized_quotient]
  · rw [hdt, hcircle, ← lineCap_arg_normalized_quotient, hdn, lineCap_arg_normalized_quotient]

/-- Actual radial crossing signs now discharge both formerly explicit
slit-plane assumptions. No ordinary join is asserted to have a radial germ. -/
theorem pointLineCap_representative_joins_non_cuspidal
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {R : ℝ} (D : LineCapGeometry c R) (hy : ∀ j, ‖y j‖ < R)
    (es : List (PointRadialC1ArcPiece ha y (lineCapSegment c D.minus D.plus)))
    (f : ℕ → ℝ → ℂ) (hn : 0 < es.length)
    (hpieces : ∀ k (hk : k < es.length), f k = (es.get ⟨k, hk⟩).curve)
    (hcircle : f es.length = pointCircleCapArc R D.alpha D.beta)
    (hv : ∀ k < es.length, f k 1 = f (k + 1) 0)
    (hclose : f es.length 1 = f 0 0)
    (hreg : ∀ k ≤ es.length, ∀ t ∈ Icc (0 : ℝ) 1, deriv (f k) t ≠ 0)
    (hm : physicalRadialProjection (c D.minus) (deriv c D.minus) < 0)
    (hp : 0 < physicalRadialProjection (c D.plus) (deriv c D.plus)) :
    deriv (f 0) 0 / deriv (f es.length) 1 ∈ Complex.slitPlane ∧
    deriv (f es.length) 0 / deriv (f (es.length - 1)) 1 ∈ Complex.slitPlane := by
  obtain ⟨harg0, hargN⟩ := pointLineCap_representative_join_arguments ha y c hd D hy es f hn
    hpieces hcircle hv hclose
  obtain ⟨hpC, hmC⟩ := lineCapArc_transverse_joins D.angle_lt D.circle_zero D.circle_one hm hp
  constructor
  · apply Complex.mem_slitPlane_iff_arg.mpr
    exact ⟨by rw [harg0]; exact Complex.slitPlane_arg_ne_pi hmC,
      div_ne_zero (hreg 0 (by omega) 0 (by norm_num)) (hreg _ le_rfl 1 (by norm_num))⟩
  · apply Complex.mem_slitPlane_iff_arg.mpr
    exact ⟨by rw [hargN]; exact Complex.slitPlane_arg_ne_pi hpC,
      div_ne_zero (hreg _ le_rfl 0 (by norm_num)) (hreg _ (by omega) 1 (by norm_num))⟩

/-- Every zero-mass internal line vertex has zero full physical turn. -/
theorem pointLineCap_internal_zero_mass_turn
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {tm tp : ℝ} (ht : tm < tp)
    (es : List (PointRadialC1ArcPiece ha y (lineCapSegment c tm tp)))
    (f : ℕ → ℝ → ℂ)
    (hpieces : ∀ k (hk : k < es.length), f k = (es.get ⟨k, hk⟩).curve)
    (hv : ∀ k < es.length, f k 1 = f (k + 1) 0)
    {k : ℕ} (hk0 : 0 < k) (hkn : k < es.length)
    (hκ : coalescedPointExponent a y (f k 0) = 0)
    {θ : ℝ} (hθ : Complex.arg (deriv (f k) 0 / deriv (f (k - 1)) 1) = Real.pi - θ) :
    Real.pi - (1 + coalescedPointExponent a y (f k 0) / 2) * θ = 0 := by
  let e := es.get ⟨k - 1, by omega⟩
  let d := es.get ⟨k, hkn⟩
  have he : f (k - 1) = e.curve := hpieces _ (by omega)
  have hd' : f k = d.curve := hpieces k hkn
  have hjoin : e.curve 1 = d.curve 0 := by
    rw [← he, ← hd']
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hv (k - 1) (by omega)
  have hp : d.curve 0 ∉ pointPunctures a y := by
    rintro ⟨j, haj, hj⟩
    have hpos := coalescedPointExponent_pos a y
      ((mem_positivePointLocations a y (f k 0)).mpr ⟨j, haj, by simpa only [hd'] using hj.symm⟩)
    rw [hκ] at hpos
    exact lt_irrefl _ hpos
  have hzero := pointLinePieces_regular_join_zero_turn hd ht e d hjoin hp
  rw [he, hd', hzero] at hθ
  have hθπ : θ = Real.pi := by linarith
  simp only [hκ, hθπ, zero_div, add_zero, one_mul, sub_self]

end RepulsiveCoulomb
