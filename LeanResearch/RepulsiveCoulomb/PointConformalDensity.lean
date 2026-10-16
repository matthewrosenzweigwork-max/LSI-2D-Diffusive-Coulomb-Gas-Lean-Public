module

public import LeanResearch.RepulsiveCoulomb.PointExponentCoalescence
public import LeanResearch.RepulsiveCoulomb.PointWeightScore
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

@[expose] public section

/-! The literal conformal density used in the Bonk--Lang reduction.
The logarithmic density is harmonic away from positive-exponent punctures.
No global curvature-measure identity or uniformization theorem is assumed here.
Harmonicity uses Mathlib's theorem `AnalyticAt.harmonicAt_log_norm` (Stefan Kebekus). -/
noncomputable section
open MeasureTheory Set InnerProductSpace
open scoped BigOperators Topology
namespace RepulsiveCoulomb

def pointConformalDensity {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) : ℝ :=
  Real.sqrt (rawPointWeight a y z)

def pointConformalLog {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, a j * Real.log ‖z - y j‖

theorem pointConformalDensity_nonneg {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (z : ℂ) : 0 ≤ pointConformalDensity a y z := Real.sqrt_nonneg _

theorem pointConformalDensity_sq {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (z : ℂ) : pointConformalDensity a y z ^ 2 = rawPointWeight a y z :=
  Real.sq_sqrt (rawPointWeight_nonneg a y z)

theorem pointConformalDensity_continuous {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) : Continuous (pointConformalDensity a y) :=
  (rawPointWeight_continuous ha y).sqrt

theorem pointConformalDensity_pos_off_punctures {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ} (hz : z ∉ pointPunctures a y) :
    0 < pointConformalDensity a y z := by
  apply Real.sqrt_pos.mpr
  rw [rawPointWeight_eq_pointWeight_zero]
  exact pointWeight_pos_off_punctures 0 ha y hz

theorem exp_two_pointConformalLog {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ} (hz : z ∉ pointPunctures a y) :
    Real.exp (2 * pointConformalLog a y z) = rawPointWeight a y z := by
  have he : 2 * pointConformalLog a y z = pointLogWeight 0 a y z := by
    simp [pointConformalLog, pointLogWeight]
  rw [he, rawPointWeight_eq_pointWeight_zero]
  exact exp_pointLogWeight_off_punctures 0 ha y hz

theorem exp_pointConformalLog {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ} (hz : z ∉ pointPunctures a y) :
    Real.exp (pointConformalLog a y z) = pointConformalDensity a y z := by
  have hsq : Real.exp (pointConformalLog a y z) ^ 2 = rawPointWeight a y z := by
    rw [← Real.exp_nat_mul]
    exact exp_two_pointConformalLog ha y hz
  have hd := pointConformalDensity_sq a y z
  nlinarith [Real.exp_pos (pointConformalLog a y z), pointConformalDensity_nonneg a y z]

theorem pointConformalLog_eq_half_log {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ} (hz : z ∉ pointPunctures a y) :
    pointConformalLog a y z = (1 / 2 : ℝ) * Real.log (rawPointWeight a y z) := by
  rw [← exp_two_pointConformalLog ha y hz, Real.log_exp]
  ring

/-- A finite sum of the regular logarithmic factors is harmonic off actual punctures. -/
theorem pointConformalLog_harmonicAt {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ} (hz : z ∉ pointPunctures a y) :
    HarmonicAt (pointConformalLog a y) z := by
  have hf (j : Fin m) : HarmonicAt (fun x : ℂ ↦ a j * Real.log ‖x - y j‖) z := by
    by_cases hj : a j = 0
    · simp [hj]
    · have hne : z - y j ≠ 0 := sub_ne_zero.mpr fun h ↦
        hz ⟨j, lt_of_le_of_ne (ha j) (Ne.symm hj), h⟩
      have hg : AnalyticAt ℂ (fun x : ℂ ↦ x - y j) z := by fun_prop
      convert (hg.harmonicAt_log_norm hne).const_smul (c := a j) using 1
  have hsum (s : Finset (Fin m)) : HarmonicAt
      (fun x : ℂ ↦ ∑ j ∈ s, a j * Real.log ‖x - y j‖) z := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      convert (hf j).add ih using 1
      ext x
      simp [Finset.sum_insert, hj]
  convert (hsum Finset.univ).const_smul (c := (1 / 2 : ℝ)) using 1
  rfl

theorem pointConformalLog_harmonicOnNhd {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    HarmonicOnNhd (pointConformalLog a y) (pointPunctures a y)ᶜ :=
  fun _ hz ↦ pointConformalLog_harmonicAt ha y hz

end RepulsiveCoulomb
