import LeanResearch.RepulsiveCoulomb.TriangularGridHatLattice
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Data.Finsupp.Basic
import Mathlib.Topology.Algebra.Group.ContinuousDiv

/-! An actual finite nodal interpolant on the regular diagonal grid. It is
compactly supported and globally Lipschitz, with exact prescribed lattice values. -/
noncomputable section
open scoped BigOperators NNReal
namespace RepulsiveCoulomb

def triangularGridInterpolant (v : (ℤ × ℤ) →₀ ℝ) (z : ℂ) : ℝ :=
  ∑ p ∈ v.support, v p * triangularGridHat (z - complexLatticePoint p)

theorem triangularGridHat_translate_lipschitz (p : ℤ × ℤ) :
    LipschitzWith 2 (fun z : ℂ => triangularGridHat (z - complexLatticePoint p)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [dist_sub_right] using triangularGridHat_lipschitz.dist_le_mul
    (z - complexLatticePoint p) (w - complexLatticePoint p)

theorem triangularGridInterpolant_lipschitz (v : (ℤ × ℤ) →₀ ℝ) :
    LipschitzWith (∑ p ∈ v.support, ‖v p‖₊ * 2) (triangularGridInterpolant v) := by
  classical
  have hp (p : ℤ × ℤ) : LipschitzWith (‖v p‖₊ * 2)
      (fun z : ℂ => v p * triangularGridHat (z - complexLatticePoint p)) := by
    simpa only [Function.comp_def, smul_eq_mul] using
      (lipschitzWith_smul (v p)).comp (triangularGridHat_translate_lipschitz p)
  have hall (s : Finset (ℤ × ℤ)) : LipschitzWith (∑ p ∈ s, ‖v p‖₊ * 2)
      (fun z : ℂ => ∑ p ∈ s, v p * triangularGridHat (z - complexLatticePoint p)) := by
    induction s using Finset.induction_on with
    | empty => simpa using (LipschitzWith.const (0 : ℝ) : LipschitzWith 0 (fun _ : ℂ => 0))
    | @insert p s hps ih =>
      simpa only [Finset.sum_insert hps] using (hp p).add ih
  exact hall v.support

theorem triangularGridInterpolant_hasCompactSupport (v : (ℤ × ℤ) →₀ ℝ) :
    HasCompactSupport (triangularGridInterpolant v) := by
  have hp (p : ℤ × ℤ) : HasCompactSupport
      (fun z : ℂ => v p * triangularGridHat (z - complexLatticePoint p)) := by
    have h := triangularGridHat_hasCompactSupport.comp_homeomorph
      (Homeomorph.subRight (complexLatticePoint p))
    exact h.mul_left
  have h := HasCompactSupport.finset_sum (s := v.support) (fun p _ => hp p)
  convert h using 1
  funext z
  simp only [triangularGridInterpolant, Finset.sum_apply]

theorem triangularGridInterpolant_nodal (v : (ℤ × ℤ) →₀ ℝ) (p : ℤ × ℤ) :
    triangularGridInterpolant v (complexLatticePoint p) = v p := by
  classical
  unfold triangularGridInterpolant
  simp_rw [triangularGridHat_lattice_difference]
  by_cases hp : p ∈ v.support
  · simp [mul_ite, hp]
  · have hz : v p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [mul_ite, hp, hz]

end RepulsiveCoulomb
