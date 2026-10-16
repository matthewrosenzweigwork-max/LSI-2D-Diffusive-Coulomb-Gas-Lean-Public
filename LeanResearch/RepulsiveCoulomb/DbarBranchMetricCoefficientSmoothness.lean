module

public import LeanResearch.RepulsiveCoulomb.DbarBranchMetricMatrixMeasurability
public import LeanResearch.RepulsiveCoulomb.DbarBranchGraphKahler
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! The literal square-root and inverse-root matrix coefficients are real
C-infinity on the collision complement. The conjugated Hilbert representer
is used throughout, not the un-conjugated holomorphic covector coefficients. -/
noncomputable section
open Set InnerProductSpace
open scoped ComplexConjugate
namespace RepulsiveCoulomb

theorem dbarGraphMetricRootScalar_contDiff (N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (dbarGraphMetricRootScalar (N := N)) :=
  (contDiff_const.add (contDiff_norm_sq ℂ)).sqrt (fun a => by positivity)

theorem dbarRootMatrix_entry {N : ℕ} (a : CoulombConfig N) (i j : Fin N) :
    dbarCLMMatrix (dbarGraphMetricRoot a) i j = (1 : Matrix (Fin N) (Fin N) ℂ) i j +
      (((1 + dbarGraphMetricRootScalar a)⁻¹ : ℝ) : ℂ) * (a i * conj (a j)) := by
  unfold dbarGraphMetricRoot
  rw [dbarCLMMatrix, dbarRankOnePerturbation_apply]
  simp [EuclideanSpace.single, EuclideanSpace.inner_single_right, Matrix.one_apply, eq_comm] <;> ring

theorem dbarRootMatrix_entry_contDiff {N : ℕ} (i j : Fin N) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a : CoulombConfig N => dbarCLMMatrix (dbarGraphMetricRoot a) i j) := by
  have ht := dbarGraphMetricRootScalar_contDiff N
  have hd : ∀ a : CoulombConfig N, 1 + dbarGraphMetricRootScalar a ≠ 0 := fun a =>
    ne_of_gt (by have hp := dbarGraphMetricRootScalar_pos a; linarith)
  have hc := Complex.ofRealCLM.contDiff.comp ((contDiff_const.add ht).inv hd)
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun a : CoulombConfig N => a i) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ |>.contDiff
  have hj : ContDiff ℝ (⊤ : ℕ∞) (fun a : CoulombConfig N => a j) :=
    (EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ |>.contDiff
  have he := funext (fun a : CoulombConfig N => dbarRootMatrix_entry a i j)
  rw [he]
  exact contDiff_const.add (hc.mul (hi.mul (Complex.conjCLE.contDiff.comp hj)))

theorem dbarInverseRootMatrix_entry_contDiff {N : ℕ} (i j : Fin N) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a : CoulombConfig N => dbarCLMMatrix (dbarGraphMetricInverseRoot a) i j) := by
  have ht := dbarGraphMetricRootScalar_contDiff N
  have hd : ∀ a : CoulombConfig N,
      dbarGraphMetricRootScalar a * (1 + dbarGraphMetricRootScalar a) ≠ 0 := fun a =>
    mul_ne_zero (dbarGraphMetricRootScalar_pos a).ne'
      (ne_of_gt (by have hp := dbarGraphMetricRootScalar_pos a; linarith))
  have hc := Complex.ofRealCLM.contDiff.comp ((ht.mul (contDiff_const.add ht)).inv hd)
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun a : CoulombConfig N => a i) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ |>.contDiff
  have hj : ContDiff ℝ (⊤ : ℕ∞) (fun a : CoulombConfig N => a j) :=
    (EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ |>.contDiff
  have he := funext (fun a : CoulombConfig N => dbarInverseRootMatrix_entry a i j)
  rw [he]
  exact contDiff_const.sub (hc.mul (hi.mul (Complex.conjCLE.contDiff.comp hj)))

theorem coulombReciprocalRiesz_contDiffAt {N : ℕ} {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => dbarCovectorRiesz (coulombReciprocalDerivative w)) z := by
  apply (contDiffAt_piLp 2).mpr
  intro i
  have he : (fun w => dbarCovectorRiesz (coulombReciprocalDerivative w) i) =
      fun w => conj (coulombReciprocalCoefficient i w) :=
    funext (fun w => dbarCovectorRiesz_coordinate (coulombReciprocalDerivative w) i)
  rw [he]
  exact Complex.conjCLE.contDiff.contDiffAt.comp z
    ((coulombReciprocalCoefficient_contDiffAt i hz).restrict_scalars ℝ)

def coulombRootMatrix {N : ℕ} (z : CoulombConfig N) : Matrix (Fin N) (Fin N) ℂ :=
  dbarCLMMatrix (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)))

theorem coulombRootMatrix_entry_contDiffAt {N : ℕ} (i j : Fin N)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w => coulombRootMatrix w i j) z :=
  (dbarRootMatrix_entry_contDiff i j).contDiffAt.comp z (coulombReciprocalRiesz_contDiffAt hz)

theorem coulombInverseRootMatrix_entry_contDiffAt {N : ℕ} (i j : Fin N)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w => coulombInverseRootMatrix w i j) z :=
  (dbarInverseRootMatrix_entry_contDiff i j).contDiffAt.comp z (coulombReciprocalRiesz_contDiffAt hz)

end RepulsiveCoulomb
