import LeanResearch.RepulsiveCoulomb.CoulombCenterGradient
import LeanResearch.RepulsiveCoulomb.PoleBranchOptimalLSIRate

/-! Transport of every element of the original closed physical form domain.
This module does not silently replace that domain by smooth tests, a surrogate
energy, or a postulated product Sobolev space. The two pulled-back gradient
components are the actual L² weak gradient of each original domain element. -/
noncomputable section
open Set MeasureTheory
open PeriodicAttractiveLogGas
open scoped Topology ENNReal
namespace RepulsiveCoulomb

variable {n : ℕ}

def coulombCenterFormValue (e : CoulombCenterRotation n) {β : ℝ}
    (hβ : 0 < β) (u : CoulombFormDomain (n + 1) hβ)
    (p : ℂ × CoulombConfig n) : ℝ :=
  coulombFormValueL (n + 1) hβ u (coulombCenterInsert e p.1 p.2)

def coulombCenterFormCenterGradient (e : CoulombCenterRotation n) {β : ℝ}
    (hβ : 0 < β) (u : CoulombFormDomain (n + 1) hβ)
    (p : ℂ × CoulombConfig n) : ℂ :=
  e (coulombFormGradientL (n + 1) hβ u (coulombCenterInsert e p.1 p.2)) 0

def coulombCenterFormRelativeGradient (e : CoulombCenterRotation n) {β : ℝ}
    (hβ : 0 < β) (u : CoulombFormDomain (n + 1) hβ)
    (p : ℂ × CoulombConfig n) : CoulombConfig n :=
  coulombTail (e (coulombFormGradientL (n + 1) hβ u (coulombCenterInsert e p.1 p.2)))

/-- Exact entropy of arbitrary full-domain elements, including infinite values. -/
theorem coulombCenterForm_entropy (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain (n + 1) hβ) :
    entropy (coulombMeasure (n + 1) β)
        (fun z => (coulombFormValueL (n + 1) hβ u z) ^ 2) =
      entropy ((coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β))
        (fun p => coulombCenterFormValue e hβ u p ^ 2) := by
  have h := coulombCenter_entropy_transport e he hβ
    (fun p => coulombCenterFormValue e hβ u p ^ 2)
  have hv : (fun z => coulombCenterFormValue e hβ u (coulombCenterChart e z) ^ 2) =
      (fun z => (coulombFormValueL (n + 1) hβ u z) ^ 2) := by
    funext z
    unfold coulombCenterFormValue
    rw [← coulombCenterChart_symm_apply, MeasurableEquiv.symm_apply_apply]
  rw [hv] at h
  exact h

/-- Exact sum of physical energies for every original closed-domain element. -/
theorem coulombCenterForm_energy (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain (n + 1) hβ) :
    coulombFormEnergy (n + 1) hβ u =
      ∫ p, (‖coulombCenterFormCenterGradient e hβ u p‖ ^ 2 +
        ‖coulombCenterFormRelativeGradient e hβ u p‖ ^ 2)
        ∂(coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β) := by
  rw [coulombFormEnergy_eq_integral]
  have h := (coulombCenter_gibbsMeasurePreserving e he hβ).symm.integral_comp'
    (fun z => ‖coulombFormGradientL (n + 1) hβ u z‖ ^ 2)
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [coulombCenterChart_symm_apply]
  let g := e (coulombFormGradientL (n + 1) hβ u (coulombCenterInsert e p.1 p.2))
  have hn := coulombInsertZero_norm_sq (g 0) (coulombTail g)
  rw [coulombInsertZero_head_tail] at hn
  change ‖coulombFormGradientL (n + 1) hβ u (coulombCenterInsert e p.1 p.2)‖ ^ 2 =
    ‖g 0‖ ^ 2 + ‖coulombTail g‖ ^ 2
  rw [← hn]
  exact congrArg (fun x : ℝ => x ^ 2) (e.norm_map _).symm

/-- Full-domain LSI is equivalent to its literal center-coordinate expression.
No tensorization premise or claim is hidden in this transport equivalence. -/
theorem coulombCenterForm_lsi_iff (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β ρ : ℝ} (hβ : 0 < β) :
    poleBranchAdmissibleLSIRate (n + 1) hβ ρ ↔
      0 < ρ ∧ ∀ u : CoulombFormDomain (n + 1) hβ,
        entropy ((coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β))
          (fun p => coulombCenterFormValue e hβ u p ^ 2) ≤
          (((2 / ρ) * ∫ p, (‖coulombCenterFormCenterGradient e hβ u p‖ ^ 2 +
            ‖coulombCenterFormRelativeGradient e hβ u p‖ ^ 2)
            ∂(coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β) : ℝ) : EReal) := by
  unfold poleBranchAdmissibleLSIRate
  simp_rw [coulombCenterForm_entropy e he hβ, coulombCenterForm_energy e he hβ]

end RepulsiveCoulomb
