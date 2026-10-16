import LeanResearch.RepulsiveCoulomb.CoulombFixedParticlePoincareAdapter
import LeanResearch.RepulsiveCoulomb.DbarBranchFormKernelConstants

/-! The actual fixed-particle Poincare gap on the original full form domain.
The separate zero-gradient theorem is proved by weak-kernel regularity and
connectedness, and is consumed here rather than left as an analytic premise. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
namespace RepulsiveCoulomb

theorem coulombForm_meanZero_zeroGradient_eq_zero {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ)
    (hm : poleBranchRealMean N hβ (coulombFormValueL N hβ u) = 0)
    (hg : coulombFormGradientL N hβ u = 0) : u = 0 := by
  letI := coulombMeasure_isProbability (N := N) hβ
  obtain ⟨a, ha⟩ := coulombForm_zero_gradient_constant hβ u hg
  have hmean : poleBranchRealMean N hβ (coulombFormValueL N hβ u) = a := by
    rw [poleBranchRealMean_eq_integral]
    calc
      _ = ∫ _z : CoulombConfig N, a ∂coulombMeasure N β := integral_congr_ae ha
      _ = a := by simp
  have ha0 : a = 0 := hmean.symm.trans hm
  have hv : coulombFormValueL N hβ u = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [ha] with z hz
    change coulombFormValueL N hβ u z = 0
    exact hz.trans ha0
  exact (coulombFormValueL_eq_zero_iff N hβ u).mp hv

theorem coulomb_fixed_particle_poincare (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : CoulombFormDomain (N + 2) hβ,
      variance (coulombFormValueL (N + 2) hβ u : CoulombConfig (N + 2) → ℝ)
        (coulombMeasure (N + 2) β) ≤ C * coulombFormEnergy (N + 2) hβ u :=
  coulombForm_poincare_of_meanZero_kernel N hβ
    (fun u hm hg => coulombForm_meanZero_zeroGradient_eq_zero hβ u hm hg)

end RepulsiveCoulomb
