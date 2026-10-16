module

public import LeanResearch.RepulsiveCoulomb.DbarBranchWeightedCoreAdjoint

@[expose] public section

/-! Expand the normalized compact adjoint into -partial + partial(Potential),
using the checked actual normalized-density derivative. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
namespace RepulsiveCoulomb

theorem coulombDensity_complex_fderiv_apply {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) (v : CoulombConfig N) :
    fderiv ℝ (fun x => (coulombDensity N β x : ℂ)) z v =
      -(coulombDensity N β z : ℂ) * fderiv ℝ (fun x => (coulombPotential β x : ℂ)) z v := by
  have hU := (coulombPotential_contDiffAt β hz).differentiableAt (by simp)
  have hρ := Complex.ofRealCLM.hasFDerivAt.comp z (coulombDensity_hasFDerivAt β hz)
  have hp := Complex.ofRealCLM.hasFDerivAt.comp z hU.hasFDerivAt
  have hρ' := hρ.fderiv
  have hp' := hp.fderiv
  change fderiv ℝ (fun x => (coulombDensity N β x : ℂ)) z = _ at hρ'
  change fderiv ℝ (fun x => (coulombPotential β x : ℂ)) z = _ at hp'
  rw [hρ', hp']
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply,
    innerSL_apply_apply, inner_neg_left, inner_gradient_left, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

theorem coulombDensity_DCoordinate {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) (i : Fin N) :
    coulombDCoordinate (fun x => (coulombDensity N β x : ℂ)) z i =
      -(coulombDensity N β z : ℂ) * coulombDCoordinate (fun x => (coulombPotential β x : ℂ)) z i := by
  unfold coulombDCoordinate
  rw [coulombDensity_complex_fderiv_apply β hz, coulombDensity_complex_fderiv_apply β hz]
  ring

theorem coulombWeightedCoreAdjointCoordinate_expanded {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) (i : Fin N) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    coulombWeightedCoreAdjointCoordinate hβ i φ z = -coulombDCoordinate φ z i +
      coulombDCoordinate (fun x => (coulombPotential β x : ℂ)) z i * φ z := by
  have hd : DifferentiableAt ℝ (fun x => (coulombDensity N β x : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z (coulombDensity_hasFDerivAt β hz).differentiableAt
  have hρ : (coulombDensity N β z : ℂ) ≠ 0 := by
    exact_mod_cast (coulombDensity_pos_off_collisions hβ hz).ne'
  rw [coulombWeightedCoreAdjointCoordinate_apply,
    coulombDCoordinate_mul hd (φ.contDiff.differentiable (by simp) z), coulombDensity_DCoordinate β hz]
  field_simp [hρ]
  ring

end RepulsiveCoulomb
