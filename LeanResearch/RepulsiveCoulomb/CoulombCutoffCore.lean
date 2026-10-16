import LeanResearch.RepulsiveCoulomb.CoulombLocalCoreBound

/-! Genuine compact localization of core functions and physical gradients. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RepulsiveCoulomb

def coulombLocalizedCore {N : ℕ}
    (η : TestFunction (coulombDomain N) ℝ ⊤) (U : Opens (CoulombConfig N))
    (hηU : tsupport (η : CoulombConfig N → ℝ) ⊆ U)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) : TestFunction U ℝ ⊤ where
  toFun z := η z * φ z
  contDiff' := η.contDiff.mul φ.contDiff
  hasCompactSupport' := η.hasCompactSupport.mul_right (f' := (φ : CoulombConfig N → ℝ))
  tsupport_subset' := (tsupport_mul_subset_left (f := (η : CoulombConfig N → ℝ))
    (g := (φ : CoulombConfig N → ℝ))).trans hηU

theorem coulombLocalizedCore_apply {N : ℕ}
    (η : TestFunction (coulombDomain N) ℝ ⊤) (U : Opens (CoulombConfig N))
    (hηU : tsupport (η : CoulombConfig N → ℝ) ⊆ U)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (z : CoulombConfig N) :
    coulombLocalizedCore η U hηU φ z = η z * φ z := rfl

theorem coulomb_gradient_mul {N : ℕ} {f g : CoulombConfig N → ℝ} {z : CoulombConfig N}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    gradient (fun x => f x * g x) z = f z • gradient g z + g z • gradient f z := by
  apply (InnerProductSpace.toDual ℝ (CoulombConfig N)).injective
  simp only [toDual_gradient, map_add, map_smul]
  exact fderiv_fun_mul hf hg

theorem coulomb_gradient_mul_sq_le {N : ℕ} {f g : CoulombConfig N → ℝ} {z : CoulombConfig N}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    ‖gradient (fun x => f x * g x) z‖ ^ 2 ≤
      2 * (f z) ^ 2 * ‖gradient g z‖ ^ 2 + 2 * (g z) ^ 2 * ‖gradient f z‖ ^ 2 := by
  rw [coulomb_gradient_mul hf hg]
  have h := norm_add_le (f z • gradient g z) (g z • gradient f z)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hp := sq_nonneg (‖f z • gradient g z‖ - ‖g z • gradient f z‖)
  simp only [norm_smul, Real.norm_eq_abs] at hs hp
  have hfs := sq_abs (f z)
  have hgs := sq_abs (g z)
  nlinarith

theorem coulombLocalizedCore_gradient_zero_off {N : ℕ}
    (η : TestFunction (coulombDomain N) ℝ ⊤) (U : Opens (CoulombConfig N))
    (hηU : tsupport (η : CoulombConfig N → ℝ) ⊆ U)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) {z : CoulombConfig N}
    (hz : z ∉ tsupport (η : CoulombConfig N → ℝ)) :
    gradient (coulombLocalizedCore η U hηU φ : CoulombConfig N → ℝ) z = 0 := by
  apply TauCeti.gradient_of_notMem_tsupport
  exact fun h => hz (tsupport_mul_subset_left h)

end RepulsiveCoulomb
