module

public import LeanResearch.RepulsiveCoulomb.CoulombWirtinger
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

/-! Literal holomorphic-coordinate derivatives and elementary conjugation and
product identities, with the same one-half convention as the checked dbar. -/
noncomputable section
open InnerProductSpace Filter
open scoped ComplexConjugate Topology
namespace RepulsiveCoulomb

def coulombDCoordinate {N : ℕ} (f : CoulombConfig N → ℂ) (z : CoulombConfig N) (i : Fin N) : ℂ :=
  (fderiv ℝ f z (coulombCoordinateInjection N i 1) -
    Complex.I * fderiv ℝ f z (coulombCoordinateInjection N i Complex.I)) / 2

theorem coulomb_fderiv_conj_apply {N : ℕ} {f : CoulombConfig N → ℂ} {z : CoulombConfig N}
    (hf : DifferentiableAt ℝ f z) (v : CoulombConfig N) :
    fderiv ℝ (fun x => conj (f x)) z v = conj (fderiv ℝ f z v) := by
  have hd := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z hf.hasFDerivAt
  have hfd := hd.fderiv
  change fderiv ℝ (fun x => conj (f x)) z = _ at hfd
  rw [hfd]
  rfl

theorem coulombDbarCoordinate_conj {N : ℕ} {f : CoulombConfig N → ℂ} {z : CoulombConfig N}
    (hf : DifferentiableAt ℝ f z) (i : Fin N) :
    coulombDbarCoordinate (fun x => conj (f x)) z i = conj (coulombDCoordinate f z i) := by
  rw [coulombDbarCoordinate, coulombDCoordinate,
    coulomb_fderiv_conj_apply hf, coulomb_fderiv_conj_apply hf]
  simp only [map_div₀, map_sub, map_mul, Complex.conj_I, map_ofNat]
  ring

theorem coulombDCoordinate_conj {N : ℕ} {f : CoulombConfig N → ℂ} {z : CoulombConfig N}
    (hf : DifferentiableAt ℝ f z) (i : Fin N) :
    coulombDCoordinate (fun x => conj (f x)) z i = conj (coulombDbarCoordinate f z i) := by
  rw [coulombDCoordinate, coulombDbarCoordinate,
    coulomb_fderiv_conj_apply hf, coulomb_fderiv_conj_apply hf]
  simp only [map_div₀, map_add, map_mul, Complex.conj_I, map_ofNat]
  ring

theorem coulombDbarCoordinate_mul {N : ℕ} {f g : CoulombConfig N → ℂ} {z : CoulombConfig N}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : Fin N) :
    coulombDbarCoordinate (fun x => f x * g x) z i =
      f z * coulombDbarCoordinate g z i + g z * coulombDbarCoordinate f z i := by
  rw [coulombDbarCoordinate, fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    coulombDbarCoordinate]
  ring

theorem coulombDCoordinate_mul {N : ℕ} {f g : CoulombConfig N → ℂ} {z : CoulombConfig N}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : Fin N) :
    coulombDCoordinate (fun x => f x * g x) z i =
      f z * coulombDCoordinate g z i + g z * coulombDCoordinate f z i := by
  rw [coulombDCoordinate, fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    coulombDCoordinate]
  ring

theorem coulombDCoordinate_of_complex_differentiable {N : ℕ}
    {f : CoulombConfig N → ℂ} {z : CoulombConfig N} (hf : DifferentiableAt ℂ f z) (i : Fin N) :
    coulombDCoordinate f z i = fderiv ℂ f z (coulombCoordinateInjection N i 1) := by
  rw [coulombDCoordinate, hf.fderiv_restrictScalars ℝ]
  have he : coulombCoordinateInjection N i Complex.I =
      Complex.I • coulombCoordinateInjection N i 1 := by
    simpa using coulombCoordinateInjection_complex_smul i Complex.I 1
  simp only [ContinuousLinearMap.coe_restrictScalars', he, map_smul, smul_eq_mul]
  rw [← mul_assoc, Complex.I_mul_I]
  ring

theorem coulombDCoordinate_real {N : ℕ} {f : CoulombConfig N → ℝ} {z : CoulombConfig N}
    (hf : DifferentiableAt ℝ f z) (i : Fin N) :
    coulombDCoordinate (fun x => (f x : ℂ)) z i = conj (gradient f z i) / 2 := by
  have hc : DifferentiableAt ℝ (fun x => (f x : ℂ)) z := Complex.ofRealCLM.differentiableAt.comp z hf
  have h := coulombDCoordinate_conj hc i
  have he : (fun x => conj (f x : ℂ)) = fun x => (f x : ℂ) := by funext x; simp
  rw [he, coulombDbarCoordinate_real hf] at h
  simpa only [map_div₀, map_ofNat] using h


theorem coulombDbarCoordinate_const_add {N : ℕ} (c : ℂ) (f : CoulombConfig N → ℂ)
    (z : CoulombConfig N) (i : Fin N) :
    coulombDbarCoordinate (fun x => c + f x) z i = coulombDbarCoordinate f z i := by
  simp only [coulombDbarCoordinate, fderiv_const_add]


theorem coulombDbarCoordinate_add {N : ℕ} {f g : CoulombConfig N → ℂ} {z : CoulombConfig N}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : Fin N) :
    coulombDbarCoordinate (fun x => f x + g x) z i =
      coulombDbarCoordinate f z i + coulombDbarCoordinate g z i := by
  rw [coulombDbarCoordinate, fderiv_fun_add hf hg]
  simp only [ContinuousLinearMap.add_apply, coulombDbarCoordinate]
  ring

theorem coulombDbarCoordinate_neg {N : ℕ} (f : CoulombConfig N → ℂ) (z : CoulombConfig N) (i : Fin N) :
    coulombDbarCoordinate (fun x => -f x) z i = -coulombDbarCoordinate f z i := by
  simp only [coulombDbarCoordinate, fderiv_fun_neg, ContinuousLinearMap.neg_apply]
  ring

theorem coulombDbarCoordinate_congr_of_eventuallyEq {N : ℕ} {f g : CoulombConfig N → ℂ}
    {z : CoulombConfig N} (he : f =ᶠ[𝓝 z] g) (i : Fin N) :
    coulombDbarCoordinate f z i = coulombDbarCoordinate g z i := by
  unfold coulombDbarCoordinate
  rw [he.fderiv_eq]

end RepulsiveCoulomb
