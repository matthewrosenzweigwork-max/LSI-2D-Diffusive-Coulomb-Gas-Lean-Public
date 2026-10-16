module

public import LeanResearch.RepulsiveCoulomb.PointConformalFlatPrimitive
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-! The literal logarithmic connection underlying conformal turn. The real
differential of the actual density logarithm is proved, then the derivative of
any actual local holomorphic phase potential with that real part is identified.
No global flux or winding identity is assumed. -/
noncomputable section
open Set Metric Filter InnerProductSpace
open scoped Topology ComplexConjugate BigOperators
namespace RepulsiveCoulomb

def pointConformalConnection {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) : ℂ :=
  conj ((1 / 2 : ℝ) • pointLogForce a y z)

theorem conj_pointLogForceKernel (z : ℂ) :
    conj ((‖z‖ ^ 2)⁻¹ • z) = z⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, Complex.real_smul,
    map_mul, Complex.conj_ofReal]
  ring

theorem pointConformalConnection_eq_reciprocal_sum {m : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) :
    pointConformalConnection a y z = ∑ j, ((a j / 2 : ℝ) : ℂ) / (z - y j) := by
  have hforce : conj (pointLogForce a y z) = ∑ j, (a j : ℂ) / (z - y j) := by
    unfold pointLogForce
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Complex.real_smul, map_mul, Complex.conj_ofReal, conj_pointLogForceKernel,
      div_eq_mul_inv]
  rw [pointConformalConnection, Complex.real_smul, map_mul, Complex.conj_ofReal,
    hforce, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

theorem hasFDerivAt_pointConformalLog {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ} (hz : z ∉ pointPunctures a y) :
    HasFDerivAt (pointConformalLog a y)
      (innerSL ℝ ((1 / 2 : ℝ) • pointLogForce a y z)) z := by
  have h := (hasFDerivAt_pointLogWeight (0 : ℝ) ha y hz).const_mul (1 / 2 : ℝ)
  have heq : (fun x : ℂ => (1 / 2 : ℝ) * pointLogWeight 0 a y x) = pointConformalLog a y := by
    funext x
    simp [pointLogWeight, pointConformalLog]
  rw [heq] at h
  apply h.congr_fderiv
  ext v
  simp [pointScore, innerSL_apply_apply, inner_smul_left, smul_eq_mul]
  ring

theorem fderiv_pointConformalLog_one {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ} (hz : z ∉ pointPunctures a y) :
    fderiv ℝ (pointConformalLog a y) z 1 = (1 / 2 : ℝ) * (pointLogForce a y z).re := by
  rw [(hasFDerivAt_pointConformalLog ha y hz).fderiv]
  simp [innerSL_apply_apply, inner_smul_left, Complex.inner, smul_eq_mul]

theorem fderiv_pointConformalLog_I {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ} (hz : z ∉ pointPunctures a y) :
    fderiv ℝ (pointConformalLog a y) z Complex.I = (1 / 2 : ℝ) * (pointLogForce a y z).im := by
  rw [(hasFDerivAt_pointConformalLog ha y hz).fderiv]
  simp [innerSL_apply_apply, inner_smul_left, Complex.inner, Complex.mul_re, smul_eq_mul]

/-- Holomorphicity and the literal real part determine the connection; there
is no free phase-derivative certificate. -/
theorem deriv_eq_pointConformalConnection {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ} (hz : z ∉ pointPunctures a y)
    {H : ℂ → ℂ} (hH : DifferentiableAt ℂ H z)
    (hre : (fun w => (H w).re) =ᶠ[𝓝 z] pointConformalLog a y) :
    deriv H z = pointConformalConnection a y z := by
  have hfd : fderiv ℝ (fun w => (H w).re) z = fderiv ℝ (pointConformalLog a y) z := hre.fderiv_eq
  have hcomp : fderiv ℝ (fun w => (H w).re) z =
      Complex.reCLM.comp ((fderiv ℂ H z).restrictScalars ℝ) := by
    have h := (Complex.reCLM.hasFDerivAt.comp z (hH.restrictScalars ℝ).hasFDerivAt).fderiv
    rw [hH.fderiv_restrictScalars ℝ] at h
    exact h
  have hv (v : ℂ) : (v * deriv H z).re = fderiv ℝ (pointConformalLog a y) z v := by
    have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) hfd
    rw [hcomp] at h
    change ((fderiv ℂ H z) v).re = _ at h
    rw [fderiv_eq_smul_deriv] at h
    exact h
  have h1 := hv 1
  have hI := hv Complex.I
  rw [fderiv_pointConformalLog_one ha y hz] at h1
  rw [fderiv_pointConformalLog_I ha y hz] at hI
  simp only [one_mul] at h1
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at hI
  apply Complex.ext
  · simpa [pointConformalConnection, Complex.real_smul] using h1
  · simp only [pointConformalConnection, Complex.conj_im, Complex.smul_im, smul_eq_mul]
    linarith

/-- The required holomorphic phase potential is constructed on an actual
puncture-free disk and has the proved literal connection derivative. -/
theorem exists_pointConformal_connection_potential {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ} (hp : p ∉ pointPunctures a y) :
    ∃ r : ℝ, 0 < r ∧ ball p r ⊆ (pointPunctures a y)ᶜ ∧
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball p r) ∧
        ∀ z ∈ ball p r, (H z).re = pointConformalLog a y z ∧
          deriv H z = pointConformalConnection a y z ∧
          ‖Complex.exp (H z)‖ = pointConformalDensity a y z := by
  obtain ⟨r, hr, hball⟩ := exists_pointDomain_ball a y hp
  have hh := (pointConformalLog_harmonicOnNhd ha y).mono hball
  obtain ⟨H, hH, hre⟩ := hh.exists_analyticOnNhd_ball_re_eq
  refine ⟨r, hr, hball, H, hH, ?_⟩
  intro z hz
  refine ⟨hre hz, ?_, ?_⟩
  · apply deriv_eq_pointConformalConnection ha y (hball hz) (hH z hz).differentiableAt
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hre hw
  · have hzre : (H z).re = pointConformalLog a y z := hre hz
    rw [Complex.norm_exp, hzre, exp_pointConformalLog ha y (hball hz)]

end RepulsiveCoulomb
