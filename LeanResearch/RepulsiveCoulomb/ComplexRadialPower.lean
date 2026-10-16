module

public import LeanResearch.RepulsiveCoulomb.PointConeCosineFormula

@[expose] public section

/-! Explicit radial-coordinate equivalences for the classical cone model. -/
noncomputable section
open Filter
open scoped Topology
namespace RepulsiveCoulomb

def complexRadialPower (p : ℝ) (z : ℂ) : ℂ := ‖z‖ ^ (p - 1) • z

theorem complexRadialPower_zero (p : ℝ) : complexRadialPower p 0 = 0 := by
  simp [complexRadialPower]

theorem complexRadialPower_one (z : ℂ) : complexRadialPower 1 z = z := by
  simp [complexRadialPower]

theorem complexRadialPower_norm {p : ℝ} (hp : 0 < p) (z : ℂ) :
    ‖complexRadialPower p z‖ = ‖z‖ ^ p := by
  by_cases hz : z = 0
  · subst z
    simp [complexRadialPower, Real.zero_rpow hp.ne']
  · rw [complexRadialPower, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      ← Real.rpow_add_one (norm_ne_zero_iff.mpr hz)]
    congr 1
    ring

theorem complexRadialPower_comp {p q : ℝ} (hp : 0 < p) (z : ℂ) :
    complexRadialPower q (complexRadialPower p z) = complexRadialPower (p * q) z := by
  by_cases hz : z = 0
  · subst z
    simp only [complexRadialPower_zero]
  · change ‖complexRadialPower p z‖ ^ (q - 1) • complexRadialPower p z = _
    rw [complexRadialPower_norm hp]
    unfold complexRadialPower
    rw [smul_smul, ← Real.rpow_mul (norm_nonneg z), ← Real.rpow_add (norm_pos_iff.mpr hz)]
    congr 2
    ring

theorem complexRadialPower_arg (p : ℝ) (z : ℂ) :
    Complex.arg (complexRadialPower p z) = Complex.arg z := by
  by_cases hz : z = 0
  · subst z
    rw [complexRadialPower_zero]
  · rw [complexRadialPower, Complex.real_smul,
      Complex.arg_real_mul z (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _)]

def complexRadialPowerEquiv (p : ℝ) (hp : 0 < p) : ℂ ≃ ℂ where
  toFun := complexRadialPower p
  invFun := complexRadialPower p⁻¹
  left_inv z := by rw [complexRadialPower_comp hp, mul_inv_cancel₀ hp.ne', complexRadialPower_one]
  right_inv z := by rw [complexRadialPower_comp (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne', complexRadialPower_one]

def coneRadialEquiv (α : ℝ) (hα : 0 ≤ α) : ℂ ≃ ℂ where
  toFun z := (α + 1)⁻¹ • complexRadialPower (α + 1) z
  invFun w := complexRadialPower (α + 1)⁻¹ ((α + 1) • w)
  left_inv z := by
    dsimp only
    have hn : α + 1 ≠ 0 := by linarith
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul, complexRadialPower_comp (by linarith),
      mul_inv_cancel₀ hn, complexRadialPower_one]
  right_inv w := by
    dsimp only
    have hn : α + 1 ≠ 0 := by linarith
    rw [complexRadialPower_comp (inv_pos.mpr (by linarith)), inv_mul_cancel₀ hn,
      complexRadialPower_one, smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem coneRadialEquiv_norm (α : ℝ) (hα : 0 ≤ α) (z : ℂ) :
    ‖coneRadialEquiv α hα z‖ = coneRadialPotential α z := by
  change ‖(α + 1)⁻¹ • complexRadialPower (α + 1) z‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith)),
    complexRadialPower_norm (by linarith)]
  rfl

theorem coneRadialEquiv_arg (α : ℝ) (hα : 0 ≤ α) (z : ℂ) :
    Complex.arg (coneRadialEquiv α hα z) = Complex.arg z := by
  change Complex.arg ((α + 1)⁻¹ • complexRadialPower (α + 1) z) = _
  rw [Complex.real_smul, Complex.arg_real_mul _ (inv_pos.mpr (by linarith)), complexRadialPower_arg]

theorem complexRadialPower_continuous {p : ℝ} (hp : 0 < p) : Continuous (complexRadialPower p) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    rw [ContinuousAt, complexRadialPower_zero, tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [complexRadialPower_norm hp]
    have hc : ContinuousAt (fun w : ℂ ↦ ‖w‖ ^ p) 0 := continuousAt_id.norm.rpow_const (Or.inr hp.le)
    simpa [ContinuousAt, Real.zero_rpow hp.ne'] using hc
  · exact (continuousAt_id.norm.rpow_const (Or.inl (norm_ne_zero_iff.mpr hz))).smul continuousAt_id

def coneRadialHomeomorph (α : ℝ) (hα : 0 ≤ α) : ℂ ≃ₜ ℂ where
  toEquiv := coneRadialEquiv α hα
  continuous_toFun := by
    change Continuous (fun z : ℂ ↦ (α + 1)⁻¹ • complexRadialPower (α + 1) z)
    convert (continuous_const : Continuous (fun _ : ℂ ↦ (α + 1)⁻¹)).smul
      (complexRadialPower_continuous (p := α + 1) (by linarith)) using 1
  continuous_invFun := by
    change Continuous (fun w : ℂ ↦ complexRadialPower (α + 1)⁻¹ ((α + 1) • w))
    have hc : Continuous (fun w : ℂ ↦ (α + 1) • w) := by
      convert (continuous_const : Continuous (fun _ : ℂ ↦ α + 1)).smul
        (continuous_id : Continuous (fun w : ℂ ↦ w)) using 1
      rfl
    exact (complexRadialPower_continuous (p := (α + 1)⁻¹) (inv_pos.mpr (by linarith))).comp hc

theorem coneRadialEquiv_zero (α : ℝ) (hα : 0 ≤ α) : coneRadialEquiv α hα 0 = 0 := by
  change (α + 1)⁻¹ • complexRadialPower (α + 1) 0 = 0
  rw [complexRadialPower_zero, smul_zero]

theorem coneRadialEquiv_ne_zero {α : ℝ} (hα : 0 ≤ α) {z : ℂ} (hz : z ≠ 0) :
    coneRadialEquiv α hα z ≠ 0 := by
  rw [← coneRadialEquiv_zero α hα]
  exact (coneRadialEquiv α hα).injective.ne hz

theorem coneRadialEquiv_arg_div (α : ℝ) (hα : 0 ≤ α) (x z : ℂ) :
    Complex.arg (coneRadialEquiv α hα z / coneRadialEquiv α hα x) = Complex.arg (z / x) := by
  by_cases hx : x = 0
  · subst x
    simp [coneRadialEquiv_zero]
  · by_cases hz : z = 0
    · subst z
      simp [coneRadialEquiv_zero]
    · apply Complex.arg_coe_angle_eq_iff.mp
      rw [Complex.arg_div_coe_angle (coneRadialEquiv_ne_zero hα hz) (coneRadialEquiv_ne_zero hα hx),
        Complex.arg_div_coe_angle hz hx, coneRadialEquiv_arg, coneRadialEquiv_arg]

end RepulsiveCoulomb
