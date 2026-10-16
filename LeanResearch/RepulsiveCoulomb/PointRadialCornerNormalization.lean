module

public import LeanResearch.RepulsiveCoulomb.PointRadialSectorNormalization
public import LeanResearch.RepulsiveCoulomb.JordanConformalTurnTransport

@[expose] public section

/-! Normalize arbitrary actual incident radial velocities, retaining their
positive rates and the full directed sector angle. No equal-speed assumption
is imposed on two macro-arcs. The principal Euclidean corner is π−θ even for
reflex θ; the physical cone correction can therefore retain the full θ. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Actual distinct rays, at any two positive speeds, admit one unit rotation
with outgoing angle zero and incoming outward angle strictly between 0 and 2π. -/
theorem exists_unequal_speed_radial_corner_normalization {u v : ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hdistinct : ¬ ∃ b : ℝ, 0 < b ∧ v = b • u) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧
      c * u = pointRadialSectorPoint ‖u‖ 0 ∧ c * v = pointRadialSectorPoint ‖v‖ θ := by
  let c := conePhase (-Complex.arg u)
  have hcn : ‖c‖ = 1 := conePhase_norm _
  have hc : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hcn]; norm_num)
  have hcu : c * u = (‖u‖ : ℂ) := conePhase_neg_arg_mul u
  obtain ⟨θ, hθ, hpolar⟩ := exists_pointRadialSectorPoint_angle (c * v) (mul_ne_zero hc hv)
  have hncv : ‖c * v‖ = ‖v‖ := by rw [norm_mul, hcn, one_mul]
  rw [hncv] at hpolar
  have hθne : θ ≠ 0 := by
    intro hθzero
    have hcv : c * v = (‖v‖ : ℂ) := by
      simpa only [hθzero, pointRadialSectorPoint_angle_zero] using hpolar.symm
    apply hdistinct
    refine ⟨‖v‖ / ‖u‖, div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hu), ?_⟩
    apply mul_left_cancel₀ hc
    rw [hcv, Complex.real_smul, mul_left_comm c, hcu, Complex.ofReal_div]
    exact (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu))).symm
  exact ⟨c, hcn, θ, lt_of_le_of_ne hθ.1 (Ne.symm hθne), hθ.2,
    by simpa only [pointRadialSectorPoint_angle_zero] using hcu, hpolar.symm⟩

/-- Normalize the chart itself and keep both literal radial paths with their
actual positive rates. This is the input expected by boundary-atom winding. -/
theorem exists_normalized_holomorphic_radial_corner {W : Set ℂ}
    (hW : IsOpen W) (hW0 : (0 : ℂ) ∈ W) {H : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H W) (hD : deriv H 0 ≠ 0) (hHinj : InjOn H W)
    {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hdistinct : ¬ ∃ b : ℝ, 0 < b ∧ v = b • u) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧
      ∃ Wn : Set ℂ, IsOpen Wn ∧ (0 : ℂ) ∈ Wn ∧ Wn = (fun z : ℂ => c⁻¹ * z) ⁻¹' W ∧
      ∃ Hn : ℂ → ℂ, AnalyticOnNhd ℂ Hn Wn ∧ deriv Hn 0 ≠ 0 ∧ InjOn Hn Wn ∧
        Hn 0 = H 0 ∧ (∀ z, Hn z = H (c⁻¹ * z)) ∧
        (∀ t : ℝ, H (t • u) = Hn (pointRadialSectorPoint (‖u‖ * t) 0)) ∧
        (∀ t : ℝ, H (t • v) = Hn (pointRadialSectorPoint (‖v‖ * t) θ)) := by
  obtain ⟨c, hcn, θ, hθ0, hθ2, hcu, hcv⟩ :=
    exists_unequal_speed_radial_corner_normalization hu hv hdistinct
  have hc : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hcn]; norm_num)
  let Wn := (fun z : ℂ => c⁻¹ * z) ⁻¹' W
  let Hn : ℂ → ℂ := fun z => H (c⁻¹ * z)
  have hWn : IsOpen Wn := hW.preimage (continuous_const.mul continuous_id)
  have hWn0 : (0 : ℂ) ∈ Wn := by simpa only [Wn, mem_preimage, mul_zero] using hW0
  have hHn : AnalyticOnNhd ℂ Hn Wn := by
    intro z hz
    exact (hH _ hz).comp (analyticAt_const.mul analyticAt_id)
  have hD0 : HasDerivAt H (deriv H 0) (c⁻¹ * (0 : ℂ)) := by
    simpa only [mul_zero] using (hH 0 hW0).differentiableAt.hasDerivAt
  have hDn : deriv Hn 0 = deriv H 0 * c⁻¹ := by
    simpa only [Hn, Function.comp_def, mul_one] using
      (hD0.comp 0 ((hasDerivAt_id (0 : ℂ)).const_mul c⁻¹)).deriv
  refine ⟨c, hcn, θ, hθ0, hθ2, Wn, hWn, hWn0, rfl, Hn, hHn, ?_, ?_, ?_,
    (fun _ => rfl), ?_, ?_⟩
  · rw [hDn]
    exact mul_ne_zero hD (inv_ne_zero hc)
  · intro z hz w hw heq
    exact mul_left_cancel₀ (inv_ne_zero hc) (hHinj hz hw heq)
  · simp only [Hn, mul_zero]
  · intro t
    have hpoint : pointRadialSectorPoint (‖u‖ * t) 0 = c * (t • u) := by
      rw [pointRadialSectorPoint_angle_zero, Complex.real_smul, mul_left_comm c, hcu,
        pointRadialSectorPoint_angle_zero, Complex.ofReal_mul]
      ring
    rw [hpoint]
    dsimp [Hn]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  · intro t
    have hpoint : pointRadialSectorPoint (‖v‖ * t) θ = c * (t • v) := by
      rw [Complex.real_smul, mul_left_comm c, hcv]
      simp only [pointRadialSectorPoint, Complex.ofReal_mul]
      ring
    rw [hpoint]
    dsimp [Hn]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- The normalized outgoing/incoming tangent ratio records π−θ in its actual
principal branch. This uses the whole reflex angle, never its short complement. -/
theorem normalized_radial_corner_principal_turn {θ cL cR : ℝ}
    (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi) (hcL : 0 < cL) (hcR : 0 < cR) :
    Complex.arg ((cL : ℂ) / (-((cR : ℂ) * (Circle.exp θ : ℂ)))) = Real.pi - θ := by
  have hphase : (Circle.exp (Real.pi - θ) : ℂ) = -(Circle.exp θ : ℂ)⁻¹ := by
    simp only [Circle.coe_exp]
    have he : ((Real.pi - θ : ℝ) : ℂ) * Complex.I =
        (Real.pi : ℂ) * Complex.I - (θ : ℂ) * Complex.I := by push_cast; ring
    rw [he, Complex.exp_sub, Complex.exp_pi_mul_I]
    simp only [div_eq_mul_inv, neg_one_mul]
  have hratio : (cL : ℂ) / (-((cR : ℂ) * (Circle.exp θ : ℂ))) =
      ((cL / cR : ℝ) : ℂ) * (Circle.exp (Real.pi - θ) : ℂ) := by
    rw [hphase, Complex.ofReal_div]
    field_simp [Complex.ofReal_ne_zero.mpr hcR.ne', Circle.coe_ne_zero] <;> ring
  rw [hratio, Complex.arg_real_mul _ (div_pos hcL hcR)]
  exact Circle.arg_exp (by linarith) (by linarith)

/-- Multiplication by the common holomorphic chart derivative cancels in
this actual corner turn. The same formula is valid at a cone point. -/
theorem holomorphic_radial_corner_principal_turn {D : ℂ} (hD : D ≠ 0)
    {θ cL cR : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (hcL : 0 < cL) (hcR : 0 < cR) :
    Complex.arg ((D * (cL : ℂ)) / (-(D * ((cR : ℂ) * (Circle.exp θ : ℂ))))) =
      Real.pi - θ := by
  rw [show -(D * ((cR : ℂ) * (Circle.exp θ : ℂ))) =
      D * (-((cR : ℂ) * (Circle.exp θ : ℂ))) by ring,
    conformal_corner_principal_turn D _ _ hD]
  exact normalized_radial_corner_principal_turn hθ0 hθ2 hcL hcR

end RepulsiveCoulomb
