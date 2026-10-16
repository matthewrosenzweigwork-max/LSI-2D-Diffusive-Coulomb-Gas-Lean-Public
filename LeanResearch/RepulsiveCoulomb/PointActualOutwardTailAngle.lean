import LeanResearch.RepulsiveCoulomb.PointActualOutwardTailSine
import LeanResearch.RepulsiveCoulomb.AffineAngularTailPotential
import Mathlib.Tactic

/-! Uncompiled additive successor. Actual uniform angular tail bound with
constructed lifts. Its only extra smallness condition is the explicit numerical
sine bound at the chosen starting radius; monotonicity propagates it outward. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_pointConformal_actual_outward_tail_angle_bound
    {n : ℕ} {a : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin n → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {A s u : ℝ} (hA : 0 < A) (hyA : ∀ j, 2 * ‖y j‖ ≤ A)
    (hB : 0 < pointExteriorHalfMass a)
    (hD : pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * A)
    (hs : 0 < s) (hsu : s < u) (hu : u < 1) (hstart : ‖γ s‖ = A)
    (hout : ∀ t ∈ Ioc s u, A < ‖γ t‖) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧
      (∀ t ∈ Icc s u, Complex.exp ((φ t : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ)) ∧
      ∀ t ∈ Icc s u,
        Real.rpow A (1 + pointExteriorHalfMass a) / Real.rpow ‖γ t‖ (1 + pointExteriorHalfMass a) +
          pointExteriorMoment a y / (pointExteriorHalfMass a * ‖γ t‖) ≤ 1 / 2 →
        |φ u - φ t| ≤ angularTailPotential A (pointExteriorHalfMass a)
          (pointExteriorMoment a y) ‖γ t‖ := by
  obtain ⟨θ, φ, hθ, hφ, hlift, hcos, hsin, hrD, hφD⟩ :=
    exists_pointConformal_actual_outward_tail_sine_bound ha y γ hc L hL hgeo
      hA hyA hB hD hs hsu hu hstart hout
  let B := pointExteriorHalfMass a
  let D := pointExteriorMoment a y
  let H : ℝ → ℝ := fun r => Real.rpow A (1 + B) / Real.rpow r (1 + B) + D / (B * r)
  have hDnonneg : 0 ≤ D := pointExteriorMoment_nonneg ha y
  have hp : 0 < 1 + B := by dsimp [B]; linarith
  have hz (t : ℝ) (ht : t ∈ Icc s u) : 0 < ‖γ t‖ := by
    by_cases heq : t = s
    · subst t; rwa [hstart]
    · exact hA.trans (hout t ⟨lt_of_le_of_ne ht.1 (Ne.symm heq), ht.2⟩)
  have hv (t : ℝ) (ht : t ∈ Ioo s u) : 0 < ‖deriv γ t‖ := by
    apply norm_pos_iff.mpr
    have htcc : t ∈ Icc s u := ⟨ht.1.le, ht.2.le⟩
    have hfar : A < ‖γ t‖ := hout t ⟨ht.1, ht.2.le⟩
    have hpuncture : γ t ∉ pointPunctures a y := by
      rintro ⟨j, _, hj⟩
      apply pointExterior_sub_ne_zero (hz t htcc) ((hyA j).trans hfar.le)
      rw [hj, sub_self]
    exact pointConformal_geodesic_deriv_ne_zero ha y γ hc L hL hgeo
      ⟨hs.trans ht.1, ht.2.trans hu⟩ hpuncture
  have hrmon : StrictMonoOn (fun t => ‖γ t‖) (Icc s u) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hc.norm.continuousOn
    intro t ht
    have ht' : t ∈ Ioo s u := by simpa only [interior_Icc] using ht
    rw [(hrD t ht').deriv]
    exact mul_pos (hv t ht') (hcos t ht')
  have hHanti {x z : ℝ} (hx : 0 < x) (hxz : x ≤ z) : H z ≤ H x := by
    have hz' : 0 < z := hx.trans_le hxz
    apply add_le_add
    · exact div_le_div_of_nonneg_left (Real.rpow_nonneg hA.le _)
        (Real.rpow_pos_of_pos hx _) (Real.rpow_le_rpow hx.le hxz hp.le)
    · exact div_le_div_of_nonneg_left hDnonneg (mul_pos hB hx)
        (mul_le_mul_of_nonneg_left hxz hB.le)
  refine ⟨φ, hφ, fun t ht => (hlift t ht).2, ?_⟩
  intro t ht hsmall
  have hsub (x : ℝ) (hx : x ∈ Icc t u) : x ∈ Icc s u := ⟨ht.1.trans hx.1, hx.2⟩
  have hsubo (x : ℝ) (hx : x ∈ Ioo t u) : x ∈ Ioo s u := ⟨ht.1.trans_lt hx.1, hx.2⟩
  have hhalf (x : ℝ) (hx : x ∈ Ioo t u) : 1 / 2 ≤ Real.cos (θ x - φ x) := by
    have hxcc : x ∈ Icc s u := hsub x ⟨hx.1.le, hx.2.le⟩
    apply cos_half_le_of_nonneg_of_abs_sin_le_half (hcos x (hsubo x hx)).le
    exact (hsin x hxcc).trans ((hHanti (hz t ht)
      (hrmon.monotoneOn ht hxcc hx.1.le)).trans hsmall)
  apply angular_increment_bound_of_affine_tail_data ht.2 hA.le hB hDnonneg
    hc.norm.continuousOn hφ.continuousOn
    (fun x hx => hz x (hsub x hx)) (fun _ _ => norm_nonneg _)
    (fun x hx => hrD x (hsubo x hx)) (fun x hx => hφD x (hsubo x hx)) hhalf
  intro x hx
  exact hsin x (hsub x ⟨hx.1.le, hx.2.le⟩)

end RepulsiveCoulomb
