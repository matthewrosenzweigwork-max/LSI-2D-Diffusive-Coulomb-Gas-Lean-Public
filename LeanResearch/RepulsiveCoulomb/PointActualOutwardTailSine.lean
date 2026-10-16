import LeanResearch.RepulsiveCoulomb.PointGeodesicSubsegmentConservedLifts
import LeanResearch.RepulsiveCoulomb.PointGeodesicExteriorRadialConvexity
import LeanResearch.RepulsiveCoulomb.PointGeodesicActualSubsegmentAperture
import LeanResearch.RepulsiveCoulomb.ComplexRadialPowerLiftDerivative
import LeanResearch.RepulsiveCoulomb.AffineMomentumPotentialBound
import LeanResearch.RepulsiveCoulomb.ScalarOutwardDerivative
import Mathlib.Tactic

/-! Uncompiled additive successor. Construct the actual angle lifts on a
genuine outward geodesic tail starting on a fixed circle. Prove the radial sign
and the uniform sine estimate from the original affine geodesic parameter.
No tangent/radial lift, ODE, or tail estimate is supplied by the caller. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_pointConformal_actual_outward_tail_sine_bound
    {n : ℕ} {a : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin n → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {A s u : ℝ} (hA : 0 < A) (hyA : ∀ j, 2 * ‖y j‖ ≤ A)
    (hB : 0 < pointExteriorHalfMass a)
    (hD : pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * A)
    (hs : 0 < s) (hsu : s < u) (hu : u < 1) (hstart : ‖γ s‖ = A)
    (hout : ∀ t ∈ Ioc s u, A < ‖γ t‖) :
    ∃ θ φ : ℝ → ℝ, Continuous θ ∧ Continuous φ ∧
      (∀ t ∈ Icc s u,
        Complex.exp ((θ t : ℂ) * Complex.I) = deriv γ t / (‖deriv γ t‖ : ℂ) ∧
        Complex.exp ((φ t : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ)) ∧
      (∀ t ∈ Ioo s u, 0 < Real.cos (θ t - φ t)) ∧
      (∀ t ∈ Icc s u, |Real.sin (θ t - φ t)| ≤
        Real.rpow A (1 + pointExteriorHalfMass a) / Real.rpow ‖γ t‖ (1 + pointExteriorHalfMass a) +
          pointExteriorMoment a y / (pointExteriorHalfMass a * ‖γ t‖)) ∧
      (∀ t ∈ Ioo s u, HasDerivAt (fun v => ‖γ v‖)
        (‖deriv γ t‖ * Real.cos (θ t - φ t)) t) ∧
      ∀ t ∈ Ioo s u, HasDerivAt φ
        ((‖deriv γ t‖ / ‖γ t‖) * Real.sin (θ t - φ t)) t := by
  let B := pointExteriorHalfMass a
  let p := 1 + B
  let D := pointExteriorMoment a y
  have hp : 0 < p := by dsimp [p, B]; linarith
  have hDnonneg : 0 ≤ D := pointExteriorMoment_nonneg ha y
  have hge (t : ℝ) (ht : t ∈ Icc s u) : A ≤ ‖γ t‖ := by
    by_cases hts : t = s
    · subst t; rw [hstart]
    · exact (hout t ⟨lt_of_le_of_ne ht.1 (Ne.symm hts), ht.2⟩).le
  have hz (t : ℝ) (ht : t ∈ Icc s u) : 0 < ‖γ t‖ := hA.trans_le (hge t ht)
  have hy (t : ℝ) (ht : t ∈ Icc s u) (j : Fin n) : 2 * ‖y j‖ ≤ ‖γ t‖ :=
    (hyA j).trans (hge t ht)
  have h01 (t : ℝ) (ht : t ∈ Icc s u) : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨hs.trans_le ht.1, ht.2.trans_lt hu⟩
  have hpuncture (t : ℝ) (ht : t ∈ Icc s u) : γ t ∉ pointPunctures a y := by
    rintro ⟨j, _, hj⟩
    apply pointExterior_sub_ne_zero (hz t ht) (hy t ht j)
    rw [hj, sub_self]
  obtain ⟨θ, φ, C, hθ, hφ, hlift⟩ := exists_pointConformal_exterior_subsegment_conserved_lifts
    ha y γ hc L hL hgeo hs hsu hu hz hy
  let ψ : ℝ → ℝ := fun t => θ t - φ t
  let r : ℝ → ℝ := fun t => ‖γ t‖
  let v : ℝ → ℝ := fun t => ‖deriv γ t‖
  let e : ℝ → ℝ := fun t => (pointExteriorConnectionError a y (γ t) * deriv γ t).im
  let F : ℝ → ℝ := fun t => Real.rpow (‖γ t‖ ^ 2) p
  have hγD (t : ℝ) (ht : t ∈ Icc s u) : DifferentiableAt ℝ γ t :=
    (pointConformal_geodesic_analyticAt ha y γ hc L hgeo (h01 t ht) (hpuncture t ht)).differentiableAt
  have hvne (t : ℝ) (ht : t ∈ Icc s u) : deriv γ t ≠ 0 :=
    pointConformal_geodesic_deriv_ne_zero ha y γ hc L hL hgeo (h01 t ht) (hpuncture t ht)
  have hrD (t : ℝ) (ht : t ∈ Icc s u) : HasDerivAt r (v t * Real.cos (ψ t)) t :=
    radius_hasDerivAt_polar (hγD t ht) (norm_pos_iff.mp (hz t ht)) (hvne t ht)
      (hlift t ht).1 (hlift t ht).2.1
  have hφD (t : ℝ) (ht : t ∈ Ioo s u) : HasDerivAt φ ((v t / r t) * Real.sin (ψ t)) t := by
    have htcc : t ∈ Icc s u := ⟨ht.1.le, ht.2.le⟩
    apply continuous_radial_lift_hasDerivAt_polar (hγD t htcc)
      (norm_pos_iff.mp (hz t htcc)) (hvne t htcc) hφ.continuousAt ?_ (hlift t htcc).1
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact (hlift x ⟨hx.1.le, hx.2.le⟩).2.1
  have hψD (t : ℝ) (ht : t ∈ Ioo s u) :
      HasDerivAt ψ (-(p * (v t / r t) * Real.sin (ψ t)) - e t) t := by
    have htcc : t ∈ Icc s u := ⟨ht.1.le, ht.2.le⟩
    have hθD := pointConformal_geodesic_tangent_lift_hasDerivAt ha y γ hc L hL hgeo
      (h01 t htcc) (hpuncture t htcc) hθ.continuousAt
      (show ∀ᶠ x in 𝓝 t, Complex.exp ((θ x : ℂ) * Complex.I) = deriv γ x / (‖deriv γ x‖ : ℂ) from by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
        exact (hlift x ⟨hx.1.le, hx.2.le⟩).1)
    have hcomplex : pointConformalConnection a y (γ t) * deriv γ t =
        (B : ℂ) * (deriv γ t / γ t) + pointExteriorConnectionError a y (γ t) * deriv γ t := by
      dsimp [B]
      rw [pointExteriorConnectionError_eq]
      simp only [div_eq_mul_inv]
      ring
    have him := congrArg Complex.im hcomplex
    simp only [Complex.add_im, Complex.im_ofReal_mul] at him
    rw [complex_div_polar_lift_im (norm_pos_iff.mp (hz t htcc)) (hvne t htcc)
      (hlift t htcc).1 (hlift t htcc).2.1] at him
    convert! hθD.sub (hφD t ht) using 1 <;> dsimp [ψ, p, r, v, e] at * <;> nlinarith [him]
  have hsecond : ∀ t ∈ Ioo s u, 0 < deriv (deriv F) t := by
    intro t ht
    have htcc : t ∈ Icc s u := ⟨ht.1.le, ht.2.le⟩
    apply pointConformal_geodesic_exterior_radial_second_pos ha y γ hc L hL hgeo
      (h01 t htcc) (hpuncture t htcc) (hz t htcc) (hy t htcc) hB
    exact hD.trans_le (mul_le_mul_of_nonneg_left (hge t htcc) hp.le)
  have hFpos : ∀ t ∈ Ioo s u, 0 < deriv F t := by
    apply deriv_pos_of_deriv2_pos_and_above_left_endpoint
      ((hc.norm.pow 2).rpow_const (fun _ => Or.inr hp.le)).continuousOn
    · intro t ht
      exact (((hγD t ⟨ht.1.le, ht.2.le⟩).hasDerivAt.norm_sq).rpow_const
        (p := p) (Or.inl (ne_of_gt (sq_pos_of_pos (hz t ⟨ht.1.le, ht.2.le⟩))))).differentiableAt
    · exact hsecond
    · intro t ht
      dsimp [F]
      rw [hstart]
      apply Real.rpow_lt_rpow (sq_nonneg A) _ hp
      nlinarith [hout t ⟨ht.1, ht.2.le⟩, norm_nonneg (γ t)]
  have hcos : ∀ t ∈ Ioo s u, 0 < Real.cos (ψ t) := by
    intro t ht
    have htcc : t ∈ Icc s u := ⟨ht.1.le, ht.2.le⟩
    have hcoef := radialPolarCoefficient_pos hp (norm_pos_iff.mp (hz t htcc)) (hvne t htcc)
    have hid := radialPower_deriv_eq_polar p (hγD t htcc) (norm_pos_iff.mp (hz t htcc))
      (hvne t htcc) (hlift t htcc).1 (hlift t htcc).2.1
    have hpos := hFpos t ht
    rw [hid] at hpos
    by_contra hn
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hcoef.le (le_of_not_gt hn)
    linarith
  have he : ∀ t ∈ Ioo s u, |e t| ≤ (D / (r t) ^ 2) * v t := by
    intro t ht
    have htcc : t ∈ Icc s u := ⟨ht.1.le, ht.2.le⟩
    apply (Complex.abs_im_le_norm _).trans
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_pointExteriorConnectionError_le ha y (hz t htcc) (hy t htcc)) (norm_nonneg _)
  refine ⟨θ, φ, hθ, hφ, fun t ht => ⟨(hlift t ht).1, (hlift t ht).2.1⟩,
    hcos, ?_, (fun t ht => hrD t ⟨ht.1.le, ht.2.le⟩), hφD⟩
  intro t ht
  have hsub (x : ℝ) (hx : x ∈ Icc s t) : x ∈ Icc s u := ⟨hx.1, hx.2.trans ht.2⟩
  have hsubo (x : ℝ) (hx : x ∈ Ioo s t) : x ∈ Ioo s u := ⟨hx.1, hx.2.trans_le ht.2⟩
  have h := sine_bound_of_affine_radial_tail ht.1 hB hDnonneg
    hc.norm.continuousOn (hθ.sub hφ).continuousOn
    (fun x hx => hz x (hsub x hx)) (fun _ _ => norm_nonneg _)
    (fun x hx => (hcos x (hsubo x hx)).le)
    (fun x hx => hrD x (hsub x ⟨hx.1.le, hx.2.le⟩))
    (fun x hx => hψD x (hsubo x hx)) (fun x hx => he x (hsubo x hx))
  simpa only [r, ψ, Pi.sub_apply, D, hstart] using h

end RepulsiveCoulomb
