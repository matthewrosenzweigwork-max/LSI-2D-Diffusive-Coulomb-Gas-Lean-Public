module

public import LeanResearch.RepulsiveCoulomb.PointGeodesicSubsegmentConservedLifts
public import LeanResearch.RepulsiveCoulomb.PointGeodesicExteriorRadialConvexity
public import LeanResearch.RepulsiveCoulomb.ComplexRadialPowerLiftDerivative
public import LeanResearch.RepulsiveCoulomb.ScalarRadialTurningTime
public import LeanResearch.RepulsiveCoulomb.ExteriorPhaseCosineAperture
public import Mathlib.Tactic

@[expose] public section

/-! Uncompiled additive successor. Actual minimizing segment to actual
constructed subsegment aperture. All angle lifts, the radial turning time,
cosine branches and the positive affine speed are constructed/derived here.
The caller supplies no lift, phase, ODE or visibility certificate. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointExteriorMoment_nonneg {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) : 0 ≤ pointExteriorMoment a y := by
  unfold pointExteriorMoment
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun j _ =>
    mul_nonneg (div_nonneg (ha j) (by norm_num)) (norm_nonneg _))

theorem pointConformal_geodesic_actual_subsegment_aperture
    {n : ℕ} {a : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin n → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {A : ℝ} (hA : 0 < A) (hyA : ∀ j, 2 * ‖y j‖ ≤ A)
    (hB : 0 < pointExteriorHalfMass a)
    (hD : pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * A)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, A < ‖γ t‖)
    (hend : ‖γ 0‖ = ‖γ 1‖) :
    ∃ m ∈ Ioo (0 : ℝ) 1, ∀ s u : ℝ, 0 < s → s < m → m < u → u < 1 →
      ∃ φ : ℝ → ℝ, Continuous φ ∧
        (∀ t ∈ Icc s u, Complex.exp ((φ t : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ)) ∧
        |φ u - φ s| ≤
          (Real.pi + 2 * (pointExteriorMoment a y / A)) / (1 + pointExteriorHalfMass a) := by
  let B := pointExteriorHalfMass a
  let p := 1 + B
  let D := pointExteriorMoment a y
  let F : ℝ → ℝ := fun t => Real.rpow (‖γ t‖ ^ 2) p
  have hp : 0 < p := by dsimp [p, B]; linarith
  have hz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < ‖γ t‖ := hA.trans (havoid t ht)
  have hy (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (j : Fin n) : 2 * ‖y j‖ ≤ ‖γ t‖ :=
    (hyA j).trans (havoid t ht).le
  have hpunc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∉ pointPunctures a y := by
    rintro ⟨j, _, hj⟩
    apply pointExterior_sub_ne_zero (hz t ht) (hy t ht j)
    rw [hj, sub_self]
  have hsecond : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < deriv (deriv F) t := by
    intro t ht
    have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    apply pointConformal_geodesic_exterior_radial_second_pos ha y γ hc L hL hgeo ht
      (hpunc t htcc) (hz t htcc) (hy t htcc) hB
    exact hD.trans (mul_lt_mul_of_pos_left (havoid t htcc) hp)
  have hFc : Continuous F := (hc.norm.pow 2).rpow_const (fun _ => Or.inr hp.le)
  have hFend : F 0 = F 1 := by dsimp [F]; rw [hend]
  obtain ⟨m, hm, hmzero, hmleft, hmright, _⟩ :=
    exists_scalar_turning_time_of_deriv2_pos (by norm_num : (0 : ℝ) < 1)
      hFc.continuousOn hFend hsecond
  refine ⟨m, hm, ?_⟩
  intro s u hs hsm hmu hu
  have hsu : s < u := hsm.trans hmu
  have hsub (t : ℝ) (ht : t ∈ Icc s u) : t ∈ Icc (0 : ℝ) 1 :=
    ⟨(hs.trans_le ht.1).le, (ht.2.trans_lt hu).le⟩
  have hsubo (t : ℝ) (ht : t ∈ Icc s u) : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨hs.trans_le ht.1, ht.2.trans_lt hu⟩
  obtain ⟨θ, φ, C, hθ, hφ, hlift⟩ :=
    exists_pointConformal_exterior_subsegment_conserved_lifts ha y γ hc L hL hgeo
      hs hsu hu (fun t ht => hz t (hsub t ht)) (fun t ht => hy t (hsub t ht))
  let ψ : ℝ → ℝ := fun t => θ t - φ t
  let δ : ℝ → ℝ := fun t => pointExteriorPhaseCorrection a y (γ t)
  let w : ℝ → ℝ := fun t => ‖deriv γ t‖ / ‖γ t‖
  have hψ : Continuous ψ := hθ.sub hφ
  have hdiff (t : ℝ) (ht : t ∈ Icc s u) : DifferentiableAt ℝ γ t :=
    (pointConformal_geodesic_analyticAt ha y γ hc L hgeo (hsubo t ht)
      (hpunc t (hsub t ht))).differentiableAt
  have hvel (t : ℝ) (ht : t ∈ Icc s u) : deriv γ t ≠ 0 :=
    pointConformal_geodesic_deriv_ne_zero ha y γ hc L hL hgeo
      (hsubo t ht) (hpunc t (hsub t ht))
  have hcoef (t : ℝ) (ht : t ∈ Icc s u) :
      0 < radialPolarCoefficient p (γ t) (deriv γ t) :=
    radialPolarCoefficient_pos hp (norm_pos_iff.mp (hz t (hsub t ht))) (hvel t ht)
  have hpolar (t : ℝ) (ht : t ∈ Icc s u) :
      deriv F t = radialPolarCoefficient p (γ t) (deriv γ t) * Real.cos (ψ t) :=
    radialPower_deriv_eq_polar p (hdiff t ht) (norm_pos_iff.mp (hz t (hsub t ht)))
      (hvel t ht) (hlift t ht).1 (hlift t ht).2.1
  have hmcc : m ∈ Icc s u := ⟨hsm.le, hmu.le⟩
  have hzero : Real.cos (ψ m) = 0 := by
    have h := hmzero
    rw [hpolar m hmcc] at h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (hcoef m hmcc))
  have hleft : ∀ t ∈ Ico s m, Real.cos (ψ t) < 0 := by
    intro t ht
    have htcc : t ∈ Icc s u := ⟨ht.1, ht.2.le.trans hmu.le⟩
    have hn := hmleft t ⟨hs.trans_le ht.1, ht.2⟩
    rw [hpolar t htcc] at hn
    by_contra hnot
    have hnonneg := mul_nonneg (hcoef t htcc).le (le_of_not_gt hnot)
    linarith
  have hright : ∀ t ∈ Ioc m u, 0 < Real.cos (ψ t) := by
    intro t ht
    have htcc : t ∈ Icc s u := ⟨hsm.le.trans ht.1.le, ht.2⟩
    have hn := hmright t ⟨ht.1, ht.2.trans_lt hu⟩
    rw [hpolar t htcc] at hn
    by_contra hnot
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos (hcoef t htcc).le (le_of_not_gt hnot)
    linarith
  have hphase : ∀ t ∈ Icc s u, p * φ t + ψ t + δ t = C := by
    intro t ht
    calc
      _ = θ t + B * φ t + pointExteriorPhaseCorrection a y (γ t) := by dsimp [p, ψ, δ]; ring
      _ = C := (hlift t ht).2.2
  have hδ : ∀ t ∈ Icc s u, |δ t| ≤ D / A := by
    intro t ht
    exact (abs_pointExteriorPhaseCorrection_le ha y (hz t (hsub t ht)) (hy t (hsub t ht))).trans
      (div_le_div_of_nonneg_left (pointExteriorMoment_nonneg ha y) hA (havoid t (hsub t ht)).le)
  have hderiv : ∀ t ∈ Ioo s u, HasDerivAt φ (w t * Real.sin (ψ t)) t := by
    intro t ht
    have htcc : t ∈ Icc s u := ⟨ht.1.le, ht.2.le⟩
    apply continuous_radial_lift_hasDerivAt_polar (hdiff t htcc)
      (norm_pos_iff.mp (hz t (hsub t htcc))) (hvel t htcc) hφ.continuousAt
      ?_ (hlift t htcc).1
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with v hv
    exact (hlift v ⟨hv.1.le, hv.2.le⟩).2.1
  have hw : ∀ t ∈ Ioo s u, 0 < w t := by
    intro t ht
    exact div_pos (norm_pos_iff.mpr (hvel t ⟨ht.1.le, ht.2.le⟩))
      (hz t (hsub t ⟨ht.1.le, ht.2.le⟩))
  refine ⟨φ, hφ, fun t ht => (hlift t ht).2.1, ?_⟩
  exact exterior_phase_aperture_of_cosine_signs hsm hmu hp hφ hψ hphase hδ hzero
    hleft hright hderiv hw ⟨le_rfl, hsu.le⟩ ⟨hsu.le, le_rfl⟩

end RepulsiveCoulomb
