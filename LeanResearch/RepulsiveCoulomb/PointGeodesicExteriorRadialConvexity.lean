import LeanResearch.RepulsiveCoulomb.PointGeodesicAcceleration
import LeanResearch.RepulsiveCoulomb.PointExteriorConnectionEstimates
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
UNCOMPILED ADDITIVE DRAFT, 2026-10-02. No accepted-source or inventory claim.

This identifies and estimates the actual second derivative along an actual
metric-affinely parameterized minimizing curve. We differentiate (‖γ‖²)^p,
so no formal Riemannian-Hessian identity is assumed. For r=‖γ‖ this is r^(2p).
The actual geodesic equation is imported from the constructed phase chart.
-/

noncomputable section
open Set Metric Filter InnerProductSpace
open scoped Topology ComplexConjugate RealInnerProductSpace

namespace RepulsiveCoulomb

def complexRadialPowerSecond (p : ℝ) (z v A : ℂ) : ℝ :=
  p * Real.rpow (‖z‖ ^ 2) (p - 2) *
    ((p - 1) * (2 * ⟪z, v⟫_ℝ) ^ 2 +
      ‖z‖ ^ 2 * (2 * (‖v‖ ^ 2 + ⟪z, A⟫_ℝ)))

theorem hasDerivAt_complexRadialPowerVelocity {γ : ℝ → ℂ} {t : ℝ} {A : ℂ}
    (p : ℝ) (hγ : DifferentiableAt ℝ γ t)
    (hacc : HasDerivAt (deriv γ) A t) (hne : γ t ≠ 0) :
    HasDerivAt
      (fun u => (2 * ⟪γ u, deriv γ u⟫_ℝ) * p *
        Real.rpow (‖γ u‖ ^ 2) (p - 1))
      (complexRadialPowerSecond p (γ t) (deriv γ t) A) t := by
  have hs : 0 < ‖γ t‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hq := hγ.hasDerivAt.norm_sq
  have hq' : HasDerivAt (fun u => 2 * ⟪γ u, deriv γ u⟫_ℝ)
      (2 * (‖deriv γ t‖ ^ 2 + ⟪γ t, A⟫_ℝ)) t := by
    simpa only [real_inner_self_eq_norm_sq, add_comm] using
      (hγ.hasDerivAt.inner ℝ hacc).const_mul 2
  have hpow : Real.rpow (‖γ t‖ ^ 2) (p - 1) =
      Real.rpow (‖γ t‖ ^ 2) (p - 2) * ‖γ t‖ ^ 2 := by
    simp only [Real.rpow_eq_pow]
    rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add hs, Real.rpow_one]
  have h := (hq'.mul_const p).mul (hq.rpow_const (p := p - 1) (Or.inl (ne_of_gt hs)))
  convert h using 1
  unfold complexRadialPowerSecond
  simp only [Real.rpow_eq_pow] at hpow ⊢
  rw [hpow]
  have hexp : p - 1 - 1 = p - 2 := by ring
  rw [hexp]
  ring

theorem pointConformal_geodesic_radialPower_hasDerivAt_deriv
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hp : γ t ∉ pointPunctures a y)
    (hne : γ t ≠ 0) (p : ℝ) :
    HasDerivAt (deriv (fun u => Real.rpow (‖γ u‖ ^ 2) p))
      (complexRadialPowerSecond p (γ t) (deriv γ t)
        (-(pointConformalConnection a y (γ t) * (deriv γ t) ^ 2))) t := by
  have hγA := pointConformal_geodesic_analyticAt ha y γ hc L hgeo ht hp
  have hacc := pointConformal_geodesic_hasDerivAt_deriv ha y γ hc L hL hgeo ht hp
  have hnonzero : ∀ᶠ u in 𝓝 t, γ u ≠ 0 :=
    hc.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hne)
  have hfirst : deriv (fun u => Real.rpow (‖γ u‖ ^ 2) p) =ᶠ[𝓝 t]
      (fun u => (2 * ⟪γ u, deriv γ u⟫_ℝ) * p *
        Real.rpow (‖γ u‖ ^ 2) (p - 1)) := by
    filter_upwards [hγA.eventually_analyticAt, hnonzero] with u hAu hnu
    exact ((hAu.differentiableAt.hasDerivAt.norm_sq).rpow_const
      (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hnu)))).deriv
  exact (hasDerivAt_complexRadialPowerVelocity p hγA.differentiableAt hacc hne).congr_of_eventuallyEq hfirst

theorem complex_real_inner_eq_conj_mul_re (z v : ℂ) :
    ⟪z, v⟫_ℝ = (conj z * v).re := by
  rw [Complex.inner, mul_comm]

theorem complex_two_inner_sq (z v : ℂ) :
    2 * ⟪z, v⟫_ℝ ^ 2 =
      ‖z‖ ^ 2 * ‖v‖ ^ 2 + (conj z ^ 2 * v ^ 2).re := by
  rw [complex_real_inner_eq_conj_mul_re,
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Exact cancellation of the homogeneous logarithmic connection. The sole
algebraic hypothesis is a scalar connection decomposition, instantiated below
with the proved literal finite-product connection. -/
theorem complex_radial_connection_bracket (B : ℝ) (z v K E : ℂ)
    (hK : z * K = (B : ℂ) + z * E) :
    B * (2 * ⟪z, v⟫_ℝ) ^ 2 +
      ‖z‖ ^ 2 * (2 * (‖v‖ ^ 2 + ⟪z, -(K * v ^ 2)⟫_ℝ)) =
      2 * ‖z‖ ^ 2 *
        ((1 + B) * ‖v‖ ^ 2 - (conj z * E * v ^ 2).re) := by
  have hn : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hprod : ((‖z‖ ^ 2 : ℝ) : ℂ) * (conj z * K * v ^ 2) =
      (B : ℂ) * (conj z ^ 2 * v ^ 2) +
        ((‖z‖ ^ 2 : ℝ) : ℂ) * (conj z * E * v ^ 2) := by
    calc
      _ = conj z ^ 2 * (z * K) * v ^ 2 := by rw [hn]; ring
      _ = conj z ^ 2 * ((B : ℂ) + z * E) * v ^ 2 := by rw [hK]
      _ = _ := by rw [hn]; ring
  have hreal : ‖z‖ ^ 2 * (conj z * K * v ^ 2).re =
      B * (conj z ^ 2 * v ^ 2).re +
        ‖z‖ ^ 2 * (conj z * E * v ^ 2).re := by
    have h := congrArg Complex.re hprod
    simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using h
  have hinner := complex_two_inner_sq z v
  have hneg : ⟪z, -(K * v ^ 2)⟫_ℝ = -(conj z * K * v ^ 2).re := by
    rw [complex_real_inner_eq_conj_mul_re, mul_neg, Complex.neg_re]
    congr 1
    ring
  rw [hneg]
  linear_combination -2 * hreal + 2 * B * hinner

theorem complex_radial_connection_bracket_pos
    {B D : ℝ} {z v K E : ℂ} (hz : z ≠ 0) (hv : v ≠ 0)
    (hK : z * K = (B : ℂ) + z * E)
    (hE : ‖E‖ ≤ D / ‖z‖ ^ 2) (hD : D < (1 + B) * ‖z‖) :
    0 < B * (2 * ⟪z, v⟫_ℝ) ^ 2 +
      ‖z‖ ^ 2 * (2 * (‖v‖ ^ 2 + ⟪z, -(K * v ^ 2)⟫_ℝ)) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hv2 : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have herr : (conj z * E * v ^ 2).re ≤ D / ‖z‖ * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖conj z * E * v ^ 2‖ := Complex.re_le_norm _
      _ = ‖z‖ * ‖E‖ * ‖v‖ ^ 2 := by simp only [norm_mul, norm_pow, Complex.norm_conj]
      _ ≤ ‖z‖ * (D / ‖z‖ ^ 2) * ‖v‖ ^ 2 := by gcongr
      _ = D / ‖z‖ * ‖v‖ ^ 2 := by field_simp [ne_of_gt hr] <;> ring
  have hsmall : D / ‖z‖ < 1 + B := (div_lt_iff₀ hr).mpr hD
  have hinterior : 0 < (1 + B) * ‖v‖ ^ 2 - (conj z * E * v ^ 2).re := by
    have h := mul_lt_mul_of_pos_right hsmall hv2
    linarith
  rw [complex_radial_connection_bracket B z v K E hK]
  exact mul_pos (by positivity) hinterior

/-- Positive actual radial second derivative, with the same threshold D/p as
the analytic conformal-Hessian proof. There is no assumed Hessian or assumed
geodesic ODE in this statement. -/
theorem pointConformal_geodesic_exterior_radial_second_pos
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hp : γ t ∉ pointPunctures a y)
    (hz : 0 < ‖γ t‖) (hy : ∀ j, 2 * ‖y j‖ ≤ ‖γ t‖)
    (hB : 0 < pointExteriorHalfMass a)
    (hD : pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * ‖γ t‖) :
    0 < deriv (deriv (fun u => Real.rpow (‖γ u‖ ^ 2)
      (1 + pointExteriorHalfMass a))) t := by
  let B := pointExteriorHalfMass a
  let E := pointExteriorConnectionError a y (γ t)
  let K := pointConformalConnection a y (γ t)
  have hz0 : γ t ≠ 0 := norm_pos_iff.mp hz
  have hv := pointConformal_geodesic_deriv_ne_zero ha y γ hc L hL hgeo ht hp
  have hK : γ t * K = (B : ℂ) + γ t * E := by
    dsimp [K, E, B]
    rw [pointExteriorConnectionError_eq]
    field_simp [hz0]
    <;> ring
  have hbracket := complex_radial_connection_bracket_pos hz0 hv hK
    (norm_pointExteriorConnectionError_le ha y hz hy) hD
  have hsecond := pointConformal_geodesic_radialPower_hasDerivAt_deriv
    ha y γ hc L hL hgeo ht hp hz0 (1 + B)
  rw [hsecond.deriv]
  unfold complexRadialPowerSecond
  have hp : 0 < 1 + B := by dsimp [B]; linarith
  have hs : 0 < Real.rpow (‖γ t‖ ^ 2) ((1 + B) - 2) :=
    Real.rpow_pos_of_pos (sq_pos_of_pos hz) _
  have hb' : 0 < ((1 + B) - 1) * (2 * ⟪γ t, deriv γ t⟫_ℝ) ^ 2 +
      ‖γ t‖ ^ 2 * (2 * (‖deriv γ t‖ ^ 2 +
        ⟪γ t, -(pointConformalConnection a y (γ t) * (deriv γ t) ^ 2)⟫_ℝ)) := by
    simpa only [add_sub_cancel_left, K] using hbracket
  exact mul_pos (mul_pos hp hs) hb'

theorem pointConformal_geodesic_exterior_radial_strictConvexOn
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    (hB : 0 < pointExteriorHalfMass a)
    (hz : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ‖γ t‖)
    (hy : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, 2 * ‖y j‖ ≤ ‖γ t‖)
    (hD : ∀ t ∈ Icc (0 : ℝ) 1,
      pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * ‖γ t‖) :
    StrictConvexOn ℝ (Icc (0 : ℝ) 1)
      (fun t => Real.rpow (‖γ t‖ ^ 2) (1 + pointExteriorHalfMass a)) := by
  have hpnonneg : 0 ≤ 1 + pointExteriorHalfMass a := by linarith
  have hf : Continuous (fun t => Real.rpow (‖γ t‖ ^ 2)
      (1 + pointExteriorHalfMass a)) :=
    (hc.norm.pow 2).rpow_const (fun _ => Or.inr hpnonneg)
  apply strictConvexOn_of_deriv2_pos (convex_Icc _ _) hf.continuousOn
  intro t ht
  have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using ht
  have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht'.1.le, ht'.2.le⟩
  have hp : γ t ∉ pointPunctures a y := by
    rintro ⟨j, _, hj⟩
    have hne := pointExterior_sub_ne_zero (hz t htcc) (hy t htcc j)
    apply hne
    rw [hj, sub_self]
  change 0 < deriv (deriv (fun u => Real.rpow (‖γ u‖ ^ 2)
    (1 + pointExteriorHalfMass a))) t
  exact pointConformal_geodesic_exterior_radial_second_pos ha y γ hc L hL hgeo
    ht' hp (hz t htcc) (hy t htcc) hB (hD t htcc)

end RepulsiveCoulomb
