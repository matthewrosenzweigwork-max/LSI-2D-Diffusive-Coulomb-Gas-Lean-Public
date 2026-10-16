import LeanResearch.RepulsiveCoulomb.JordanAffineTraceTangent
import LeanResearch.RepulsiveCoulomb.JordanRoundedPointIncrement
import LeanResearch.RepulsiveCoulomb.JordanRadialCornerTurnReplacement
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Actual tangent accounting at one constructed radial corner. The two old
collars and two new half-patches are identified by their literal physical
traces. Their speeds are transported by the proved positive-affine chain
rule; no arbitrary equal-image representative is declared unit speed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- The actual charted rounding contributes exactly the two removed old
collar turns and the actual adjacent-velocity principal corner turn. -/
theorem radial_corner_rounding_tangent_accounting
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsSimplyConnected U)
    {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H U)
    (hHreg : ∀ z ∈ U, deriv H z ≠ 0) (hHinj : InjOn H U)
    {u v : ℂ} (hu : u ≠ 0) (hc : v / u ∈ Complex.slitPlane)
    (hLU : MapsTo (euclideanIncomingRadius u) (Icc (0 : ℝ) 1) U)
    (hRU : MapsTo (euclideanOutgoingRadius v) (Icc (0 : ℝ) 1) U)
    (hBU : MapsTo (euclideanBezierCorner u v) (Icc (0 : ℝ) 1) U)
    (L R A B : ℝ → ℂ)
    (hL : ContDiff ℝ 1 L) (hR : ContDiff ℝ 1 R)
    (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B)
    (hLr : ∀ t ∈ Icc (0 : ℝ) 1, deriv L t ≠ 0)
    (hRr : ∀ t ∈ Icc (0 : ℝ) 1, deriv R t ≠ 0)
    (hAr : ∀ t ∈ Icc (0 : ℝ) 1, deriv A t ≠ 0)
    (hBr : ∀ t ∈ Icc (0 : ℝ) 1, deriv B t ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hδq : δ < 1 / 4)
    (holdL : ∀ t ∈ Icc (0 : ℝ) 1,
      L ((1 - δ) + δ * t) = H (euclideanIncomingRadius u t))
    (holdR : ∀ t ∈ Icc (0 : ℝ) 1,
      R (δ * t) = H (euclideanOutgoingRadius v t))
    (hnewL : ∀ t ∈ Icc (0 : ℝ) 1,
      A ((1 - δ) + δ * t) = H (euclideanBezierCorner u v (t / 2)))
    (hnewR : ∀ t ∈ Icc (0 : ℝ) 1,
      B (δ * t) = H (euclideanBezierCorner u v ((t + 1) / 2)))
    (a b : Icc (0 : ℝ) 1) (ha : (a : ℝ) = δ) (hb : (b : ℝ) = 1 - δ)
    (θL θR ψL ψR : Icc (0 : ℝ) 1 → ℝ)
    (hθL : Continuous θL) (hθR : Continuous θR)
    (hψL : Continuous ψL) (hψR : Continuous ψR)
    (hθLl : ∀ t, Complex.exp ((θL t : ℂ) * Complex.I) = deriv L t / (‖deriv L t‖ : ℂ))
    (hθRl : ∀ t, Complex.exp ((θR t : ℂ) * Complex.I) = deriv R t / (‖deriv R t‖ : ℂ))
    (hψLl : ∀ t, Complex.exp ((ψL t : ℂ) * Complex.I) = deriv A t / (‖deriv A t‖ : ℂ))
    (hψRl : ∀ t, Complex.exp ((ψR t : ℂ) * Complex.I) = deriv B t / (‖deriv B t‖ : ℂ)) :
    (ψL 1 - ψL b) + (ψR a - ψR 0) =
      (θL 1 - θL b) + (θR a - θR 0) + Complex.arg (deriv R 0 / deriv L 1) := by
  have hLin (t : Icc (0 : ℝ) 1) :
      (unitIntervalAffine b 1 t : ℝ) = (1 - δ) + δ * t := by
    change (b : ℝ) + (1 - (b : ℝ)) * (t : ℝ) = _
    rw [hb]
    ring
  have hRin (t : Icc (0 : ℝ) 1) : (unitIntervalAffine 0 a t : ℝ) = δ * t := by
    change 0 + ((a : ℝ) - 0) * (t : ℝ) = _
    rw [ha]
    ring
  have hLI (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (1 - δ) + δ * t ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [ht.1, ht.2]
  have hRI (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : δ * t ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [ht.1, ht.2]
  have hdPhysL (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      DifferentiableAt ℝ (H ∘ euclideanIncomingRadius u) t := by
    have hh := ((hH _ (hLU ht)).differentiableAt.hasDerivAt).comp t
      (show HasDerivAt (euclideanIncomingRadius u) u t from by
        simpa only [euclideanIncomingRadius_deriv] using
          ((show Differentiable ℝ (euclideanIncomingRadius u) from by
            unfold euclideanIncomingRadius; fun_prop) t).hasDerivAt)
    exact hh.differentiableAt
  have hdPhysR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      DifferentiableAt ℝ (H ∘ euclideanOutgoingRadius v) t := by
    have hh := ((hH _ (hRU ht)).differentiableAt.hasDerivAt).comp t
      (show HasDerivAt (euclideanOutgoingRadius v) v t from by
        simpa only [euclideanOutgoingRadius_deriv] using
          ((show Differentiable ℝ (euclideanOutgoingRadius v) from by
            unfold euclideanOutgoingRadius; fun_prop) t).hasDerivAt)
    exact hh.differentiableAt
  have hdL (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      deriv (H ∘ euclideanIncomingRadius u) t = δ • deriv L ((1 - δ) + δ * t) := by
    have hh := hasDerivAt_positive_affine_trace (hL.differentiable (by norm_num)) (1 - δ) δ t
    exact (deriv_eq_of_eqOn_unitInterval ht (hdPhysL t ht) hh.differentiableAt
      (fun s hs => (holdL s hs).symm)).trans hh.deriv
  have hdR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      deriv (H ∘ euclideanOutgoingRadius v) t = δ • deriv R (δ * t) := by
    have hh := hasDerivAt_positive_affine_trace (hR.differentiable (by norm_num)) 0 δ t
    have hh' : HasDerivAt (fun s => R (δ * s)) (δ • deriv R (δ * t)) t := by
      simpa only [zero_add] using hh
    exact (deriv_eq_of_eqOn_unitInterval ht (hdPhysR t ht) hh'.differentiableAt
      (fun s hs => (holdR s hs).symm)).trans hh'.deriv
  obtain ⟨P, hP, hPgerm, _, hPreg, _, _, _, _, _⟩ :=
    exists_holomorphic_bezier_smooth_arc hU hH hHreg hHinj hu hc hBU
  have hPC1 : ContDiff ℝ 1 P := hP.of_le (by simp)
  obtain ⟨β, hβ, hβl⟩ := exists_regular_edge_tangent_angle_lift hPC1 hPreg
  have hβphys (t : Icc (0 : ℝ) 1) : Complex.exp ((β t : ℂ) * Complex.I) =
      deriv (H ∘ euclideanBezierCorner u v) t / (‖deriv (H ∘ euclideanBezierCorner u v) t‖ : ℂ) := by
    rw [hβl, (hPgerm t t.2).deriv_eq]
  have hθLphys (t : Icc (0 : ℝ) 1) :
      Complex.exp ((θL (unitIntervalAffine b 1 t) : ℂ) * Complex.I) =
        deriv (H ∘ euclideanIncomingRadius u) t / (‖deriv (H ∘ euclideanIncomingRadius u) t‖ : ℂ) := by
    rw [hθLl, hLin, hdL t t.2, normalized_complex_smul_pos (hLr _ (hLI t t.2)) hδ]
  have hθRphys (t : Icc (0 : ℝ) 1) :
      Complex.exp ((θR (unitIntervalAffine 0 a t) : ℂ) * Complex.I) =
        deriv (H ∘ euclideanOutgoingRadius v) t / (‖deriv (H ∘ euclideanOutgoingRadius v) t‖ : ℂ) := by
    rw [hθRl, hRin, hdR t t.2, normalized_complex_smul_pos (hRr _ (hRI t t.2)) hδ]
  have hturn := conformal_radial_corner_turn_replacement hU hUc hH.differentiableOn
    hH.deriv.continuousOn hHreg hu hc hLU hRU hBU
    (hθL.comp (unitIntervalAffine_continuous _ _))
    (hθR.comp (unitIntervalAffine_continuous _ _)) hβ hθLphys hθRphys hβphys
  have harg : Complex.arg (deriv (H ∘ euclideanOutgoingRadius v) 0 /
        deriv (H ∘ euclideanIncomingRadius u) 1) = Complex.arg (deriv R 0 / deriv L 1) := by
    rw [hdR 0 (by norm_num), hdL 1 (by norm_num), mul_zero,
      show (1 - δ) + δ * 1 = 1 by ring]
    simp only [Complex.real_smul]
    exact conformal_corner_principal_turn (δ : ℂ) _ _ (Complex.ofReal_ne_zero.mpr hδ.ne')
  rw [harg] at hturn
  simp only [Function.comp_apply, unitIntervalAffine_zero, unitIntervalAffine_one] at hturn
  have hnewLangle (t : Icc (0 : ℝ) 1) :
      Circle.exp (ψL (unitIntervalAffine b 1 t)) = Circle.exp (β (cornerFirstHalf t)) := by
    apply Circle.ext
    change Complex.exp ((ψL (unitIntervalAffine b 1 t) : ℂ) * Complex.I) =
      Complex.exp ((β (cornerFirstHalf t) : ℂ) * Complex.I)
    rw [hψLl, hβl, hLin]
    have htP : (t : ℝ) / 2 ∈ Icc (0 : ℝ) 1 := (cornerFirstHalf t).2
    have heq (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        A ((1 - δ) + δ * s) = P (0 + (1 / 2) * s) := by
      have hsp : s / 2 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hs.1, hs.2]
      rw [show 0 + (1 / 2 : ℝ) * s = s / 2 by ring,
        (hPgerm _ hsp).self_of_nhds]
      exact hnewL s hs
    have he := positive_affine_trace_tangent_direction (hA.differentiable (by norm_num))
      (hPC1.differentiable (by norm_num)) hδ (by norm_num : (0 : ℝ) < 1 / 2)
      t.2 heq (hAr _ (hLI t t.2))
      (by simpa only [zero_add, one_div, inv_mul_eq_div] using hPreg _ htP)
    simpa only [cornerFirstHalf, zero_add, one_div, inv_mul_eq_div] using he
  have hnewRangle (t : Icc (0 : ℝ) 1) :
      Circle.exp (ψR (unitIntervalAffine 0 a t)) = Circle.exp (β (cornerSecondHalf t)) := by
    apply Circle.ext
    change Complex.exp ((ψR (unitIntervalAffine 0 a t) : ℂ) * Complex.I) =
      Complex.exp ((β (cornerSecondHalf t) : ℂ) * Complex.I)
    rw [hψRl, hβl, hRin]
    have htP : ((t : ℝ) + 1) / 2 ∈ Icc (0 : ℝ) 1 := (cornerSecondHalf t).2
    have heq (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        B (0 + δ * s) = P (1 / 2 + (1 / 2) * s) := by
      have hsp : (s + 1) / 2 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hs.1, hs.2]
      rw [zero_add, show (1 / 2 : ℝ) + (1 / 2) * s = (s + 1) / 2 by ring,
        (hPgerm _ hsp).self_of_nhds]
      exact hnewR s hs
    have he := positive_affine_trace_tangent_direction (hB.differentiable (by norm_num))
      (hPC1.differentiable (by norm_num)) hδ (by norm_num : (0 : ℝ) < 1 / 2)
      t.2 heq (by simpa only [zero_add] using hBr _ (hRI t t.2))
      (by rw [show (1 / 2 : ℝ) + (1 / 2) * (t : ℝ) = ((t : ℝ) + 1) / 2 by ring]; exact hPreg _ htP)
    simpa only [zero_add, cornerSecondHalf,
      show (1 / 2 : ℝ) + (1 / 2) * (t : ℝ) = ((t : ℝ) + 1) / 2 by ring] using he
  have hnew := two_half_argument_increment
    (ψL ∘ unitIntervalAffine b 1) (ψR ∘ unitIntervalAffine 0 a) β
    (hψL.comp (unitIntervalAffine_continuous _ _))
    (hψR.comp (unitIntervalAffine_continuous _ _)) hβ hnewLangle hnewRangle
  simp only [Function.comp_apply, unitIntervalAffine_zero, unitIntervalAffine_one] at hnew
  exact hnew.trans hturn

end RepulsiveCoulomb
