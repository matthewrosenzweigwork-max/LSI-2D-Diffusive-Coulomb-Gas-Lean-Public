module

public import LeanResearch.RepulsiveCoulomb.PointGeodesicClockDifferentiable
public import LeanResearch.RepulsiveCoulomb.PointConformalArgumentTransport
public import LeanResearch.RepulsiveCoulomb.JordanBezierCorner

@[expose] public section

/-! The actual conformal tangent equation on a regular reparameterized
geodesic. A positive clock factor is derived, so the normalized tangent phase
is independent of speed. No second derivative of the C1 representative is
needed to differentiate its continuous tangent-angle lift. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- A continuous lift through the real exponential covering inherits a
local real derivative. The integer ambiguity is eliminated locally. -/
theorem hasDerivAt_of_eventually_circle_exp_eq {θ φ : ℝ → ℝ} {u : ℝ}
    (hθ : ContinuousAt θ u) (hφ : DifferentiableAt ℝ φ u)
    (hexp : ∀ᶠ v in 𝓝 u, Circle.exp (θ v) = Circle.exp (φ v)) :
    HasDerivAt θ (deriv φ u) u := by
  have hθN : ∀ᶠ v in 𝓝 u, θ v - θ u ∈ Ioo (-Real.pi) Real.pi := by
    apply (hθ.sub continuousAt_const).tendsto.eventually
    change Ioo (-Real.pi) Real.pi ∈ 𝓝 (θ u - θ u)
    simpa only [sub_self] using
      Ioo_mem_nhds (neg_neg_of_pos Real.pi_pos) Real.pi_pos
  have hφN : ∀ᶠ v in 𝓝 u, φ v - φ u ∈ Ioo (-Real.pi) Real.pi := by
    apply (hφ.continuousAt.sub continuousAt_const).tendsto.eventually
    change Ioo (-Real.pi) Real.pi ∈ 𝓝 (φ u - φ u)
    simpa only [sub_self] using
      Ioo_mem_nhds (neg_neg_of_pos Real.pi_pos) Real.pi_pos
  have heq : θ =ᶠ[𝓝 u] (fun v => θ u + (φ v - φ u)) := by
    filter_upwards [hθN, hφN, hexp] with v hvθ hvφ hvexp
    have hdexp : Circle.exp (θ v - θ u) = Circle.exp (φ v - φ u) := by
      rw [Circle.exp_sub, Circle.exp_sub, hvexp, hexp.self_of_nhds]
    have h := (Circle.exp_injOn_Ico (a := -Real.pi) (b := Real.pi) (by linarith))
      ⟨hvθ.1.le, hvθ.2⟩ ⟨hvφ.1.le, hvφ.2⟩ hdexp
    linarith
  exact ((hφ.hasDerivAt.sub_const (φ u)).const_add (θ u)).congr_of_eventuallyEq heq

/-- A varying positive real speed changes no tangent direction. This
produces the derivative of the actual tangent-angle lift from the phase. -/
theorem positive_parallel_phase_angle_hasDerivAt
    {V G : ℝ → ℂ} {c θ : ℝ → ℝ} {w : ℂ} {u : ℝ}
    (hw : w ≠ 0) (hG : DifferentiableAt ℝ G u) (hθ : ContinuousAt θ u)
    (hdata : ∀ᶠ v in 𝓝 u, 0 < c v ∧ V v ≠ 0 ∧
      Complex.exp (G v) * V v = c v • w ∧
      Complex.exp ((θ v : ℂ) * Complex.I) = V v / (‖V v‖ : ℂ)) :
    HasDerivAt θ (-(deriv G u).im) u := by
  let φ : ℝ → ℝ := fun v => Complex.arg w - (G v).im
  have hφD : HasDerivAt φ (-(deriv G u).im) u := by
    convert! (Complex.imCLM.hasFDerivAt.comp_hasDerivAt u hG.hasDerivAt).const_sub
      (Complex.arg w) using 1 <;> simp [φ, Function.comp_def]
  have hexp : ∀ᶠ v in 𝓝 u, Circle.exp (θ v) = Circle.exp (φ v) := by
    filter_upwards [hdata] with v hv
    obtain ⟨hcv, hvne, hparallel, hlift0⟩ := hv
    have hlift : Circle.exp (θ v) = euclideanDirection (V v) hvne := Circle.ext hlift0
    have hdir : euclideanDirection (Complex.exp (G v) * V v)
        (mul_ne_zero (Complex.exp_ne_zero _) hvne) = euclideanDirection w hw := by
      calc
        _ = euclideanDirection (c v • w) (smul_ne_zero hcv.ne' hw) := by
          apply Circle.ext
          simp only [euclideanDirection_coe, hparallel]
        _ = _ := euclideanDirection_smul_pos hw hcv
    have hsum : Circle.exp (θ v + (G v).im) = Circle.exp (Complex.arg w) := by
      rw [Circle.exp_add, hlift, ← euclideanDirection_cexp, mul_comm,
        ← euclideanDirection_mul _ _ (Complex.exp_ne_zero _) hvne, hdir,
        ← euclideanDirection_arg w hw, Circle.exp_arg]
    dsimp [φ]
    calc
      Circle.exp (θ v) = Circle.exp (θ v + (G v).im) / Circle.exp (G v).im := by
        rw [Circle.exp_add, mul_div_cancel_right]
      _ = Circle.exp (Complex.arg w - (G v).im) := by
        rw [hsum, Circle.exp_sub]
  have h := hasDerivAt_of_eventually_circle_exp_eq hθ hφD.differentiableAt hexp
  rwa [hφD.deriv] at h

/-- The positive phase transport is constructed for the actual equal-image
representative from its original metric geodesic. -/
theorem exists_pointConformal_equal_image_positive_parallel_phase
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {x z : ℂ} (hxz : x ≠ z) (γ : Icc (0 : ℝ) 1 → ℂ)
    (h0 : γ ⟨0, by norm_num⟩ = x)
    (hd : ∀ v w, (pointSmoothConformalEDist a y (γ v) (γ w)).toReal =
      |w.1 - v.1| * (pointSmoothConformalEDist a y x z).toReal)
    (s t : Icc (0 : ℝ) 1) (hst : s < t) {η : ℝ → ℂ}
    (hη : ContDiff ℝ 1 η) (hi : InjOn η (Icc (0 : ℝ) 1))
    (hreg : ∀ v ∈ Icc (0 : ℝ) 1, deriv η v ≠ 0)
    (hη0 : η 0 = γ s) (hη1 : η 1 = γ t)
    (himage : η '' Icc (0 : ℝ) 1 = γ '' Icc s t)
    (havoid : ∀ v ∈ Ioo (0 : ℝ) 1, η v ∉ pointPunctures a y)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ∃ H : ℂ → ℂ, ∃ w : ℂ, w ≠ 0 ∧ DifferentiableAt ℂ H (η u) ∧
      deriv H (η u) = pointConformalConnection a y (η u) ∧
      ∀ᶠ v in 𝓝 u,
        0 < deriv (pointGeodesicMetricClock a y x z η) v ∧
        Complex.exp (H (η v)) * deriv η v =
          deriv (pointGeodesicMetricClock a y x z η) v • w := by
  let τ := pointGeodesicMetricClock a y x z η
  let g := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ
  let D := (pointSmoothConformalEDist a y x z).toReal
  have hD : 0 < D := by
    apply ENNReal.toReal_pos
    · exact (pointSmoothConformalEDist_eq_zero_iff ha y x z).not.mpr hxz
    · exact (pointSmoothConformalEDist_lt_top ha y x z).ne
  obtain ⟨hτc, hτm, hτ0, hτ1, _, hparam⟩ :=
    pointConformal_equal_image_oriented_clock ha y hxz γ h0 hd s t hst
      hη.continuous.continuousOn hi hη0 hη1 himage
  have hucc : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
  have huN : Icc (0 : ℝ) 1 ∈ 𝓝 u :=
    mem_of_superset (Ioo_mem_nhds hu.1 hu.2) Ioo_subset_Icc_self
  have hτuc : ContinuousAt τ u := (hτc u hucc).continuousAt huN
  have hτu : τ u ∈ Ioo (0 : ℝ) 1 := by
    have hl := hτm (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) hucc hu.1
    have hr := hτm hucc (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) hu.2
    rw [hτ0] at hl
    rw [hτ1] at hr
    exact ⟨s.2.1.trans_lt hl, hr.trans_le t.2.2⟩
  have hg : Continuous g := continuous_IccExtend_iff.mpr
    (pointConformal_geodesic_continuous ha y γ hd)
  have hgeo : ∀ v ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (g v) (g w)).toReal = |w - v| * D := by
    intro v hv w hw
    dsimp [g]
    rw [IccExtend_of_mem _ _ hv, IccExtend_of_mem _ _ hw]
    exact hd ⟨v, hv⟩ ⟨w, hw⟩
  have hparamu : η u = g (τ u) := hparam u hucc
  have hpu : g (τ u) ∉ pointPunctures a y := by
    rw [← hparamu]
    exact havoid u hu
  obtain ⟨e, H, A, B, hB, hep, hHA, he, hflat⟩ :=
    exists_pointConformal_geodesic_phase_affine_development ha y g hg D hD hgeo hτu hpu
  have hηsrc : η u ∈ e.source := by rwa [hparam u hucc]
  have hlocal : ∀ᶠ v in 𝓝 u,
      η v ∈ e.source ∧ e (η v) = A + (τ v : ℂ) * B := by
    filter_upwards [huN, hτuc.tendsto.eventually hflat] with v hv hf
    rw [hparam v hv]
    exact hf
  have heq : (e ∘ η) =ᶠ[𝓝 u] (fun v => A + (τ v : ℂ) * B) :=
    hlocal.mono (fun _ hv => hv.2)
  refine ⟨H, B, hB, (hHA _ hηsrc).differentiableAt, (he _ hηsrc).2.2.2, ?_⟩
  filter_upwards [Ioo_mem_nhds hu.1 hu.2, hlocal, heq.eventually_nhds] with v hv hsrc heqv
  have hvcc : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
  obtain ⟨hτd, hpos, _, _⟩ := pointConformal_equal_image_oriented_clock_positive
    ha y hxz γ h0 hd s t hst hη.continuous.continuousOn hi hη0 hη1 himage
    hv (hη.differentiable (by norm_num) v) (hreg v hvcc) (havoid v hv)
  have hcomp : deriv (e ∘ η) v = Complex.exp (H (η v)) * deriv η v := by
    have hed := (he _ hsrc.1).1.differentiableAt
    rw [fderiv_comp_deriv v (hed.restrictScalars ℝ)
      (hη.differentiable (by norm_num) v), hed.fderiv_restrictScalars (𝕜 := ℝ)]
    change (fderiv ℂ e (η v)) (deriv η v) = _
    simp only [fderiv_eq_smul_deriv, (he _ hsrc.1).2.1, smul_eq_mul]
    ring
  have hline : HasDerivAt (fun r => A + (τ r : ℂ) * B)
      (((deriv τ v : ℝ) : ℂ) * B) v :=
    (hτd.hasDerivAt.ofReal_comp.mul_const B).const_add A
  have heqv' : (e ∘ η) =ᶠ[𝓝 v] (fun r => A + (τ r : ℂ) * B) := heqv
  refine ⟨hpos, ?_⟩
  rw [← hcomp, heqv'.deriv_eq, hline.deriv, Complex.real_smul]

/-- Differentiate the actual continuous tangent-angle lift of a C1 macro-arc.
All conformal transport data are constructed from its original geodesic. -/
theorem pointConformal_equal_image_tangent_angle_hasDerivAt
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {x z : ℂ} (hxz : x ≠ z) (γ : Icc (0 : ℝ) 1 → ℂ)
    (h0 : γ ⟨0, by norm_num⟩ = x)
    (hd : ∀ v w, (pointSmoothConformalEDist a y (γ v) (γ w)).toReal =
      |w.1 - v.1| * (pointSmoothConformalEDist a y x z).toReal)
    (s t : Icc (0 : ℝ) 1) (hst : s < t) {η : ℝ → ℂ}
    (hη : ContDiff ℝ 1 η) (hi : InjOn η (Icc (0 : ℝ) 1))
    (hreg : ∀ v ∈ Icc (0 : ℝ) 1, deriv η v ≠ 0)
    (hη0 : η 0 = γ s) (hη1 : η 1 = γ t)
    (himage : η '' Icc (0 : ℝ) 1 = γ '' Icc s t)
    (havoid : ∀ v ∈ Ioo (0 : ℝ) 1, η v ∉ pointPunctures a y)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) {θ : ℝ → ℝ}
    (hθ : ContinuousAt θ u)
    (hlift : ∀ᶠ v in 𝓝 u, Complex.exp ((θ v : ℂ) * Complex.I) =
      deriv η v / (‖deriv η v‖ : ℂ)) :
    HasDerivAt θ (-(pointConformalConnection a y (η u) * deriv η u).im) u := by
  obtain ⟨H, w, hw, hH, hconnection, hparallel⟩ :=
    exists_pointConformal_equal_image_positive_parallel_phase ha y hxz γ h0 hd s t hst
      hη hi hreg hη0 hη1 himage havoid hu
  have hG : HasDerivAt (H ∘ η) (pointConformalConnection a y (η u) * deriv η u) u := by
    have h := hH.hasDerivAt.comp u (hη.differentiable (by norm_num) u).hasDerivAt
    rwa [hconnection] at h
  have hdata : ∀ᶠ v in 𝓝 u,
      0 < deriv (pointGeodesicMetricClock a y x z η) v ∧ deriv η v ≠ 0 ∧
      Complex.exp ((H ∘ η) v) * deriv η v =
        deriv (pointGeodesicMetricClock a y x z η) v • w ∧
      Complex.exp ((θ v : ℂ) * Complex.I) = deriv η v / (‖deriv η v‖ : ℂ) := by
    filter_upwards [hparallel, hlift, Ioo_mem_nhds hu.1 hu.2] with v hv hl hv01
    exact ⟨hv.1, hreg v ⟨hv01.1.le, hv01.2.le⟩, hv.2, hl⟩
  have h := positive_parallel_phase_angle_hasDerivAt hw hG.differentiableAt hθ hdata
  rwa [hG.deriv] at h

end RepulsiveCoulomb
