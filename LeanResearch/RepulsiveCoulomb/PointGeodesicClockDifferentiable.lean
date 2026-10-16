import LeanResearch.RepulsiveCoulomb.PointGeodesicOrientedClock
import LeanResearch.RepulsiveCoulomb.PointGeodesicPhysicalSpeed
import LeanResearch.RepulsiveCoulomb.PointConformalPhaseChart
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! A regular equal-image representative of an actual geodesic has a
strictly positive differentiable source clock away from the punctures.
Differentiability is proved by constructing an affine developing chart and
recovering the clock by a real-linear coordinate. In particular it is not
inferred just from strict monotonicity. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- An actual developing chart makes the original constant-speed parameter
locally affine, and its affine velocity is nonzero. -/
theorem exists_pointConformal_geodesic_phase_affine_development {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : ℝ → ℂ) (hc : Continuous γ)
    (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hp : γ t ∉ pointPunctures a y) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ H : ℂ → ℂ, ∃ A B : ℂ,
      B ≠ 0 ∧ γ t ∈ e.source ∧ AnalyticOnNhd ℂ H e.source ∧
      (∀ z ∈ e.source, AnalyticAt ℂ e z ∧ deriv e z = Complex.exp (H z) ∧
        (H z).re = pointConformalLog a y z ∧
        deriv H z = pointConformalConnection a y z) ∧
      ∀ᶠ v in 𝓝 t, γ v ∈ e.source ∧ e (γ v) = A + (v : ℂ) * B := by
  obtain ⟨e, H, r, hr, hep, _, hsource, _, _, hHA, he, hmetric⟩ :=
    exists_pointConformal_phase_metric_chart ha y hp
  let U : Set ℝ := Ioo 0 1 ∩ γ ⁻¹' ball (γ t) r
  have hU : IsOpen U := isOpen_Ioo.inter (isOpen_ball.preimage hc)
  have htU : t ∈ U := ⟨ht, mem_ball_self hr⟩
  obtain ⟨ε, hε, hsmall⟩ := Metric.isOpen_iff.mp hU t htU
  let s := t - ε / 2
  let u := t + ε / 2
  have hst : s < t := by dsimp [s]; linarith
  have htu : t < u := by dsimp [u]; linarith
  have hsu : s < u := hst.trans htu
  have hlocal (v : ℝ) (hv : v ∈ Icc s u) : v ∈ U := by
    apply hsmall
    rw [mem_ball, Real.dist_eq]
    dsimp [s, u] at hv
    exact abs_lt.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have h01 (v : ℝ) (hv : v ∈ Icc s u) : v ∈ Icc (0 : ℝ) 1 :=
    ⟨(hlocal v hv).1.1.le, (hlocal v hv).1.2.le⟩
  have hsrc (v : ℝ) (hv : v ∈ Icc s u) : γ v ∈ e.source :=
    hsource (hlocal v hv).2
  let B : ℂ := (e (γ u) - e (γ s)) / ((u - s : ℝ) : ℂ)
  let A : ℂ := e (γ s) - (s : ℂ) * B
  have hB : B ≠ 0 := by
    apply div_ne_zero
    · apply sub_ne_zero.mpr
      intro heq
      have hgsu : γ s = γ u := e.injOn (hsrc s ⟨le_rfl, hsu.le⟩)
        (hsrc u ⟨hsu.le, le_rfl⟩) heq.symm
      have h := hgeo s (h01 s ⟨le_rfl, hsu.le⟩) u (h01 u ⟨hsu.le, le_rfl⟩)
      rw [hgsu, pointSmoothConformalEDist_self, ENNReal.toReal_zero] at h
      have hpos : 0 < |u - s| * L :=
        mul_pos (abs_pos.mpr (sub_ne_zero.mpr hsu.ne')) hL
      linarith
    · exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hsu.ne')
  have hmet (v : ℝ) (hv : v ∈ Icc s u) (w : ℝ) (hw : w ∈ Icc s u) :
      (pointSmoothConformalEDist a y (γ v) (γ w)).toReal = dist (e (γ v)) (e (γ w)) := by
    rw [hmetric _ (hlocal v hv).2 _ (hlocal w hw).2,
      ENNReal.toReal_ofReal (norm_nonneg _), dist_eq_norm']
  refine ⟨e, H, A, B, hB, hep, hHA, he, ?_⟩
  filter_upwards [Ioo_mem_nhds hst htu] with v hv
  refine ⟨hsrc v ⟨hv.1.le, hv.2.le⟩, ?_⟩
  have hf := (flat_chart_geodesic_affine_parameter a y e hsu γ L hsrc hmet
    (fun v hv w hw => hgeo v (h01 v hv) w (h01 w hw))
    ⟨hv.1.le, hv.2.le⟩).1
  rw [hf, AffineMap.lineMap_apply_module', Complex.real_smul]
  dsimp [A, B]
  push_cast
  ring

/-- Forget only the phase data when a real-linear clock coordinate suffices. -/
theorem exists_pointConformal_geodesic_affine_development {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : ℝ → ℂ) (hc : Continuous γ)
    (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hp : γ t ∉ pointPunctures a y) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ A B : ℂ,
      B ≠ 0 ∧ AnalyticAt ℂ e (γ t) ∧
      ∀ᶠ v in 𝓝 t, e (γ v) = A + (v : ℂ) * B := by
  obtain ⟨e, H, A, B, hB, hep, _, he, hflat⟩ :=
    exists_pointConformal_geodesic_phase_affine_development ha y γ hc L hL hgeo ht hp
  exact ⟨e, A, B, hB, (he _ hep).1, hflat.mono (fun _ hv => hv.2)⟩

/-- The literal clock is recovered from an affine chart coordinate. Its
regularity is derived from that of the new representative. -/
theorem differentiableAt_clock_of_affine_development
    {g η : ℝ → ℂ} {τ : ℝ → ℝ} {u : ℝ} {e : ℂ → ℂ} {A B : ℂ}
    (hB : B ≠ 0) (hτ : ContinuousAt τ u) (hη : DifferentiableAt ℝ η u)
    (he : DifferentiableAt ℂ e (η u))
    (hparam : η =ᶠ[𝓝 u] (g ∘ τ))
    (hflat : ∀ᶠ v in 𝓝 (τ u), e (g v) = A + (v : ℂ) * B) :
    DifferentiableAt ℝ τ u := by
  let f : ℝ → ℝ := fun v => ((e (η v) - A) / B).re
  have hf : DifferentiableAt ℝ f u := by
    exact Complex.reCLM.differentiableAt.comp u
      ((((he.restrictScalars ℝ).comp u hη).sub_const A).div_const B)
  have heq : τ =ᶠ[𝓝 u] f := by
    filter_upwards [hparam, hτ.tendsto.eventually hflat] with v hv hfv
    dsimp [Function.comp_def] at hv
    dsimp [f]
    rw [hv, hfv]
    simp [hB]
  exact hf.congr_of_eventuallyEq heq

/-- The metric-distance clock has positive derivative at every regular
nonpuncture parameter. The tangent relation and physical speed are both proved;
the representative is never assigned the original constant metric speed. -/
theorem pointConformal_equal_image_oriented_clock_positive {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {x z : ℂ} (hxz : x ≠ z)
    (γ : Icc (0 : ℝ) 1 → ℂ) (h0 : γ ⟨0, by norm_num⟩ = x)
    (hd : ∀ v w, (pointSmoothConformalEDist a y (γ v) (γ w)).toReal =
      |w.1 - v.1| * (pointSmoothConformalEDist a y x z).toReal)
    (s t : Icc (0 : ℝ) 1) (hst : s < t) {η : ℝ → ℂ}
    (hc : ContinuousOn η (Icc (0 : ℝ) 1)) (hi : InjOn η (Icc (0 : ℝ) 1))
    (hη0 : η 0 = γ s) (hη1 : η 1 = γ t)
    (himage : η '' Icc (0 : ℝ) 1 = γ '' Icc s t)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hη : DifferentiableAt ℝ η u)
    (hηne : deriv η u ≠ 0) (hp : η u ∉ pointPunctures a y) :
    let τ := pointGeodesicMetricClock a y x z η
    let g := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ
    DifferentiableAt ℝ τ u ∧ 0 < deriv τ u ∧
      deriv η u = deriv τ u • deriv g (τ u) ∧
      pointConformalDensity a y (η u) * ‖deriv η u‖ =
        deriv τ u * (pointSmoothConformalEDist a y x z).toReal := by
  let τ := pointGeodesicMetricClock a y x z η
  let g := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ
  let D := (pointSmoothConformalEDist a y x z).toReal
  have hD : 0 < D := by
    apply ENNReal.toReal_pos
    · exact (pointSmoothConformalEDist_eq_zero_iff ha y x z).not.mpr hxz
    · exact (pointSmoothConformalEDist_lt_top ha y x z).ne
  obtain ⟨hτc, hτm, hτ0, hτ1, hτrange, hparam⟩ :=
    pointConformal_equal_image_oriented_clock ha y hxz γ h0 hd s t hst hc hi hη0 hη1 himage
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
  have hparamN : η =ᶠ[𝓝 u] (g ∘ τ) := by
    filter_upwards [huN] with v hv
    exact hparam v hv
  have hparamu : η u = g (τ u) := hparam u hucc
  have hg : Continuous g := continuous_IccExtend_iff.mpr
    (pointConformal_geodesic_continuous ha y γ hd)
  have hgeo : ∀ v ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (g v) (g w)).toReal = |w - v| * D := by
    intro v hv w hw
    dsimp [g]
    rw [IccExtend_of_mem _ _ hv, IccExtend_of_mem _ _ hw]
    exact hd ⟨v, hv⟩ ⟨w, hw⟩
  have hpg : g (τ u) ∉ pointPunctures a y := by rwa [← hparamu]
  obtain ⟨e, A, B, hB, heA, hflat⟩ :=
    exists_pointConformal_geodesic_affine_development ha y g hg D hD hgeo hτu hpg
  have he : DifferentiableAt ℂ e (η u) := by
    rw [hparamu]
    exact heA.differentiableAt
  have hτd : DifferentiableAt ℝ τ u :=
    differentiableAt_clock_of_affine_development hB hτuc hη he hparamN hflat
  have hgd : DifferentiableAt ℝ g (τ u) :=
    (pointConformal_geodesic_analyticAt ha y g hg D hgeo hτu hpg).differentiableAt
  have htan : deriv η u = deriv τ u • deriv g (τ u) :=
    hparamN.deriv_eq.trans (hgd.hasDerivAt.scomp u hτd.hasDerivAt).deriv
  have hnonneg : 0 ≤ deriv τ u := by
    have h := hτm.monotoneOn.derivWithin_nonneg (x := u)
    rwa [derivWithin_of_mem_nhds huN] at h
  have hpos : 0 < deriv τ u := lt_of_le_of_ne hnonneg (by
    intro heq
    apply hηne
    rw [htan, ← heq, zero_smul])
  refine ⟨hτd, hpos, htan, ?_⟩
  have hspeed := pointConformal_geodesic_physical_speed ha y g hg D hgeo hτu hpg
  rw [htan, norm_smul, Real.norm_eq_abs, abs_of_pos hpos, hparamu]
  calc
    _ = deriv τ u * (pointConformalDensity a y (g (τ u)) * ‖deriv g (τ u)‖) := by ring
    _ = _ := by rw [hspeed]

end RepulsiveCoulomb
