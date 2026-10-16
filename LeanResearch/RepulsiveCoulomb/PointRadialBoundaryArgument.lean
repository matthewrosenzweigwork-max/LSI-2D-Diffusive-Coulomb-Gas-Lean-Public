module

public import LeanResearch.RepulsiveCoulomb.PointArcObserverCorrection
public import LeanResearch.RepulsiveCoulomb.PointHolomorphicExteriorRays

@[expose] public section

/-! The actual outside-zero winding theorem and the two literal radial
collars determine the argument increment on the rest of a Jordan boundary.
The full sector angle is retained, including reflex sectors. These identities
are derived from actual point-angle lifts, not supplied flux values. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- Three actual boundary portions, in their original order, have zero
sum of argument increments around an actual outside point. -/
theorem jordan_outside_three_arc_argument_sum_zero
    (γ : Icc (0 : ℝ) 1 → ℂ) (hγ : Continuous γ) (hclose : γ 0 = γ 1)
    {U V : Set ℂ} (hK : IsCompact (closure U)) (hV : IsOpen V) (hVc : IsConnected V)
    (hcover : U ∪ V = (range γ)ᶜ) {w : ℂ} (hw : w ∈ V)
    (βL βM βR : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1)
    (hcL : Continuous βL) (hcM : Continuous βM) (hcR : Continuous βR)
    (hstart : βL 0 = 0) (hLM : βL 1 = βM 0) (hMR : βM 1 = βR 0)
    (hfinish : βR 1 = 1)
    (ψL ψM ψR : Icc (0 : ℝ) 1 → ℝ)
    (hψL : Continuous ψL) (hψM : Continuous ψM) (hψR : Continuous ψR)
    (hLL : ∀ t, Complex.exp ((ψL t : ℂ) * Complex.I) =
      (γ (βL t) - w) / (‖γ (βL t) - w‖ : ℂ))
    (hML : ∀ t, Complex.exp ((ψM t : ℂ) * Complex.I) =
      (γ (βM t) - w) / (‖γ (βM t) - w‖ : ℂ))
    (hRL : ∀ t, Complex.exp ((ψR t : ℂ) * Complex.I) =
      (γ (βR t) - w) / (‖γ (βR t) - w‖ : ℂ)) :
    (ψL 1 - ψL 0) + (ψM 1 - ψM 0) + (ψR 1 - ψR 0) = 0 := by
  have havoid (t : Icc (0 : ℝ) 1) : γ t ≠ w := by
    intro heq
    have hwc : w ∈ (range γ)ᶜ := hcover ▸ Or.inr hw
    exact hwc ⟨t, heq⟩
  obtain ⟨θ, hθ, hθlift⟩ := exists_interval_euclidean_angle_lift
    (hγ.sub continuous_const) (fun t => sub_ne_zero.mpr (havoid t))
  have hzero := jordan_outside_argument_increment_zero γ hγ hclose hK hV hVc hcover
    hw θ hθ hθlift
  have hpart (β : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1) (hc : Continuous β)
      (ψ : Icc (0 : ℝ) 1 → ℝ) (hψ : Continuous ψ)
      (hl : ∀ t, Complex.exp ((ψ t : ℂ) * Complex.I) =
        (γ (β t) - w) / (‖γ (β t) - w‖ : ℂ)) :
      ψ 1 - ψ 0 = θ (β 1) - θ (β 0) := by
    have h := euclidean_angle_lift_increment_eq hψ (hθ.comp hc)
      (fun t => by
        apply Circle.ext
        simpa only [Circle.coe_exp, Function.comp_def] using
          (hl t).trans (hθlift (β t)).symm) (0 : Icc (0 : ℝ) 1) 1
    exact h
  rw [hpart βL hcL ψL hψL hLL, hpart βM hcM ψM hψM hML,
    hpart βR hcR ψR hψR hRL, hstart, hLM, hMR, hfinish]
  linarith

/-- A sufficiently small common chart disk works for every full sector
angle and every actual Jordan boundary with the displayed two radial collars.
The remaining-arc angle is determined exactly, including its holomorphic
endpoint corrections. Shrinking the cutoff will remove these corrections. -/
theorem exists_radial_boundary_remaining_argument_formula {W : Set ℂ}
    (hW : IsOpen W) (hW0 : (0 : ℂ) ∈ W) {H : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H W) (hD : deriv H 0 ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ball (0 : ℂ) R ⊆ W ∧
      ∀ ρ θ φ : ℝ, 0 < ρ → ρ < R → 0 < θ → θ < φ → φ < 2 * Real.pi →
      ∀ (γ : Icc (0 : ℝ) 1 → ℂ), Continuous γ → γ 0 = γ 1 →
      ∀ U V : Set ℂ, IsCompact (closure U) → IsOpen V → IsConnected V →
      U ∪ V = (range γ)ᶜ →
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), H (pointRadialSectorPoint ε φ) ∈ V) →
      ∀ βL βM βR : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1,
      Continuous βL → Continuous βM → Continuous βR →
      βL 0 = 0 → βL 1 = βM 0 → βM 1 = βR 0 → βR 1 = 1 →
      (∀ t, γ (βL t) = H (pointRadialSectorPoint (ρ * t.1) 0)) →
      (∀ t, γ (βR t) = H (pointRadialSectorPoint (ρ * (1 - t.1)) θ)) →
      (∀ t, γ (βM t) ≠ H 0) →
      ∀ ψ : Icc (0 : ℝ) 1 → ℝ, Continuous ψ →
      (∀ t, Complex.exp ((ψ t : ℂ) * Complex.I) =
        (γ (βM t) - H 0) / (‖γ (βM t) - H 0‖ : ℂ)) →
      ψ 1 - ψ 0 = θ - pointHolomorphicSecantCorrection H (pointRadialSectorPoint ρ 0) 0 +
        pointHolomorphicSecantCorrection H (pointRadialSectorPoint ρ θ) 0 := by
  obtain ⟨R, hR, hRW, hpos, hbranch⟩ :=
    exists_holomorphic_exterior_radial_argument_branches hW hW0 hH hD
  refine ⟨R, hR, hRW, ?_⟩
  intro ρ θ φ hρ hρR hθ hθφ hφ2 γ hγ hclose U V hK hV hVc hcover hout
    βL βM βR hcL hcM hcR hstart hLM hMR hfinish hleft hright havoid ψ hψ hψlift
  let η : Icc (0 : ℝ) 1 → ℂ := γ ∘ βM
  let w : ℝ → ℂ := fun ε => H (pointRadialSectorPoint ε φ)
  have hη : Continuous η := hγ.comp hcM
  have hηavoid : ∀ t, η t ≠ H 0 := havoid
  obtain ⟨δ, hδ, hslit⟩ := exists_uniform_arc_observer_slit_disk η hη (H 0) hηavoid
  have hrad : Tendsto (fun ε : ℝ => pointRadialSectorPoint ε φ) (𝓝 0) (𝓝 (0 : ℂ)) := by
    have hc : Continuous (fun ε : ℝ => pointRadialSectorPoint ε φ) := by
      unfold pointRadialSectorPoint
      fun_prop
    simpa only [pointRadialSectorPoint_zero] using hc.tendsto 0
  have hw : Tendsto w (𝓝 0) (𝓝 (H 0)) := (hH 0 hW0).continuousAt.tendsto.comp hrad
  have hwδ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), w ε ∈ ball (H 0) δ :=
    mem_nhdsWithin_of_mem_nhds (hw (ball_mem_nhds _ hδ))
  have hεR : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < R :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hR)
  have hbalance : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      pointArcObserverArgument η ψ (H 0) (w ε) 1 -
        pointArcObserverArgument η ψ (H 0) (w ε) 0 =
      -(pointHolomorphicExteriorRadialArgument H ε φ 0 ρ -
        pointHolomorphicExteriorRadialArgument H ε φ θ ρ) := by
    filter_upwards [self_mem_nhdsWithin, hεR, hwδ, hout] with ε hε hεR hwδ hwV
    have hεpos : 0 < ε := hε
    obtain ⟨hc0, hl0, hz0⟩ := hbranch ε φ 0 ρ hεpos hεR hρ.le hρR
      (by linarith) (by simpa using hφ2)
    obtain ⟨hcθ, hlθ, hzθ⟩ := hbranch ε φ θ ρ hεpos hεR hρ.le hρR
      (sub_pos.mpr hθφ) (by linarith)
    let rL : Icc (0 : ℝ) 1 → ℝ := fun t => ρ * t.1
    let rR : Icc (0 : ℝ) 1 → ℝ := fun t => ρ * (1 - t.1)
    have hrL : Continuous rL := continuous_const.mul continuous_subtype_val
    have hrR : Continuous rR := continuous_const.mul (continuous_const.sub continuous_subtype_val)
    have hmL (t : Icc (0 : ℝ) 1) : rL t ∈ Icc (0 : ℝ) ρ := by
      dsimp [rL]
      exact ⟨mul_nonneg hρ.le t.2.1, by nlinarith [t.2.2]⟩
    have hmR (t : Icc (0 : ℝ) 1) : rR t ∈ Icc (0 : ℝ) ρ := by
      dsimp [rR]
      constructor <;> nlinarith [t.2.1, t.2.2]
    let ψL := pointHolomorphicExteriorRadialArgument H ε φ 0 ∘ rL
    let ψR := pointHolomorphicExteriorRadialArgument H ε φ θ ∘ rR
    let ψM := pointArcObserverArgument η ψ (H 0) (w ε)
    have hψLc : Continuous ψL := hc0.comp_continuous hrL hmL
    have hψRc : Continuous ψR := hcθ.comp_continuous hrR hmR
    obtain ⟨hψMc, hψML⟩ := pointArcObserverArgument_continuous_lift hη hψ hηavoid
      (fun t => (hslit (w ε) hwδ t).1) (fun t => (hslit (w ε) hwδ t).2) hψlift
    have hsum := jordan_outside_three_arc_argument_sum_zero γ hγ hclose hK hV hVc hcover
      hwV βL βM βR hcL hcM hcR hstart hLM hMR hfinish ψL ψM ψR hψLc hψMc hψRc
      (fun t => by rw [hleft t]; exact hl0 (rL t) (hmL t))
      hψML (fun t => by rw [hright t]; exact hlθ (rR t) (hmR t))
    have hcommon : pointHolomorphicExteriorRadialArgument H ε φ 0 0 =
        pointHolomorphicExteriorRadialArgument H ε φ θ 0 := hz0.trans hzθ.symm
    dsimp [ψL, ψR, ψM, rL, rR, Function.comp_def] at hsum
    norm_num only [mul_one, mul_zero, sub_zero, sub_self] at hsum
    rw [hcommon] at hsum
    linarith
  have hpoint0 (A : ℝ) : pointRadialSectorPoint ρ A ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hρ.le]
    exact hρR
  have hne (A : ℝ) : pointRadialSectorPoint ρ A ≠ 0 :=
    norm_pos_iff.mp (by rw [pointRadialSectorPoint_norm hρ.le]; exact hρ)
  have hlimV := holomorphic_exterior_two_ray_observer_limit (hH 0 hW0).continuousAt hD
    hρ hθ hθφ hφ2
    (hpos _ (hpoint0 0) 0 (mem_ball_self hR) (hne 0))
    (hpos _ (hpoint0 θ) 0 (mem_ball_self hR) (hne θ))
  have hlimM := (pointArcObserverArgument_increment_tendsto η ψ
    (0 : Icc (0 : ℝ) 1) 1 (hηavoid 0) (hηavoid 1)).comp hw
  have hbalance' :
      (fun ε => pointArcObserverArgument η ψ (H 0) (w ε) 1 -
        pointArcObserverArgument η ψ (H 0) (w ε) 0) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε => -(pointHolomorphicExteriorRadialArgument H ε φ 0 ρ -
        pointHolomorphicExteriorRadialArgument H ε φ θ ρ)) := hbalance
  have heq := tendsto_nhds_unique (hlimM.mono_left nhdsWithin_le_nhds)
    ((hlimV.neg.mono_left nhdsWithin_le_nhds).congr' hbalance'.symm)
  linarith

end RepulsiveCoulomb
