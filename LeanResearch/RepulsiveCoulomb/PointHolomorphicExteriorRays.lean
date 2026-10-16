import LeanResearch.RepulsiveCoulomb.PointHolomorphicSecantCorrection

/-! Actual argument branches on the holomorphic images of both radial legs,
with the exact observer and cutoff limits. The disk and its common phase
branch are constructed from holomorphic regularity. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

def pointHolomorphicExteriorRadialArgument (H : ℂ → ℂ) (ε φ A r : ℝ) : ℝ :=
  pointExteriorRadialArgument ε φ A r +
    pointHolomorphicSecantCorrection H (pointRadialSectorPoint r A) (pointRadialSectorPoint ε φ)

private theorem exterior_radial_point_ne_observer {ε r φ A : ℝ}
    (hε : 0 < ε) (hr : 0 ≤ r) (hδ0 : 0 < φ - A) (hδ2 : φ - A < 2 * Real.pi) :
    pointRadialSectorPoint r A ≠ pointRadialSectorPoint ε φ := by
  apply sub_ne_zero.mp
  rw [pointExteriorRayFactor_identity]
  exact mul_ne_zero (neg_ne_zero.mpr (Circle.coe_ne_zero _))
    (Complex.slitPlane_ne_zero (pointExteriorRayFactor_mem_slitPlane hε hr hδ0 hδ2))

private theorem holomorphic_exterior_radial_branch_continuous {H : ℂ → ℂ} {R : ℝ}
    (hc : ContinuousOn H (ball (0 : ℂ) R)) (hD : deriv H 0 ≠ 0)
    (hpos : ∀ z ∈ ball (0 : ℂ) R, ∀ w ∈ ball (0 : ℂ) R, z ≠ w →
      0 < (pointHolomorphicSecantRatio H z w).re)
    (ε φ A ρ : ℝ) (hε : 0 < ε) (hεR : ε < R) (hρR : ρ < R)
    (hδ0 : 0 < φ - A) (hδ2 : φ - A < 2 * Real.pi) :
    ContinuousOn (pointHolomorphicExteriorRadialArgument H ε φ A) (Icc (0 : ℝ) ρ) := by
  let w : ℂ := pointRadialSectorPoint ε φ
  have hw : w ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hε.le]
    exact hεR
  have hz : MapsTo (fun r : ℝ => pointRadialSectorPoint r A) (Icc (0 : ℝ) ρ) (ball (0 : ℂ) R) := by
    intro r hr
    rw [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hr.1]
    exact hr.2.trans_lt hρR
  have hne : ∀ r ∈ Icc (0 : ℝ) ρ, pointRadialSectorPoint r A ≠ w :=
    fun r hr => exterior_radial_point_ne_observer hε hr.1 hδ0 hδ2
  have hpath : Continuous (fun r : ℝ => pointRadialSectorPoint r A) := by
    unfold pointRadialSectorPoint
    fun_prop
  have hHz : ContinuousOn (fun r : ℝ => H (pointRadialSectorPoint r A)) (Icc (0 : ℝ) ρ) :=
    hc.comp hpath.continuousOn hz
  have hden : Continuous (fun r : ℝ => (pointRadialSectorPoint r A - w) * deriv H 0) :=
    (hpath.sub continuous_const).mul_const (deriv H 0)
  have hdenne : ∀ r ∈ Icc (0 : ℝ) ρ, (pointRadialSectorPoint r A - w) * deriv H 0 ≠ 0 :=
    fun r hr => mul_ne_zero (sub_ne_zero.mpr (hne r hr)) hD
  have hQ : ContinuousOn (fun r : ℝ => pointHolomorphicSecantRatio H (pointRadialSectorPoint r A) w)
      (Icc (0 : ℝ) ρ) := by
    unfold pointHolomorphicSecantRatio
    exact (hHz.sub continuousOn_const).div hden.continuousOn hdenne
  have hQslit : MapsTo (fun r : ℝ => pointHolomorphicSecantRatio H (pointRadialSectorPoint r A) w)
      (Icc (0 : ℝ) ρ) Complex.slitPlane :=
    fun r hr => Or.inl (hpos _ (hz hr) w hw (hne r hr))
  have harg := Complex.continuousOn_arg.comp hQ hQslit
  have hbase : ContinuousOn (pointExteriorRadialArgument ε φ A) (Icc (0 : ℝ) ρ) :=
    (pointExteriorRadialArgument_continuousOn hε hδ0 hδ2).mono (fun r hr => hr.1)
  unfold pointHolomorphicExteriorRadialArgument pointHolomorphicSecantCorrection
  exact hbase.add (continuousOn_const.add harg)

private theorem holomorphic_exterior_radial_branch_lift {H : ℂ → ℂ}
    (hD : deriv H 0 ≠ 0) {ε r φ A : ℝ} (hε : 0 < ε) (hr : 0 ≤ r)
    (hδ0 : 0 < φ - A) (hδ2 : φ - A < 2 * Real.pi)
    (hpos : 0 < (pointHolomorphicSecantRatio H (pointRadialSectorPoint r A)
      (pointRadialSectorPoint ε φ)).re) :
    Complex.exp ((pointHolomorphicExteriorRadialArgument H ε φ A r : ℂ) * Complex.I) =
      (H (pointRadialSectorPoint r A) - H (pointRadialSectorPoint ε φ)) /
        (‖H (pointRadialSectorPoint r A) - H (pointRadialSectorPoint ε φ)‖ : ℂ) := by
  have hne := exterior_radial_point_ne_observer hε hr hδ0 hδ2
  have hphase := pointExteriorRadialArgument_lift hε hr hδ0 hδ2
  exact (pointHolomorphicSecantCorrection_lift hD hne hpos hphase).2

/-- Construct one disk that works simultaneously for every exterior angle
and both radial legs. Their real argument branches agree at the vertex. -/
theorem exists_holomorphic_exterior_radial_argument_branches {U : Set ℂ}
    (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U) {H : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H U) (hD : deriv H 0 ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ball (0 : ℂ) R ⊆ U ∧
      (∀ z ∈ ball (0 : ℂ) R, ∀ w ∈ ball (0 : ℂ) R, z ≠ w →
        0 < (pointHolomorphicSecantRatio H z w).re) ∧
      ∀ ε φ A ρ : ℝ, 0 < ε → ε < R → 0 ≤ ρ → ρ < R →
        0 < φ - A → φ - A < 2 * Real.pi →
        ContinuousOn (pointHolomorphicExteriorRadialArgument H ε φ A) (Icc (0 : ℝ) ρ) ∧
        (∀ r ∈ Icc (0 : ℝ) ρ,
          Complex.exp ((pointHolomorphicExteriorRadialArgument H ε φ A r : ℂ) * Complex.I) =
            (H (pointRadialSectorPoint r A) - H (pointRadialSectorPoint ε φ)) /
              (‖H (pointRadialSectorPoint r A) - H (pointRadialSectorPoint ε φ)‖ : ℂ)) ∧
        pointHolomorphicExteriorRadialArgument H ε φ A 0 =
          Complex.arg (-(Circle.exp φ : ℂ)) +
            pointHolomorphicSecantCorrection H 0 (pointRadialSectorPoint ε φ) := by
  obtain ⟨R, hR, hball, hbound⟩ := exists_holomorphic_secant_positive_disk hU h0 hH hD
  have hpos : ∀ z ∈ ball (0 : ℂ) R, ∀ w ∈ ball (0 : ℂ) R, z ≠ w →
      0 < (pointHolomorphicSecantRatio H z w).re :=
    fun z hz w hw hzw => (hbound z hz w hw hzw).2
  refine ⟨R, hR, hball, hpos, ?_⟩
  intro ε φ A ρ hε hεR hρ hρR hδ0 hδ2
  refine ⟨holomorphic_exterior_radial_branch_continuous (hH.continuousOn.mono hball)
    hD hpos ε φ A ρ hε hεR hρR hδ0 hδ2, ?_, ?_⟩
  · intro r hr
    have hz : pointRadialSectorPoint r A ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hr.1]
      exact hr.2.trans_lt hρR
    have hw : pointRadialSectorPoint ε φ ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hε.le]
      exact hεR
    exact holomorphic_exterior_radial_branch_lift hD hε hr.1 hδ0 hδ2
      (hpos _ hz _ hw (exterior_radial_point_ne_observer hε hr.1 hδ0 hδ2))
  · simp only [pointHolomorphicExteriorRadialArgument,
      pointExteriorRadialArgument_zero hε, pointRadialSectorPoint_zero]

/-- For a fixed cutoff the observer limit is minus the full interior angle
plus the two actual holomorphic endpoint corrections. No principal-angle
replacement is made, even for a reflex sector. -/
theorem holomorphic_exterior_two_ray_observer_limit {H : ℂ → ℂ}
    (hc : ContinuousAt H 0) (hD : deriv H 0 ≠ 0) {ρ θ φ : ℝ}
    (hρ : 0 < ρ) (hθ0 : 0 < θ) (hθφ : θ < φ) (hφ2 : φ < 2 * Real.pi)
    (hpos0 : 0 < (pointHolomorphicSecantRatio H (pointRadialSectorPoint ρ 0) 0).re)
    (hposθ : 0 < (pointHolomorphicSecantRatio H (pointRadialSectorPoint ρ θ) 0).re) :
    Tendsto (fun ε : ℝ => pointHolomorphicExteriorRadialArgument H ε φ 0 ρ -
      pointHolomorphicExteriorRadialArgument H ε φ θ ρ) (𝓝 0)
      (𝓝 (-θ + (pointHolomorphicSecantCorrection H (pointRadialSectorPoint ρ 0) 0 -
        pointHolomorphicSecantCorrection H (pointRadialSectorPoint ρ θ) 0))) := by
  have hn (A : ℝ) : pointRadialSectorPoint ρ A ≠ 0 :=
    norm_pos_iff.mp (by rw [pointRadialSectorPoint_norm hρ.le]; exact hρ)
  have hpath : Tendsto (fun ε : ℝ => pointRadialSectorPoint ε φ) (𝓝 0) (𝓝 0) := by
    have h : Continuous (fun ε : ℝ => pointRadialSectorPoint ε φ) := by
      unfold pointRadialSectorPoint
      fun_prop
    simpa only [pointRadialSectorPoint_zero] using h.tendsto 0
  have hχ0 := (pointHolomorphicSecantCorrection_observer_limit hc hD (hn 0) hpos0).comp hpath
  have hχθ := (pointHolomorphicSecantCorrection_observer_limit hc hD (hn θ) hposθ).comp hpath
  have he : (fun ε : ℝ => pointHolomorphicExteriorRadialArgument H ε φ 0 ρ -
      pointHolomorphicExteriorRadialArgument H ε φ θ ρ) =
      (fun ε : ℝ => (pointExteriorRadialArgument ε φ 0 ρ - pointExteriorRadialArgument ε φ θ ρ) +
        (pointHolomorphicSecantCorrection H (pointRadialSectorPoint ρ 0) (pointRadialSectorPoint ε φ) -
          pointHolomorphicSecantCorrection H (pointRadialSectorPoint ρ θ) (pointRadialSectorPoint ε φ))) := by
    funext ε
    unfold pointHolomorphicExteriorRadialArgument
    ring
  rw [he]
  exact (pointExteriorTwoRayArgument_limit hρ hθ0 hθφ hφ2).add (hχ0.sub hχθ)

/-- The second, cutoff-shrinking limit removes exactly those chart endpoint
corrections, leaving minus the full actual sector angle. -/
theorem holomorphic_exterior_two_ray_cutoff_limit {H : ℂ → ℂ}
    (hH : DifferentiableAt ℂ H 0) (hD : deriv H 0 ≠ 0) (θ : ℝ) :
    Tendsto (fun ρ : ℝ => -θ +
      (pointHolomorphicSecantCorrection H (pointRadialSectorPoint ρ 0) 0 -
        pointHolomorphicSecantCorrection H (pointRadialSectorPoint ρ θ) 0))
      (𝓝[>] 0) (𝓝 (-θ)) := by
  have h := (tendsto_const_nhds (x := -θ)).add
    ((pointHolomorphicSecantCorrection_radial_limit hH hD 0).sub
      (pointHolomorphicSecantCorrection_radial_limit hH hD θ))
  simpa only [sub_self, add_zero] using h

end RepulsiveCoulomb
