import LeanResearch.RepulsiveCoulomb.PointGeodesicMacroPhase
import LeanResearch.RepulsiveCoulomb.PointRegularArcPointArgument
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Actual weighted point-argument transport on a complete regular C1
geodesic macro-arc. Continuous point-argument lifts, including at a boundary
puncture endpoint, are constructed; their weighted increment is the negative
of the actual tangent increment. This is the smooth-edge part of Gauss–Bonnet,
not an assumed global flux or boundary-atom identity. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

/-- The local tangent and literal logarithmic connection identities assemble
on a closed arc by the real mean-value theorem, including endpoint limits. -/
theorem pointConformal_equal_image_argument_turn_eq
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
    {θ : ℝ → ℝ} (hθ : ContinuousOn θ (Icc (0 : ℝ) 1))
    (hθlift : ∀ u ∈ Ioo (0 : ℝ) 1, Complex.exp ((θ u : ℂ) * Complex.I) =
      deriv η u / (‖deriv η u‖ : ℂ))
    (ψ : Fin m → ℝ → ℝ) (hψ : ∀ j, ContinuousOn (ψ j) (Icc (0 : ℝ) 1))
    (hψlift : ∀ j, a j ≠ 0 → ∀ u ∈ Ioo (0 : ℝ) 1,
      Complex.exp ((ψ j u : ℂ) * Complex.I) = (η u - y j) / (‖η u - y j‖ : ℂ)) :
    θ 1 - θ 0 = -(∑ j, (a j / 2) * (ψ j 1 - ψ j 0)) := by
  let F : ℝ → ℝ := fun u => θ u + ∑ j, (a j / 2) * ψ j u
  have hF : ContinuousOn F (Icc (0 : ℝ) 1) := by
    apply hθ.add
    exact continuousOn_finsetSum _ (fun j _ => continuousOn_const.mul (hψ j))
  have hFD (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : HasDerivAt F 0 u := by
    have hucc : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
    have huN : Icc (0 : ℝ) 1 ∈ 𝓝 u :=
      mem_of_superset (Ioo_mem_nhds hu.1 hu.2) Ioo_subset_Icc_self
    have hθD := pointConformal_equal_image_tangent_angle_hasDerivAt
      ha y hxz γ h0 hd s t hst hη hi hreg hη0 hη1 himage havoid hu
      ((hθ u hucc).continuousAt huN)
      (by filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv; exact hθlift v hv)
    have hψD := hasDerivAt_point_weighted_argument ha y
      (hη.differentiable (by norm_num) u) (havoid u hu) ψ
      (fun j => (hψ j u hucc).continuousAt huN)
      (by
        intro j hj
        filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
        exact hψlift j hj v hv)
    convert! hθD.add hψD using 1 <;> simp [F]
  obtain ⟨u, hu, hzero⟩ := exists_hasDerivAt_eq_slope F (fun _ => 0)
    (show (0 : ℝ) < 1 by norm_num) hF hFD
  have hsum : (∑ j, (a j / 2) * (ψ j 1 - ψ j 0)) =
      (∑ j, (a j / 2) * ψ j 1) - ∑ j, (a j / 2) * ψ j 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  dsimp [F] at hzero
  norm_num at hzero
  rw [hsum]
  linarith

/-- Both tangent and point-angle lifts are constructed from the actual C1
representative. Nominal zero-weight locations need no avoidance condition. -/
theorem exists_pointConformal_equal_image_argument_turn
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
    (havoid : ∀ v ∈ Ioo (0 : ℝ) 1, η v ∉ pointPunctures a y) :
    ∃ θ : Icc (0 : ℝ) 1 → ℝ, ∃ ψ : Fin m → Icc (0 : ℝ) 1 → ℝ,
      Continuous θ ∧ (∀ j, Continuous (ψ j)) ∧
      (∀ u, Complex.exp ((θ u : ℂ) * Complex.I) = deriv η u / (‖deriv η u‖ : ℂ)) ∧
      (∀ j, a j ≠ 0 → ∀ u : Icc (0 : ℝ) 1, u.1 ∈ Ioo (0 : ℝ) 1 →
        Complex.exp ((ψ j u : ℂ) * Complex.I) = (η u - y j) / (‖η u - y j‖ : ℂ)) ∧
      θ 1 - θ 0 = -(∑ j, (a j / 2) * (ψ j 1 - ψ j 0)) := by
  classical
  obtain ⟨θ, hθ, hθlift⟩ := exists_regular_edge_tangent_angle_lift hη hreg
  have hψex (j : Fin m) : ∃ ψ : Icc (0 : ℝ) 1 → ℝ, Continuous ψ ∧
      (a j ≠ 0 → ∀ u : Icc (0 : ℝ) 1, u.1 ∈ Ioo (0 : ℝ) 1 →
        Complex.exp ((ψ u : ℂ) * Complex.I) = (η u - y j) / (‖η u - y j‖ : ℂ)) := by
    by_cases haj : a j = 0
    · exact ⟨fun _ => 0, continuous_const, fun h => False.elim (h haj)⟩
    have hp (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : η u ≠ y j := by
      intro heq
      exact havoid u hu ⟨j, lt_of_le_of_ne (ha j) (Ne.symm haj), heq⟩
    obtain ⟨ψ, hψ, _, hlift⟩ := exists_regular_arc_point_argument_lift hη hi hreg (y j) hp
    exact ⟨ψ, hψ, fun _ => hlift⟩
  choose ψ hψ hψlift using hψex
  let Θ : ℝ → ℝ := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) θ
  let Ψ : Fin m → ℝ → ℝ := fun j => IccExtend (show (0 : ℝ) ≤ 1 by norm_num) (ψ j)
  have hΘ : Continuous Θ := continuous_IccExtend_iff.mpr hθ
  have hΨ (j : Fin m) : Continuous (Ψ j) := continuous_IccExtend_iff.mpr (hψ j)
  have hΘlift (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      Complex.exp ((Θ u : ℂ) * Complex.I) = deriv η u / (‖deriv η u‖ : ℂ) := by
    dsimp [Θ]
    rw [IccExtend_of_mem _ _ ⟨hu.1.le, hu.2.le⟩]
    exact hθlift ⟨u, ⟨hu.1.le, hu.2.le⟩⟩
  have hΨlift (j : Fin m) (hj : a j ≠ 0) (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      Complex.exp ((Ψ j u : ℂ) * Complex.I) = (η u - y j) / (‖η u - y j‖ : ℂ) := by
    dsimp [Ψ]
    rw [IccExtend_of_mem _ _ ⟨hu.1.le, hu.2.le⟩]
    exact hψlift j hj ⟨u, ⟨hu.1.le, hu.2.le⟩⟩ hu
  have hturn := pointConformal_equal_image_argument_turn_eq ha y hxz γ h0 hd s t hst
    hη hi hreg hη0 hη1 himage havoid hΘ.continuousOn hΘlift Ψ
    (fun j => (hΨ j).continuousOn) hΨlift
  refine ⟨θ, ψ, hθ, hψ, hθlift, hψlift, ?_⟩
  simpa [Θ, Ψ, IccExtend] using hturn

end RepulsiveCoulomb
