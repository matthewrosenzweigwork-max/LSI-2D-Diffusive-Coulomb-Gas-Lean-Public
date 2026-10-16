import LeanResearch.RepulsiveCoulomb.PointChosenRadialMetricTransition
import LeanResearch.RepulsiveCoulomb.PointFiniteCornerChosenRotation
import LeanResearch.RepulsiveCoulomb.PointMetricLineNormalizedChart
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Uncompiled records-only successor. An original-germ normalized corner
chart receives an actual classical-cone metric chart by the explicit radial
power map, preserving its outgoing ray and full initial interval. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem coneRadialEquiv_unit_rotation {α : ℝ} (hα : 0 ≤ α)
    {q : ℂ} (hq : ‖q‖ = 1) (z : ℂ) :
    coneRadialEquiv α hα (q * z) = q * coneRadialEquiv α hα z := by
  change (α + 1)⁻¹ • (‖q * z‖ ^ (α + 1 - 1) • (q * z)) =
    q * ((α + 1)⁻¹ • (‖z‖ ^ (α + 1 - 1) • z))
  simp only [norm_mul, hq, one_mul, Complex.real_smul]
  ring

/-- This transition is constructed for the SAME normalized original-germ
chart, rather than comparing it with an unrelated existential metric chart. -/
theorem exists_pointCorner_physical_metric_transition
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {p : ℂ} (E : OpenPartialHomeomorph ℂ ℂ)
    {q : ℂ} (hq : ‖q‖ = 1)
    (hsource : E.source = (pointChosenSmoothRadialChart ha y p).source)
    (hE : ∀ z, E z = q * pointChosenSmoothRadialChart ha y p z) :
    ∃ F : OpenPartialHomeomorph ℂ ℂ, p ∈ F.source ∧ F p = 0 ∧ F.source ⊆ E.source ∧
      (∀ z, F z = coneRadialEquiv (coalescedPointExponent a y p / 2)
        (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)) (E z)) ∧
      (∀ u ∈ F.source, ∀ v ∈ F.source,
        (pointSmoothConformalEDist a y u v).toReal = pointClassicalConeDist a y p (F u) (F v)) ∧
      (∀ z ∈ F.target,
        (coneRadialEquiv (coalescedPointExponent a y p / 2)
          (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num))).symm z ∈ E.target ∧
        F.symm z = E.symm ((coneRadialEquiv (coalescedPointExponent a y p / 2)
          (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num))).symm z)) := by
  let α := coalescedPointExponent a y p / 2
  have hα : 0 ≤ α := div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)
  have hq0 : q ≠ 0 := norm_ne_zero_iff.mp (by rw [hq]; norm_num)
  obtain ⟨F₀, hp, hp0, hF₀, hmetric, hFsrc⟩ := exists_pointChosen_classical_metric_transition ha y p
  let F := pointRotatedRadialChart F₀ q hq0
  have hsrc : F.source = F₀.source := pointRotatedRadialChart_source F₀ q hq0
  have hF (z : ℂ) : F z = coneRadialEquiv α hα (E z) := by
    rw [pointRotatedRadialChart_apply, hF₀, hE, coneRadialEquiv_unit_rotation hα hq]
  have hsub : F.source ⊆ E.source := by
    rw [hsrc, hsource]
    exact hFsrc
  refine ⟨F, by rwa [hsrc], ?_, hsub, hF, ?_, ?_⟩
  · rw [pointRotatedRadialChart_apply, hp0, mul_zero]
  · intro u hu v hv
    rw [hsrc] at hu hv
    rw [pointRotatedRadialChart_apply, pointRotatedRadialChart_apply,
      pointClassicalConeDist_rotation a y p hq]
    exact hmetric u hu v hv
  · intro z hz
    have hzin : F.symm z ∈ F.source := F.symm.mapsTo hz
    have hEz : E (F.symm z) = (coneRadialEquiv α hα).symm z := by
      apply (coneRadialEquiv α hα).injective
      rw [← hF, F.right_inv hz, Equiv.apply_symm_apply]
    have ht : (coneRadialEquiv α hα).symm z ∈ E.target := hEz ▸ E.mapsTo (hsub hzin)
    exact ⟨ht, by rw [← hEz, E.left_inv (hsub hzin)]⟩

end RepulsiveCoulomb
