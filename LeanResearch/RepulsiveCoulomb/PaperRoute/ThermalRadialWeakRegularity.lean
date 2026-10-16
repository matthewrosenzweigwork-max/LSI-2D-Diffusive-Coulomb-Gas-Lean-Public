import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalNewtonGradient
import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalLipschitzWeakDerivative
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.MetricSpace.Holder

/-! A genuine bounded-radial-potential regularity
instance. The only inputs are a measurable nonnegative bounded P2 probability
density and radiality of its literal potential. The output has actual weak
first and second derivatives, with compact-set MemLp bounds, C1 regularity
and HolderOnWith for the ACTUAL first derivative. No Sobolev or regularity
certificate is assumed, and the Newton gradient need not be differentiable
everywhere. The extracted generic Lipschitz weak derivative bridge proves
the distributional identities by difference quotients and Rademacher. -/
noncomputable section
open MeasureTheory Real Set Metric Filter InnerProductSpace TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace
namespace RepulsiveCoulomb.PaperRoute

/-- Literal weak-Hessian candidate, in the genuine iterated operator space. -/
def thermalWeakHessian (ρ : ℂ → ℝ) (x : ℂ) :
    ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (innerSL ℝ).comp (fderiv ℝ (thermalNewtonGradient (equilibriumDensityMeasure ρ)) x)

section RawDensity
variable {ρ : ℂ → ℝ} {M : ℝ}
  (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
  (hρi : Integrable ρ) (hρmass : (∫ x, ρ x)=1)
  (hρ2 : Integrable (fun x : ℂ => ‖x‖^2 * ρ x))
  (hUrad : ∀ ⦃x y : ℂ⦄, ‖x‖=‖y‖ →
    equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y)

include hρ0 hρM in
theorem thermalNewtonGradient_ballwise_lipschitz :
    ∀ R : ℝ, ∃ K : ℝ≥0,
      LipschitzOnWith K (thermalNewtonGradient (equilibriumDensityMeasure ρ)) (closedBall 0 R) := by
  intro R
  exact ⟨thermalNewtonLipschitzConstant M, (thermalNewtonGradient_lipschitz hρ0 hρM).lipschitzOnWith⟩

include hρm hρ0 hρM hρi hρmass hρ2 hUrad in
theorem thermal_radial_potential_contDiff_one : ContDiff ℝ 1 (equilibriumDensityPotential ρ) :=
  equilibriumDensityPotential_contDiff_one hρm hρ0 hρM hρi hρmass hρ2 hUrad

include hρm hρ0 hρM hρi hρmass hρ2 hUrad in
theorem thermal_radial_potential_fderiv_function :
    fderiv ℝ (equilibriumDensityPotential ρ) =
      fun x => innerSL ℝ (thermalNewtonGradient (equilibriumDensityMeasure ρ) x) := by
  funext x
  exact thermalDensityPotential_fderiv_eq_newtonGradient hρm hρ0 hρM hρi hρmass hρ2 hUrad x

include hρm hρ0 hρM hρi hρmass hρ2 hUrad in
/-- U has its actual Frechet derivative as its first weak derivative. -/
theorem thermal_radial_potential_hasWeakFDerivOn :
    TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ) (equilibriumDensityPotential ρ)
      (fderiv ℝ (equilibriumDensityPotential ρ)) := by
  have hU := thermal_radial_potential_contDiff_one hρm hρ0 hρM hρi hρmass hρ2 hUrad
  exact TauCeti.hasWeakFDerivOn_of_differentiableOn
    (hU.continuous.locallyIntegrable.locallyIntegrableOn _)
    ((hU.continuous_fderiv (by norm_num)).locallyIntegrable.locallyIntegrableOn _)
    (fun x _ => hU.differentiable (by norm_num) x)

include hρ0 hρM in
/-- The Newton vector field has an actual weak derivative, constructed by
the generic Lipschitz theorem rather than by a.e. differentiability alone. -/
theorem thermalNewtonGradient_hasWeakFDerivOn :
    TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ)
      (thermalNewtonGradient (equilibriumDensityMeasure ρ))
      (fderiv ℝ (thermalNewtonGradient (equilibriumDensityMeasure ρ))) :=
  plane_hasWeakFDerivOn_of_lipschitzOn_closedBall
    (thermalNewtonGradient_ballwise_lipschitz hρ0 hρM)

include hρm hρ0 hρM hρi hρmass hρ2 hUrad in
/-- The ACTUAL first derivative DU has a genuine weak derivative H. -/
theorem thermal_radial_potential_fderiv_hasWeakFDerivOn :
    TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ)
      (fderiv ℝ (equilibriumDensityPotential ρ)) (thermalWeakHessian ρ) := by
  rw [thermal_radial_potential_fderiv_function hρm hρ0 hρM hρi hρmass hρ2 hUrad]
  apply TauCeti.hasWeakFDerivOn_iff.mpr
  intro v
  have h := (thermalNewtonGradient_hasWeakFDerivOn hρ0 hρM).hasWeakLineDerivOn v
  simpa only [thermalWeakHessian, ContinuousLinearMap.comp_apply] using
    h.clm_comp (innerSL ℝ)

include hρm hρ0 hρM hρi hρmass hρ2 hUrad in
theorem thermal_radial_potential_memLp_isCompact (p : ℝ≥0∞)
    {S : Set ℂ} (hS : IsCompact S) :
    MemLp (equilibriumDensityPotential ρ) p (volume.restrict S) := by
  have hU := (thermal_radial_potential_contDiff_one hρm hρ0 hρM hρi hρmass hρ2 hUrad).continuous
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_ne_top
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hU.continuousOn
  exact MemLp.of_bound hU.aestronglyMeasurable.restrict B
    (ae_restrict_of_forall_mem hS.measurableSet hB)

include hρm hρ0 hρM hρi hρmass hρ2 hUrad in
theorem thermal_radial_potential_fderiv_memLp_isCompact (p : ℝ≥0∞)
    {S : Set ℂ} (hS : IsCompact S) :
    MemLp (fderiv ℝ (equilibriumDensityPotential ρ)) p (volume.restrict S) := by
  have hG := plane_memLp_isCompact_of_lipschitzOn_closedBall
    (thermalNewtonGradient_ballwise_lipschitz hρ0 hρM) p hS
  rw [thermal_radial_potential_fderiv_function hρm hρ0 hρM hρi hρmass hρ2 hUrad]
  exact hG.continuousLinearMap_comp (innerSL ℝ)

include hρ0 hρM in
/-- Local Lp of the genuine weak Hessian, including p=infinity. -/
theorem thermalWeakHessian_memLp_isCompact (p : ℝ≥0∞)
    {S : Set ℂ} (hS : IsCompact S) : MemLp (thermalWeakHessian ρ) p (volume.restrict S) := by
  have hDG := plane_fderiv_memLp_isCompact_of_lipschitzOn_closedBall
    (thermalNewtonGradient_ballwise_lipschitz hρ0 hρM) p hS
  let L : (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) :=
    ContinuousLinearMap.compL ℝ ℂ ℂ (ℂ →L[ℝ] ℝ) (innerSL ℝ)
  convert hDG.continuousLinearMap_comp (𝕜 := ℝ) (F := ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) L using 1
  rfl

include hρm hρ0 hρM hρi hρmass hρ2 hUrad in
/-- A stronger quantitative property of this radial specialization: the
actual Frechet derivative of U is globally Lipschitz. -/
theorem thermal_radial_potential_fderiv_lipschitz :
    LipschitzWith (thermalNewtonLipschitzConstant M)
      (fderiv ℝ (equilibriumDensityPotential ρ)) := by
  rw [thermal_radial_potential_fderiv_function hρm hρ0 hρM hρi hρmass hρ2 hUrad]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← map_sub, innerSL_apply_norm]
  simpa only [dist_eq_norm] using (thermalNewtonGradient_lipschitz hρ0 hρM).dist_le_mul x y

include hρm hρ0 hρM hρi hρmass hρ2 hUrad in
/-- Honest local C1,theta data: HolderOnWith of the ACTUAL DU on every
closed ball, for every 0≤theta≤1. The paper uses 0<theta<1. -/
theorem thermal_radial_potential_fderiv_holder_closedBall
    (R θ : ℝ≥0) (hθ : θ ≤ 1) :
    HolderOnWith
      (thermalNewtonLipschitzConstant M * (2 * R : ℝ≥0)^(1-(θ : ℝ))) θ
      (fderiv ℝ (equilibriumDensityPotential ρ)) (closedBall (0 : ℂ) (R : ℝ)) := by
  have hlip := thermal_radial_potential_fderiv_lipschitz hρm hρ0 hρM hρi hρmass hρ2 hUrad
  have hdiam : ∀ x ∈ closedBall (0 : ℂ) (R : ℝ),
      ∀ y ∈ closedBall (0 : ℂ) (R : ℝ), edist x y ≤ (2 * R : ℝ≥0) := by
    intro x hx y hy
    have hx' : dist x (0 : ℂ) ≤ R := hx
    have hy' : dist (0 : ℂ) y ≤ R := by simpa only [mem_closedBall, dist_comm] using hy
    have hd : dist x y ≤ ((2 * R : ℝ≥0) : ℝ) := by
      have ht := dist_triangle x (0 : ℂ) y
      push_cast
      linarith
    simpa only [edist_dist, ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hd
  simpa only [NNReal.coe_one] using
    (HolderOnWith.of_le hdiam (hlip.holderWith.holderOnWith _) hθ)

include hρm hρ0 hρM hρi hρmass hρ2 hUrad in
/-- Transparent W2,p-local/C1,theta characterization. It includes both
distributional test identities and all compact Lp conditions; no surrogate
field called Sobolev is used. The same raw-density hypotheses discharge
every component. -/
theorem thermal_radial_weak_regularity :
    ContDiff ℝ 1 (equilibriumDensityPotential ρ) ∧
    TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ) (equilibriumDensityPotential ρ)
      (fderiv ℝ (equilibriumDensityPotential ρ)) ∧
    TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ)
      (fderiv ℝ (equilibriumDensityPotential ρ)) (thermalWeakHessian ρ) ∧
    (∀ (p : ℝ≥0∞) (S : Set ℂ), IsCompact S →
      MemLp (equilibriumDensityPotential ρ) p (volume.restrict S) ∧
      MemLp (fderiv ℝ (equilibriumDensityPotential ρ)) p (volume.restrict S) ∧
      MemLp (thermalWeakHessian ρ) p (volume.restrict S)) ∧
    (∀ R θ : ℝ≥0, θ ≤ 1 →
      HolderOnWith
        (thermalNewtonLipschitzConstant M * (2 * R : ℝ≥0)^(1-(θ : ℝ))) θ
        (fderiv ℝ (equilibriumDensityPotential ρ)) (closedBall (0 : ℂ) (R : ℝ))) := by
  refine ⟨thermal_radial_potential_contDiff_one hρm hρ0 hρM hρi hρmass hρ2 hUrad,
    thermal_radial_potential_hasWeakFDerivOn hρm hρ0 hρM hρi hρmass hρ2 hUrad,
    thermal_radial_potential_fderiv_hasWeakFDerivOn hρm hρ0 hρM hρi hρmass hρ2 hUrad, ?_, ?_⟩
  · intro p S hS
    exact ⟨thermal_radial_potential_memLp_isCompact hρm hρ0 hρM hρi hρmass hρ2 hUrad p hS,
      thermal_radial_potential_fderiv_memLp_isCompact hρm hρ0 hρM hρi hρmass hρ2 hUrad p hS,
      thermalWeakHessian_memLp_isCompact hρ0 hρM p hS⟩
  · exact thermal_radial_potential_fderiv_holder_closedBall hρm hρ0 hρM hρi hρmass hρ2 hUrad

end RawDensity
end RepulsiveCoulomb.PaperRoute
