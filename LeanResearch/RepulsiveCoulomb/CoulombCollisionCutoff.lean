module

public import LeanResearch.RepulsiveCoulomb.CoulombRelativeKernel
public import LeanResearch.RepulsiveCoulomb.CoulombCollisionGaussian
public import LeanResearch.RepulsiveCoulomb.PlanarPowerCutoffEnergy

@[expose] public section

/-! Smooth collision-tube cutoffs with the genuine full physical gradient. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

def coulombRelativeProjection (N : ℕ) : CoulombConfig (N + 2) →L[ℝ] ℂ :=
  (Real.sqrt 2)⁻¹ • (coulombCoordinate 0 - coulombCoordinate (Fin.succ 0))

theorem coulombRelativeProjection_apply (N : ℕ) (z : CoulombConfig (N + 2)) :
    coulombRelativeProjection N z = (Real.sqrt 2)⁻¹ • (z 0 - z (Fin.succ 0)) := rfl

theorem coulombRelativeProjection_insert {N : ℕ} (c u : ℂ) (y : CoulombConfig N) :
    coulombRelativeProjection N (coulombRelativeInsert c u y) = u := by
  rw [coulombRelativeProjection_apply, coulombRelative_pair_difference, smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.2 (by norm_num)).ne', one_smul]

theorem gradient_comp_coulombRelativeProjection {N : ℕ} {f : ℂ → ℝ}
    (z : CoulombConfig (N + 2)) (hf : DifferentiableAt ℝ f (coulombRelativeProjection N z)) :
    gradient (fun x => f (coulombRelativeProjection N x)) z =
      coulombRelativeInjection N (gradient f (coulombRelativeProjection N z)) := by
  have h := hf.hasFDerivAt.comp z (coulombRelativeProjection N).hasFDerivAt
  apply (toDual ℝ (CoulombConfig (N + 2))).injective
  simp only [toDual_gradient]
  change fderiv ℝ (f ∘ coulombRelativeProjection N) z = _
  rw [h.fderiv]
  ext v
  change fderiv ℝ f (coulombRelativeProjection N z) (coulombRelativeProjection N v) =
    inner ℝ (coulombRelativeInjection N (gradient f (coulombRelativeProjection N z))) v
  rw [← inner_gradient_left, real_inner_comm]
  calc
    _ = inner ℝ v (coulombRelativeInjection N (gradient f (coulombRelativeProjection N z))) :=
      (coulomb_inner_relative_injection v (gradient f (coulombRelativeProjection N z))).symm
    _ = _ := real_inner_comm _ _

def coulombFirstCollisionBump (N : ℕ) (ε : ℝ) (hε : 0 < ε) : CoulombConfig (N + 2) → ℝ :=
  fun z => pointCutoffBump 0 ε hε (coulombRelativeProjection N z)

theorem coulombFirstCollisionBump_contDiff (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (coulombFirstCollisionBump N ε hε) :=
  (pointCutoffBump 0 ε hε).contDiff.comp (coulombRelativeProjection N).contDiff

theorem coulombFirstCollisionBump_gradient (N : ℕ) (ε : ℝ) (hε : 0 < ε) (z : CoulombConfig (N + 2)) :
    gradient (coulombFirstCollisionBump N ε hε) z =
      coulombRelativeInjection N (gradient (pointCutoffBump 0 ε hε) (coulombRelativeProjection N z)) :=
  gradient_comp_coulombRelativeProjection z
    ((pointCutoffBump_contDiff 0 ε hε).differentiable (by simp) _)

theorem coulombFirstCollisionBump_gradient_norm (N : ℕ) (ε : ℝ) (hε : 0 < ε) (z : CoulombConfig (N + 2)) :
    ‖gradient (coulombFirstCollisionBump N ε hε) z‖ =
      ‖gradient (pointCutoffBump 0 ε hε) (coulombRelativeProjection N z)‖ := by
  rw [coulombFirstCollisionBump_gradient, coulombRelativeInjection_norm]

theorem coulombFirstCollisionBump_gradient_continuous (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Continuous (gradient (coulombFirstCollisionBump N ε hε)) := by
  have he : gradient (coulombFirstCollisionBump N ε hε) =
      fun z => coulombRelativeInjection N (gradient (pointCutoffBump 0 ε hε) (coulombRelativeProjection N z)) :=
    funext (fun z => coulombFirstCollisionBump_gradient N ε hε z)
  rw [he]
  exact (coulombRelativeInjection N).continuous.comp
    ((TauCeti.continuous_gradient_testFunction (pointCutoffTestFunction 0 ε hε)).comp
      (coulombRelativeProjection N).continuous)

theorem coulombFirstCollisionBump_energy_integrable (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun z => ‖gradient (coulombFirstCollisionBump N ε hε) z‖ ^ 2)
      (coulombMeasure (N + 2) β) := by
  let _ := coulombMeasure_isProbability (N := N + 2) hβ
  obtain ⟨B, hB, hb⟩ := exists_pointCutoffBump_gradient_bound
  have hm : MemLp (gradient (coulombFirstCollisionBump N ε hε)) 2 (coulombMeasure (N + 2) β) :=
    MemLp.of_bound (coulombFirstCollisionBump_gradient_continuous N ε hε).aestronglyMeasurable
      (B / ε) (Eventually.of_forall (fun z => by
        rw [coulombFirstCollisionBump_gradient_norm]
        exact hb 0 ε hε _))
  exact hm.norm.integrable_sq

theorem coulombFirstCollisionBump_energy_density_integral (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (ε : ℝ) (hε : 0 < ε) :
    (∫ z, ‖gradient (coulombFirstCollisionBump N ε hε) z‖ ^ 2 ∂coulombMeasure (N + 2) β) =
      ∫ z, coulombDensity (N + 2) β z * ‖gradient (coulombFirstCollisionBump N ε hε) z‖ ^ 2 := by
  rw [coulombMeasure_eq_withDensity hβ, integral_withDensity_eq_integral_toReal_smul
    (coulombDensity_continuous hβ.le).measurable.ennreal_ofReal (by simp)]
  congr 1
  funext z
  simp only [ENNReal.toReal_ofReal (coulombDensity_nonneg β z), smul_eq_mul]

end RepulsiveCoulomb

