import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCoreCoordinates
import Mathlib.MeasureTheory.Function.L2Space

/-! The actual inverse metric square root is a bounded complex-linear
self-adjoint contraction on the original fixed-fiber weighted vector L2.
Its pointwise inverse may be unbounded; no bounded inverse is asserted. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulombInverseRoot_memLp {N : ℕ} (β : ℝ)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    MemLp (fun z => dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (g z))
      2 (coulombMeasure N β) := by
  apply memLp_piLp_iff.mpr
  intro i
  have he : (fun z => dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (g z) i) =
      fun z => ∑ j, coulombInverseRootMatrix z i j * g z j :=
    funext (fun z => dbarCLMMatrix_apply _ _ i)
  rw [he]
  exact memLp_finsetSum Finset.univ (fun j _ =>
    (coulombInverseRootMatrix_entry_memLp_top β i j).fun_mul ((Lp.memLp g).eval_piLp j))

def coulombInverseRootL2 {N : ℕ} (β : ℝ)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (coulombInverseRoot_memLp β g).toLp
    (fun z => dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (g z))

theorem coulombInverseRootL2_coe {N : ℕ} (β : ℝ)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    coulombInverseRootL2 β g =ᵐ[coulombMeasure N β]
      fun z => dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (g z) :=
  MemLp.coeFn_toLp _

theorem coulombInverseRootL2_norm_le {N : ℕ} (β : ℝ)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) : ‖coulombInverseRootL2 β g‖ ≤ ‖g‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coulombInverseRootL2_coe β g] with z hz
  rw [hz]
  exact dbarCovectorMetricInverseRoot_contraction (coulombReciprocalDerivative z) (g z)

def coulombInverseRootL2Linear (N : ℕ) (β : ℝ) :
    Lp (CoulombConfig N) 2 (coulombMeasure N β) →ₗ[ℂ]
      Lp (CoulombConfig N) 2 (coulombMeasure N β) where
  toFun := coulombInverseRootL2 β
  map_add' := by
    intro f g
    apply Lp.ext
    filter_upwards [coulombInverseRootL2_coe β (f + g), coulombInverseRootL2_coe β f,
      coulombInverseRootL2_coe β g, Lp.coeFn_add f g,
      Lp.coeFn_add (coulombInverseRootL2 β f) (coulombInverseRootL2 β g)] with z hs hf hg hfg hR
    rw [hs, hR, Pi.add_apply, hf, hg, hfg, Pi.add_apply, map_add]
  map_smul' := by
    intro c f
    change coulombInverseRootL2 β (c • f) = c • coulombInverseRootL2 β f
    apply Lp.ext
    filter_upwards [coulombInverseRootL2_coe β (c • f), coulombInverseRootL2_coe β f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (coulombInverseRootL2 β f)] with z hs hf hcf hR
    rw [hs, hR, Pi.smul_apply, hf, hcf, Pi.smul_apply, map_smul]

def coulombInverseRootL2L (N : ℕ) (β : ℝ) :
    Lp (CoulombConfig N) 2 (coulombMeasure N β) →L[ℂ]
      Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (coulombInverseRootL2Linear N β).mkContinuous 1 (by
    intro g
    change ‖coulombInverseRootL2 β g‖ ≤ 1 * ‖g‖
    simpa only [one_mul] using coulombInverseRootL2_norm_le β g)

theorem coulombInverseRootL2L_selfAdjoint_pairing {N : ℕ} (β : ℝ)
    (f g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    inner ℂ (coulombInverseRootL2L N β f) g = inner ℂ f (coulombInverseRootL2L N β g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coulombInverseRootL2_coe β f, coulombInverseRootL2_coe β g] with z hf hg
  change inner ℂ (coulombInverseRootL2 β f z) (g z) = inner ℂ (f z) (coulombInverseRootL2 β g z)
  rw [hf, hg]
  exact dbarGraphMetricInverseRoot_selfAdjoint_pairing _ _ _

theorem coulombInverseRootL2L_injective (N : ℕ) (β : ℝ) :
    Function.Injective (coulombInverseRootL2L N β) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro f hf
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  have hz : (coulombInverseRootL2L N β f : CoulombConfig N → CoulombConfig N) =ᵐ[coulombMeasure N β] 0 :=
    Lp.eq_zero_iff_ae_eq_zero.mp hf
  filter_upwards [coulombInverseRootL2_coe β f, hz] with z hR hzero
  have hpoint : dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (f z) = 0 :=
    hR.symm.trans hzero
  have hi := congrArg (fun L : CoulombConfig N →L[ℂ] CoulombConfig N => L (f z))
    (dbarGraphMetricRoot_inverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)))
  change f z = 0
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hpoint, map_zero] using hi.symm

end RepulsiveCoulomb
