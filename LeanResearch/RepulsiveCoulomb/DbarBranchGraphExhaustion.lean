import LeanResearch.RepulsiveCoulomb.DbarBranchGraphMetricNorms
import LeanResearch.RepulsiveCoulomb.CoulombExhaustionCompact
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The actual holomorphic graph and the square-root exhaustion have the
pointwise derivative bound required for proper metric cutoffs. The graph target
is the Hilbert product WithLp 2, not the ordinary product with its maximum norm. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
namespace RepulsiveCoulomb

abbrev CoulombHolomorphicGraphSpace (N : ℕ) := WithLp 2 (CoulombConfig N × ℂ)

def coulombHolomorphicGraph {N : ℕ} (z : CoulombConfig N) : CoulombHolomorphicGraphSpace N :=
  WithLp.toLp 2 (z, (coulombVandermonde z)⁻¹)

def coulombHolomorphicGraphDerivative {N : ℕ} (z : CoulombConfig N) :
    CoulombConfig N →L[ℂ] CoulombHolomorphicGraphSpace N :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (CoulombConfig N) ℂ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℂ (CoulombConfig N)).prod (coulombReciprocalDerivative z))

theorem coulombHolomorphicGraph_hasFDerivAt {N : ℕ} {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    HasFDerivAt (coulombHolomorphicGraph (N := N)) (coulombHolomorphicGraphDerivative z) z :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (CoulombConfig N) ℂ).symm.hasFDerivAt.comp z
    ((hasFDerivAt_id z).prodMk (coulombReciprocal_hasFDerivAt hz))

theorem coulombHolomorphicGraph_norm_sq {N : ℕ} (z : CoulombConfig N) :
    ‖coulombHolomorphicGraph z‖ ^ 2 = coulombExhaustion z := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rfl

theorem coulombHolomorphicGraphDerivative_norm_sq {N : ℕ} (z v : CoulombConfig N) :
    ‖coulombHolomorphicGraphDerivative z v‖ ^ 2 =
      (inner ℂ v (coulombReciprocalGraphMetric z v)).re := by
  rw [coulombReciprocalGraphMetric_quadratic, WithLp.prod_norm_sq_eq_of_L2]
  rfl

def coulombGraphRadius {N : ℕ} (z : CoulombConfig N) : ℝ := Real.sqrt (1 + ‖coulombHolomorphicGraph z‖ ^ 2)

theorem coulombGraphRadius_eq {N : ℕ} (z : CoulombConfig N) :
    coulombGraphRadius z = Real.sqrt (1 + coulombExhaustion z) := by
  rw [coulombGraphRadius, coulombHolomorphicGraph_norm_sq]

theorem coulombGraphRadius_pos {N : ℕ} (z : CoulombConfig N) : 0 < coulombGraphRadius z :=
  Real.sqrt_pos.mpr (by positivity)

theorem coulombHolomorphicGraph_norm_le_radius {N : ℕ} (z : CoulombConfig N) :
    ‖coulombHolomorphicGraph z‖ ≤ coulombGraphRadius z := by
  have hs : (coulombGraphRadius z) ^ 2 = 1 + ‖coulombHolomorphicGraph z‖ ^ 2 :=
    Real.sq_sqrt (by positivity)
  nlinarith [coulombGraphRadius_pos z, norm_nonneg (coulombHolomorphicGraph z)]

theorem coulombGraphRadius_fderiv_apply {N : ℕ} {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) (v : CoulombConfig N) :
    fderiv ℝ (coulombGraphRadius (N := N)) z v =
      inner ℝ (coulombHolomorphicGraph z) (coulombHolomorphicGraphDerivative z v) / coulombGraphRadius z := by
  have hd := (coulombHolomorphicGraph_hasFDerivAt hz).restrictScalars ℝ
  have he := (hasFDerivAt_const (1 : ℝ) z).add hd.norm_sq
  have hr := he.sqrt (by positivity : (1 : ℝ) + ‖coulombHolomorphicGraph z‖ ^ 2 ≠ 0)
  have hf := hr.fderiv
  change fderiv ℝ (coulombGraphRadius (N := N)) z = _ at hf
  rw [hf]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.zero_apply, zero_add, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat, Pi.add_apply]
  change (1 / (2 * coulombGraphRadius z)) * (2 * inner ℝ (coulombHolomorphicGraph z)
    (coulombHolomorphicGraphDerivative z v)) = _
  field_simp [(coulombGraphRadius_pos z).ne'] <;> ring

theorem coulombGraphRadius_directional_bound {N : ℕ} {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) (v : CoulombConfig N) :
    |fderiv ℝ (coulombGraphRadius (N := N)) z v| ≤ ‖coulombHolomorphicGraphDerivative z v‖ := by
  rw [coulombGraphRadius_fderiv_apply hz v, abs_div, abs_of_pos (coulombGraphRadius_pos z)]
  apply (div_le_iff₀ (coulombGraphRadius_pos z)).mpr
  calc
    _ ≤ ‖coulombHolomorphicGraph z‖ * ‖coulombHolomorphicGraphDerivative z v‖ := abs_real_inner_le_norm _ _
    _ ≤ coulombGraphRadius z * ‖coulombHolomorphicGraphDerivative z v‖ :=
      mul_le_mul_of_nonneg_right (coulombHolomorphicGraph_norm_le_radius z) (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem coulombGraphRadius_metric_dual_bound {N : ℕ} {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    ‖(fderiv ℝ (coulombGraphRadius (N := N)) z).comp
      ((dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))).restrictScalars ℝ)‖ ≤ 1 := by
  let a : CoulombConfig N := dbarCovectorRiesz (coulombReciprocalDerivative z)
  let B : CoulombConfig N →L[ℝ] CoulombConfig N :=
    (dbarGraphMetricInverseRoot a).restrictScalars ℝ
  let L : CoulombConfig N →L[ℝ] ℝ :=
    (fderiv ℝ (coulombGraphRadius (N := N)) z).comp B
  change ‖L‖ ≤ 1
  refine L.opNorm_le_bound (by norm_num) ?_
  intro v
  have hnorm (w : CoulombConfig N) :
      ‖coulombHolomorphicGraphDerivative z w‖ = ‖dbarGraphMetricRoot a w‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [coulombHolomorphicGraphDerivative_norm_sq, dbarGraphMetricRoot_norm_sq,
      ← dbarCovectorMetric_eq_rankOne]
    rfl
  have hSR := congrArg (fun L : CoulombConfig N →L[ℂ] CoulombConfig N => L v)
    (dbarGraphMetricRoot_inverseRoot a)
  change dbarGraphMetricRoot a (dbarGraphMetricInverseRoot a v) = v at hSR
  have hb := coulombGraphRadius_directional_bound hz (dbarGraphMetricInverseRoot a v)
  rw [hnorm, hSR] at hb
  simpa only [L, B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', Real.norm_eq_abs,
    one_mul] using hb

end RepulsiveCoulomb
