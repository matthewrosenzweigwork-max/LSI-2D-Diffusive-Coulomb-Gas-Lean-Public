module

public import LeanResearch.RepulsiveCoulomb.DbarBranchGraphMetricAlgebra
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! Explicit square-root factors for the rank-one graph metric. These are
pointwise algebraic identities only; variable-coefficient L2 domains and their
joint graph approximation remain separate obligations. -/
noncomputable section
open InnerProductSpace
open scoped ComplexConjugate
namespace RepulsiveCoulomb

def dbarRankOnePerturbation {N : ℕ} (a : CoulombConfig N) (c : ℂ) :
    CoulombConfig N →L[ℂ] CoulombConfig N :=
  ContinuousLinearMap.id ℂ _ + c • rankOne ℂ a a

theorem dbarRankOnePerturbation_apply {N : ℕ} (a z : CoulombConfig N) (c : ℂ) :
    dbarRankOnePerturbation a c z = z + (c * inner ℂ a z) • a := by
  simp only [dbarRankOnePerturbation, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, rankOne_apply, smul_smul]

theorem dbarRankOnePerturbation_comp {N : ℕ} (a : CoulombConfig N) (c d : ℂ) :
    (dbarRankOnePerturbation a c).comp (dbarRankOnePerturbation a d) =
      dbarRankOnePerturbation a (c + d + c * d * inner ℂ a a) := by
  ext z
  simp only [ContinuousLinearMap.comp_apply, dbarRankOnePerturbation_apply,
    inner_add_right, inner_smul_right]
  rw [add_assoc, ← add_smul]
  have hc : d * inner ℂ a z + c * (inner ℂ a z + d * inner ℂ a z * inner ℂ a a) =
      (c + d + c * d * inner ℂ a a) * inner ℂ a z := by ring
  rw [hc]

theorem dbarRankOnePerturbation_zero {N : ℕ} (a : CoulombConfig N) :
    dbarRankOnePerturbation a 0 = ContinuousLinearMap.id ℂ _ := by
  simp [dbarRankOnePerturbation]

theorem dbarRankOnePerturbation_one {N : ℕ} (a : CoulombConfig N) :
    dbarRankOnePerturbation a 1 = dbarGraphMetric a := by
  simp [dbarRankOnePerturbation, dbarGraphMetric]

def dbarGraphMetricRootScalar {N : ℕ} (a : CoulombConfig N) : ℝ := Real.sqrt (1 + ‖a‖ ^ 2)

theorem dbarGraphMetricRootScalar_pos {N : ℕ} (a : CoulombConfig N) :
    0 < dbarGraphMetricRootScalar a := Real.sqrt_pos.mpr (by positivity)

theorem dbarGraphMetricRootScalar_sq {N : ℕ} (a : CoulombConfig N) :
    (dbarGraphMetricRootScalar a) ^ 2 = 1 + ‖a‖ ^ 2 := Real.sq_sqrt (by positivity)

def dbarGraphMetricRoot {N : ℕ} (a : CoulombConfig N) : CoulombConfig N →L[ℂ] CoulombConfig N :=
  dbarRankOnePerturbation a (((1 + dbarGraphMetricRootScalar a)⁻¹ : ℝ) : ℂ)

def dbarGraphMetricInverseRoot {N : ℕ} (a : CoulombConfig N) : CoulombConfig N →L[ℂ] CoulombConfig N :=
  dbarRankOnePerturbation a (-(((dbarGraphMetricRootScalar a * (1 + dbarGraphMetricRootScalar a))⁻¹ : ℝ) : ℂ))

theorem dbarGraphMetricRoot_square {N : ℕ} (a : CoulombConfig N) :
    (dbarGraphMetricRoot a).comp (dbarGraphMetricRoot a) = dbarGraphMetric a := by
  let t := dbarGraphMetricRootScalar a
  have ht : 0 < t := dbarGraphMetricRootScalar_pos a
  have ht1 : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have ht2 : t ^ 2 = 1 + ‖a‖ ^ 2 := dbarGraphMetricRootScalar_sq a
  have hc : (1 + t)⁻¹ + (1 + t)⁻¹ + (1 + t)⁻¹ * (1 + t)⁻¹ * ‖a‖ ^ 2 = 1 := by
    field_simp [ht1]
    nlinarith [ht2]
  rw [dbarGraphMetricRoot, dbarRankOnePerturbation_comp, ← dbarRankOnePerturbation_one a]
  congr 1
  have hi : inner ℂ a a = (‖a‖ ^ 2 : ℝ) := by
    apply Complex.ext
    · exact inner_self_eq_norm_sq (𝕜 := ℂ) a
    · exact inner_self_im (𝕜 := ℂ) a
  rw [hi]
  simpa only [t, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_inv, Complex.ofReal_one] using congrArg Complex.ofReal hc

theorem dbarGraphMetricRoot_inverseRoot {N : ℕ} (a : CoulombConfig N) :
    (dbarGraphMetricRoot a).comp (dbarGraphMetricInverseRoot a) = ContinuousLinearMap.id ℂ _ := by
  let t := dbarGraphMetricRootScalar a
  have ht : 0 < t := dbarGraphMetricRootScalar_pos a
  have ht1 : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have ht2 : t ^ 2 = 1 + ‖a‖ ^ 2 := dbarGraphMetricRootScalar_sq a
  have hc : (1 + t)⁻¹ - (t * (1 + t))⁻¹ -
      (1 + t)⁻¹ * (t * (1 + t))⁻¹ * ‖a‖ ^ 2 = 0 := by
    field_simp [ht.ne', ht1]
    nlinarith [ht2]
  rw [dbarGraphMetricRoot, dbarGraphMetricInverseRoot, dbarRankOnePerturbation_comp,
    ← dbarRankOnePerturbation_zero a]
  congr 1
  have hi : inner ℂ a a = (‖a‖ ^ 2 : ℝ) := by
    apply Complex.ext
    · exact inner_self_eq_norm_sq (𝕜 := ℂ) a
    · exact inner_self_im (𝕜 := ℂ) a
  rw [hi]
  simpa only [t, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_one, Complex.ofReal_zero,
    Complex.ofReal_neg, sub_eq_add_neg, mul_neg, neg_mul] using congrArg Complex.ofReal hc

theorem dbarGraphMetricInverseRoot_root {N : ℕ} (a : CoulombConfig N) :
    (dbarGraphMetricInverseRoot a).comp (dbarGraphMetricRoot a) = ContinuousLinearMap.id ℂ _ := by
  have he : (dbarGraphMetricInverseRoot a).comp (dbarGraphMetricRoot a) =
      (dbarGraphMetricRoot a).comp (dbarGraphMetricInverseRoot a) := by
    rw [dbarGraphMetricRoot, dbarGraphMetricInverseRoot, dbarRankOnePerturbation_comp,
      dbarRankOnePerturbation_comp]
    congr 1
    ring
  exact he.trans (dbarGraphMetricRoot_inverseRoot a)

theorem dbarGraphMetricInverseRoot_square {N : ℕ} (a : CoulombConfig N) :
    (dbarGraphMetricInverseRoot a).comp (dbarGraphMetricInverseRoot a) = dbarGraphMetricInverse a := by
  apply ContinuousLinearMap.ext
  intro z
  have hS : ∀ v, dbarGraphMetricRoot a (dbarGraphMetricRoot a v) = dbarGraphMetric a v :=
    fun v => congrArg (fun L : CoulombConfig N →L[ℂ] CoulombConfig N => L v) (dbarGraphMetricRoot_square a)
  have hSR : ∀ v, dbarGraphMetricRoot a (dbarGraphMetricInverseRoot a v) = v :=
    fun v => congrArg (fun L : CoulombConfig N →L[ℂ] CoulombConfig N => L v) (dbarGraphMetricRoot_inverseRoot a)
  change dbarGraphMetricInverseRoot a (dbarGraphMetricInverseRoot a z) = dbarGraphMetricInverse a z
  calc
    _ = dbarGraphMetricInverse a (dbarGraphMetric a
        (dbarGraphMetricInverseRoot a (dbarGraphMetricInverseRoot a z))) :=
      (dbarGraphMetric_left_inverse a _).symm
    _ = _ := by rw [← hS, hSR, hSR]


theorem dbarRankOnePerturbation_real_selfAdjoint {N : ℕ} (a u v : CoulombConfig N) (c : ℝ) :
    inner ℂ (dbarRankOnePerturbation a c u) v = inner ℂ u (dbarRankOnePerturbation a c v) := by
  simp only [dbarRankOnePerturbation_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, map_mul, Complex.conj_ofReal, inner_conj_symm]
  ring

theorem dbarGraphMetricRoot_selfAdjoint_pairing {N : ℕ} (a u v : CoulombConfig N) :
    inner ℂ (dbarGraphMetricRoot a u) v = inner ℂ u (dbarGraphMetricRoot a v) :=
  dbarRankOnePerturbation_real_selfAdjoint a u v _

theorem dbarGraphMetricInverseRoot_selfAdjoint_pairing {N : ℕ} (a u v : CoulombConfig N) :
    inner ℂ (dbarGraphMetricInverseRoot a u) v = inner ℂ u (dbarGraphMetricInverseRoot a v) := by
  simpa only [dbarGraphMetricInverseRoot, Complex.ofReal_neg] using
    dbarRankOnePerturbation_real_selfAdjoint a u v
      (-(dbarGraphMetricRootScalar a * (1 + dbarGraphMetricRootScalar a))⁻¹)

theorem dbarGraphMetricRoot_norm_sq {N : ℕ} (a g : CoulombConfig N) :
    ‖dbarGraphMetricRoot a g‖ ^ 2 = (inner ℂ g (dbarGraphMetric a g)).re := by
  have hs := congrArg (fun L : CoulombConfig N →L[ℂ] CoulombConfig N => L g)
    (dbarGraphMetricRoot_square a)
  change dbarGraphMetricRoot a (dbarGraphMetricRoot a g) = dbarGraphMetric a g at hs
  calc
    _ = (inner ℂ (dbarGraphMetricRoot a g) (dbarGraphMetricRoot a g)).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
    _ = _ := by rw [dbarGraphMetricRoot_selfAdjoint_pairing, hs]

theorem dbarGraphMetricInverseRoot_norm_sq {N : ℕ} (a g : CoulombConfig N) :
    ‖dbarGraphMetricInverseRoot a g‖ ^ 2 = (inner ℂ g (dbarGraphMetricInverse a g)).re := by
  have hs := congrArg (fun L : CoulombConfig N →L[ℂ] CoulombConfig N => L g)
    (dbarGraphMetricInverseRoot_square a)
  change dbarGraphMetricInverseRoot a (dbarGraphMetricInverseRoot a g) =
    dbarGraphMetricInverse a g at hs
  calc
    _ = (inner ℂ (dbarGraphMetricInverseRoot a g) (dbarGraphMetricInverseRoot a g)).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
    _ = _ := by rw [dbarGraphMetricInverseRoot_selfAdjoint_pairing, hs]

end RepulsiveCoulomb
