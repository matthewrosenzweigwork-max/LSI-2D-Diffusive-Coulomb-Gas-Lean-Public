module

public import LeanResearch.RepulsiveCoulomb.JordanPhysicalCornerPatch
public import LeanResearch.RepulsiveCoulomb.JordanSymmetricCornerPatch
public import Mathlib.Analysis.Calculus.Deriv.Shift

@[expose] public section

/-! The actual additive real C1 map encoding both collars. It is not asserted
holomorphic or locally injective; physical monotonicity proves patch simplicity.
This map lets the existing purely continuous point-homotopy layer be reused. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def physicalCornerMap (L R : ℝ → ℂ) (p : ℂ) (z : ℂ) : ℂ := L z.re + R z.im - p

theorem physicalCornerMap_continuous {L R : ℝ → ℂ}
    (hL : Continuous L) (hR : Continuous R) (p : ℂ) :
    Continuous (physicalCornerMap L R p) :=
  ((hL.comp Complex.continuous_re).add (hR.comp Complex.continuous_im)).sub continuous_const

theorem physicalCornerMap_axes {L R : ℝ → ℂ} {p : ℂ}
    (hL0 : L 0 = p) (hR0 : R 0 = p) (t : ℝ) :
    physicalCornerMap L R p (t • (1 : ℂ)) = L t ∧
      physicalCornerMap L R p (t • Complex.I) = R t := by
  simp [physicalCornerMap, Complex.real_smul, hL0, hR0]

theorem physicalCornerPatch_eq_map (L R : ℝ → ℂ) (p : ℂ) (δ t : ℝ) :
    physicalCornerPatch L R p δ t =
      physicalCornerMap L R p (euclideanSymmetricCornerPatch δ 1 Complex.I t) := by
  have hcoord : euclideanSymmetricCornerPatch δ 1 Complex.I t =
      (physicalCornerLeftClock δ t : ℂ) + (physicalCornerRightClock δ t : ℂ) * Complex.I := by
    simp only [euclideanSymmetricCornerPatch, euclideanBezierCorner,
      physicalCornerLeftClock, physicalCornerRightClock, physicalCornerClock,
      Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_neg,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  unfold physicalCornerPatch physicalCornerMap
  rw [hcoord]
  simp [Complex.mul_re, Complex.mul_im]


def finitePhysicalIncoming {ι : Type*} (σ : Equiv.Perm ι)
    (f : ι → ℝ → ℂ) (i : ι) (t : ℝ) : ℂ := f (σ.symm i) (1 + t)

def finitePhysicalCornerMap {ι : Type*} (σ : Equiv.Perm ι)
    (f : ι → ℝ → ℂ) (i : ι) : ℂ → ℂ :=
  physicalCornerMap (finitePhysicalIncoming σ f i) (f i) (f i 0)

theorem finitePhysicalIncoming_contDiff {ι : Type*} (σ : Equiv.Perm ι)
    {f : ι → ℝ → ℂ} (hf : ∀ i, ContDiff ℝ 1 (f i)) (i : ι) :
    ContDiff ℝ 1 (finitePhysicalIncoming σ f i) := by
  unfold finitePhysicalIncoming
  have h := hf (σ.symm i)
  fun_prop

theorem finitePhysicalIncoming_deriv {ι : Type*} (σ : Equiv.Perm ι)
    (f : ι → ℝ → ℂ) (i : ι) (t : ℝ) :
    deriv (finitePhysicalIncoming σ f i) t = deriv (f (σ.symm i)) (1 + t) :=
  deriv_comp_const_add _ _ _

theorem finitePhysicalCornerMap_axes {ι : Type*} (σ : Equiv.Perm ι)
    (f : ι → ℝ → ℂ) (hend : ∀ i, f i 1 = f (σ i) 0) (i : ι) (t : ℝ) :
    finitePhysicalCornerMap σ f i (t • (1 : ℂ)) = f (σ.symm i) (1 + t) ∧
      finitePhysicalCornerMap σ f i (t • Complex.I) = f i t := by
  apply physicalCornerMap_axes
  · simpa [finitePhysicalIncoming] using hend (σ.symm i)
  · rfl

theorem finitePhysicalCornerMap_continuous {ι : Type*} (σ : Equiv.Perm ι)
    {f : ι → ℝ → ℂ} (hf : ∀ i, Continuous (f i)) (i : ι) :
    Continuous (finitePhysicalCornerMap σ f i) :=
  physicalCornerMap_continuous ((hf _).comp (continuous_const.add continuous_id)) (hf _) _

end RepulsiveCoulomb
