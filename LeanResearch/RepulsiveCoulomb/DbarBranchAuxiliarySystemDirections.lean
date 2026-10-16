module

public import LeanResearch.RepulsiveCoulomb.DbarBranchDensityLocalizedData
public import LeanResearch.RepulsiveCoulomb.DbarBranchComplexDivergenceTests

@[expose] public section

/-! Exact real coordinate directions and Wirtinger weights for the local
auxiliary system after w=rho*u. Both signs and the factor one-half are explicit. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace RepulsiveCoulomb

def dbarSystemDirection (N : ℕ) (d : Fin N × Bool) : CoulombConfig N :=
  coulombCoordinateInjection N d.1 (if d.2 then Complex.I else 1)

def dbarSystemPartialWeight (t : Bool) : ℂ := if t then -(Complex.I / 2) else 1 / 2

def dbarSystemBarWeight (t : Bool) : ℂ := if t then Complex.I / 2 else 1 / 2

theorem dbarSystemPartialWeight_formula {N : ℕ}
    (f : CoulombConfig N → ℂ) (z : CoulombConfig N) (j : Fin N) :
    (∑ t : Bool, dbarSystemPartialWeight t * fderiv ℝ f z (dbarSystemDirection N (j, t))) =
      coulombDCoordinate f z j := by
  simp only [Fintype.sum_bool, dbarSystemPartialWeight, dbarSystemDirection,
    Bool.false_eq_true, ite_false, ite_true, coulombDCoordinate]
  ring

theorem dbarSystemBarWeight_formula {N : ℕ}
    (f : CoulombConfig N → ℂ) (z : CoulombConfig N) (j : Fin N) :
    (∑ t : Bool, dbarSystemBarWeight t * fderiv ℝ f z (dbarSystemDirection N (j, t))) =
      coulombDbarCoordinate f z j := by
  simp only [Fintype.sum_bool, dbarSystemBarWeight, dbarSystemDirection,
    Bool.false_eq_true, ite_false, ite_true, coulombDbarCoordinate]
  ring

def coulombAuxiliaryScalarDensityPrincipal {N : ℕ}
    (b : Fin N) (d : Fin N × Bool) (z : CoulombConfig N) : ℂ :=
  -dbarSystemPartialWeight d.2 * coulombInverseRootMatrix z d.1 b

theorem coulombAuxiliaryScalarDensityPrincipal_contDiffAt {N : ℕ}
    (b : Fin N) (d : Fin N × Bool) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coulombAuxiliaryScalarDensityPrincipal b d) z :=
  contDiffAt_const.mul (coulombInverseRootMatrix_entry_contDiffAt d.1 b hz)

theorem coulombAuxiliaryScalarDensityPrincipal_direction_sum {N : ℕ}
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (z : CoulombConfig N)
    (b j : Fin N) (w : ℂ) :
    (∑ t : Bool, (fderiv ℝ (φ : CoulombConfig N → ℝ) z (dbarSystemDirection N (j, t)) : ℂ) *
      (coulombAuxiliaryScalarDensityPrincipal b (j, t) z * w)) =
      -coulombDCoordinate (fun x => (φ x : ℂ)) z j * coulombInverseRootMatrix z j b * w := by
  have h := dbarSystemPartialWeight_formula
    (TestFunction.postcompCLM Complex.ofRealCLM φ : CoulombConfig N → ℂ) z j
  simp_rw [coulombRealCore_complex_fderiv] at h
  simp only [TestFunction.postcompCLM_apply, Function.comp_def, Complex.ofRealCLM_apply] at h
  rw [← h]
  simp only [Fintype.sum_bool, coulombAuxiliaryScalarDensityPrincipal]
  ring

def coulombAuxiliaryRawCurlDensityPrincipal {N : ℕ} (β : ℝ)
    (i j b : Fin N) (d : Fin N × Bool) (z : CoulombConfig N) : ℂ :=
  dbarSystemBarWeight d.2 *
    ((if d.1 = i then coulombDensityRootMatrix β z j b else 0) -
      (if d.1 = j then coulombDensityRootMatrix β z i b else 0))

theorem coulombAuxiliaryRawCurlDensityPrincipal_contDiffAt {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (i j b : Fin N) (d : Fin N × Bool) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coulombAuxiliaryRawCurlDensityPrincipal β i j b d) z := by
  unfold coulombAuxiliaryRawCurlDensityPrincipal
  apply contDiffAt_const.mul
  apply ContDiffAt.sub
  · split_ifs
    · exact coulombDensityRootMatrix_entry_contDiffAt hβ j b hz
    · exact contDiffAt_const
  · split_ifs
    · exact coulombDensityRootMatrix_entry_contDiffAt hβ i b hz
    · exact contDiffAt_const

theorem coulombAuxiliaryRawCurlDensityPrincipal_direction_sum {N : ℕ} (β : ℝ)
    (f : CoulombConfig N → ℂ) (z : CoulombConfig N) (i j b : Fin N) (w : ℂ) :
    (∑ d : Fin N × Bool, fderiv ℝ f z (dbarSystemDirection N d) *
      (coulombAuxiliaryRawCurlDensityPrincipal β i j b d z * w)) =
      coulombDbarCoordinate f z i * coulombDensityRootMatrix β z j b * w -
        coulombDbarCoordinate f z j * coulombDensityRootMatrix β z i b * w := by
  classical
  rw [← dbarSystemBarWeight_formula f z i, ← dbarSystemBarWeight_formula f z j]
  simp [Fintype.sum_prod_type, Fintype.sum_bool, coulombAuxiliaryRawCurlDensityPrincipal,
    mul_sub, sub_mul, mul_ite, ite_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

end RepulsiveCoulomb
