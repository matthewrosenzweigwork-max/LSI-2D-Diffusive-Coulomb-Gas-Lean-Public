module

public import LeanResearch.RepulsiveCoulomb.CoulombRelativeJointLaw
public import LeanResearch.RepulsiveCoulomb.CoulombRelativeSwap
public import LeanResearch.RepulsiveCoulomb.CoulombFormIntegrals

@[expose] public section

noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology
namespace RepulsiveCoulomb

def coulombSwapFirst (N : ℕ) (z : CoulombConfig (N + 2)) : CoulombConfig (N + 2) :=
  coulombInsertZero (z (Fin.succ 0)) (coulombInsertZero (z 0) (coulombTail (coulombTail z)))

theorem coulombSwapFirst_relative {N : ℕ} (c u : ℂ) (y : CoulombConfig N) :
    coulombSwapFirst N (coulombRelativeInsert c u y) = coulombRelativeInsert c (-u) y := by
  ext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · change (Real.sqrt 2)⁻¹ • (c - u) = (Real.sqrt 2)⁻¹ • (c + -u)
    rw [sub_eq_add_neg]
  · change (Real.sqrt 2)⁻¹ • (c + u) = (Real.sqrt 2)⁻¹ • (c - -u)
    rw [sub_neg_eq_add]
  · rfl

theorem coulombSwapFirst_continuous (N : ℕ) : Continuous (coulombSwapFirst N) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · exact (coulombCoordinate (Fin.succ 0)).continuous
  · exact (coulombCoordinate 0).continuous
  · exact (coulombCoordinate k.succ.succ).continuous

end RepulsiveCoulomb

