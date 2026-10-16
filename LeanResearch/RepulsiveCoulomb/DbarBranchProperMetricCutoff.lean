module

public import LeanResearch.RepulsiveCoulomb.DbarBranchGraphExhaustion
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Distribution.TestFunction

@[expose] public section

/-! Genuine compact smooth cutoffs on the full collision complement, built
from the checked proper exhaustion. Zero extension at collisions is proved
smooth using the compact sublevel containment of the support. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

def dbarUnitCutoff : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def coulombMetricCutoff {N : ℕ} (R : ℝ) : CoulombConfig N → ℝ :=
  (coulombDomain N : Set (CoulombConfig N)).indicator
    (fun z => dbarUnitCutoff (coulombGraphRadius z / R))

theorem coulombGraphRadius_contDiffAt {N : ℕ} {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) : ContDiffAt ℝ (⊤ : ℕ∞) (coulombGraphRadius (N := N)) z := by
  have he : (coulombGraphRadius (N := N)) = fun w => Real.sqrt (1 + coulombExhaustion w) :=
    funext coulombGraphRadius_eq
  rw [he]
  apply (contDiffAt_const.add ((coulombExhaustion_contDiffAt hz).of_le le_top)).sqrt
  rw [← coulombHolomorphicGraph_norm_sq]
  positivity

theorem coulombMetricCutoff_support_subset {N : ℕ} {R : ℝ} (hR : 0 < R) :
    Function.support (coulombMetricCutoff (N := N) R) ⊆
      {z : CoulombConfig N | z ∈ coulombDomain N ∧ coulombExhaustion z ≤ (2 * R) ^ 2} := by
  classical
  intro z hz
  change coulombMetricCutoff R z ≠ 0 at hz
  have hzΩ : z ∈ coulombDomain N := by
    by_contra hnot
    exact hz (by simp [coulombMetricCutoff, hnot])
  have hψ : dbarUnitCutoff (coulombGraphRadius z / R) ≠ 0 := by
    simpa only [coulombMetricCutoff, indicator_of_mem hzΩ] using hz
  have hm : coulombGraphRadius z / R ∈ ball (0 : ℝ) 2 := by
    change coulombGraphRadius z / R ∈ ball (0 : ℝ) dbarUnitCutoff.rOut
    rw [← dbarUnitCutoff.support_eq]
    exact hψ
  have hdiv : coulombGraphRadius z / R < 2 :=
    lt_of_le_of_lt (le_abs_self _) (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using hm)
  have hlt : coulombGraphRadius z < 2 * R := (div_lt_iff₀ hR).mp hdiv
  have hs : (coulombGraphRadius z) ^ 2 = 1 + coulombExhaustion z := by
    rw [coulombGraphRadius_eq, Real.sq_sqrt]
    rw [← coulombHolomorphicGraph_norm_sq]
    positivity
  refine ⟨hzΩ, ?_⟩
  nlinarith [coulombGraphRadius_pos z]

theorem coulombMetricCutoff_tsupport_subset {N : ℕ} {R : ℝ} (hR : 0 < R) :
    tsupport (coulombMetricCutoff (N := N) R) ⊆
      {z : CoulombConfig N | z ∈ coulombDomain N ∧ coulombExhaustion z ≤ (2 * R) ^ 2} :=
  closure_minimal (coulombMetricCutoff_support_subset hR)
    (coulombExhaustion_sublevel_isCompact N ((2 * R) ^ 2)).isClosed

theorem coulombMetricCutoff_hasCompactSupport {N : ℕ} {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (coulombMetricCutoff (N := N) R) :=
  (coulombExhaustion_sublevel_isCompact N ((2 * R) ^ 2)).of_isClosed_subset
    isClosed_closure (coulombMetricCutoff_tsupport_subset hR)

theorem coulombMetricCutoff_contDiff {N : ℕ} {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ (⊤ : ℕ∞) (coulombMetricCutoff (N := N) R) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hzΩ : z ∈ coulombDomain N
  · have hψ : ContDiff ℝ (⊤ : ℕ∞) (dbarUnitCutoff : ℝ → ℝ) := dbarUnitCutoff.contDiff
    apply (hψ.contDiffAt.comp z ((coulombGraphRadius_contDiffAt hzΩ).div_const R)).congr_of_eventuallyEq
    filter_upwards [(coulombDomain N).isOpen.mem_nhds hzΩ] with w hw
    exact indicator_of_mem hw _
  · have hzK : z ∉ {w : CoulombConfig N | w ∈ coulombDomain N ∧ coulombExhaustion w ≤ (2 * R) ^ 2} :=
      fun h => hzΩ h.1
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [(coulombExhaustion_sublevel_isCompact N ((2 * R) ^ 2)).isClosed.isOpen_compl.mem_nhds hzK]
      with w hw
    change coulombMetricCutoff R w = 0
    by_contra hne
    exact hw (coulombMetricCutoff_support_subset hR hne)

def coulombMetricCutoffTest {N : ℕ} {R : ℝ} (hR : 0 < R) :
    TestFunction (coulombDomain N) ℝ ⊤ where
  toFun := coulombMetricCutoff R
  contDiff' := coulombMetricCutoff_contDiff hR
  hasCompactSupport' := coulombMetricCutoff_hasCompactSupport hR
  tsupport_subset' := fun z hz => (coulombMetricCutoff_tsupport_subset hR hz).1

theorem coulombMetricCutoff_nonneg {N : ℕ} (R : ℝ) (z : CoulombConfig N) :
    0 ≤ coulombMetricCutoff R z := by
  classical
  by_cases hz : z ∈ coulombDomain N
  · simpa only [coulombMetricCutoff, indicator_of_mem hz] using
      (dbarUnitCutoff.nonneg (x := coulombGraphRadius z / R))
  · simp [coulombMetricCutoff, hz]

theorem coulombMetricCutoff_le_one {N : ℕ} (R : ℝ) (z : CoulombConfig N) :
    coulombMetricCutoff R z ≤ 1 := by
  classical
  by_cases hz : z ∈ coulombDomain N
  · simpa only [coulombMetricCutoff, indicator_of_mem hz] using
      (dbarUnitCutoff.le_one (x := coulombGraphRadius z / R))
  · simp [coulombMetricCutoff, hz]

theorem coulombMetricCutoff_eq_one {N : ℕ} {R : ℝ} (hR : 0 < R) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) (hρ : coulombGraphRadius z ≤ R) : coulombMetricCutoff R z = 1 := by
  rw [coulombMetricCutoff, indicator_of_mem hz]
  apply dbarUnitCutoff.one_of_mem_closedBall
  change |coulombGraphRadius z / R - 0| ≤ 1
  rw [sub_zero, abs_of_nonneg (div_nonneg (coulombGraphRadius_pos z).le hR.le)]
  exact (div_le_one hR).mpr hρ

end RepulsiveCoulomb
