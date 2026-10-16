import LeanResearch.RepulsiveCoulomb.DbarBranchMetricCoefficientExtension
import LeanResearch.RepulsiveCoulomb.DbarBranchCompactInputMollifier
import Mathlib.Topology.MetricSpace.Thickening

/-! A common compact support margin and a single shrinking bump family for
all coefficients, inputs and outputs of a localized auxiliary system. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology Pointwise
namespace RepulsiveCoulomb

theorem coulombCompact_common_metric_margin {N : ℕ} {K : Set (CoulombConfig N)}
    (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N) :
    ∃ R r : ℝ, 0 < R ∧ 0 < r ∧
      Metric.closedBall 0 r + K ⊆ coulombGraphRadiusSublevel N R := by
  obtain ⟨R, hR, hKR⟩ := coulombCompact_in_radius_sublevel hK hKΩ
  obtain ⟨r, hr, hmargin⟩ := hK.exists_cthickening_subset_open
    (coulombGraphRadiusSublevel_isOpen N R) hKR
  refine ⟨R, r, hR, hr, ?_⟩
  rintro z ⟨a, ha, k, hk, rfl⟩
  apply hmargin
  apply mem_cthickening_of_dist_le (a + k) k r K hk
  simpa only [dist_eq_norm, add_sub_cancel_right, mem_closedBall, dist_zero_right, sub_zero] using ha

theorem coulombCompact_mollifier_common_support {N : ℕ} {K : Set (CoulombConfig N)}
    (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N) :
    ∃ L : Set (CoulombConfig N), IsCompact L ∧ L ⊆ coulombDomain N ∧
      ∃ r : ℝ, 0 < r ∧ ∀ {f : CoulombConfig N → ℂ} (hf : MemLp f 2 volume)
        (hfc : HasCompactSupport f) (hsupp : Function.support f ⊆ K)
        (ψ : ContDiffBump (0 : CoulombConfig N)), ψ.rOut ≤ r →
        tsupport (dbarCompactInputMollifyTest hf hfc ψ : CoulombConfig N → ℂ) ⊆ L := by
  obtain ⟨R, r, hR, hr, hmargin⟩ := coulombCompact_common_metric_margin hK hKΩ
  refine ⟨Metric.closedBall 0 r + K, (isCompact_closedBall _ _).add hK,
    fun z hz => (hmargin hz).1, r, hr, ?_⟩
  intro f hf hfc hsupp ψ hψ
  exact (dbarCompactInputMollifyTest_support hf hfc ψ hK hsupp).trans
    (add_subset_add (closedBall_subset_closedBall hψ) Subset.rfl)

end RepulsiveCoulomb
