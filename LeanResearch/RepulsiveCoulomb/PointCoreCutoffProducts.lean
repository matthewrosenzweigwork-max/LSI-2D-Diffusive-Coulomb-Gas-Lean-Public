module

public import LeanResearch.RepulsiveCoulomb.PointUniformPoincare
public import LeanResearch.RepulsiveCoulomb.AnnularProductEnergy

@[expose] public section

/-! Actual inner and outer localization in the original smooth core. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

def pointCoreInnerCutoff {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (R : ℝ) (hR : 0 < R) (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    TestFunction (pointDomain a y) ℝ ⊤ :=
  ⟨fun x => pointCutoffBump 0 R hR x * φ x,
    (pointCutoffBump_contDiff 0 R hR).mul φ.contDiff,
    φ.hasCompactSupport.mul_left, tsupport_mul_subset_right.trans φ.tsupport_subset⟩

def pointCoreOuterCutoff {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (R : ℝ) (hR : 0 < R) (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    TestFunction (pointDomain a y) ℝ ⊤ :=
  ⟨fun x => (1 - pointCutoffBump 0 R hR x) * φ x,
    (contDiff_const.sub (pointCutoffBump_contDiff 0 R hR)).mul φ.contDiff,
    φ.hasCompactSupport.mul_left, tsupport_mul_subset_right.trans φ.tsupport_subset⟩

theorem pointCore_cutoff_decomposition {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (R : ℝ) (hR : 0 < R) (φ : TestFunction (pointDomain a y) ℝ ⊤) (x : ℂ) :
    pointCoreInnerCutoff R hR φ x + pointCoreOuterCutoff R hR φ x = φ x := by
  change pointCutoffBump 0 R hR x * φ x + (1 - pointCutoffBump 0 R hR x) * φ x = φ x
  ring

theorem pointCore_inner_cutoff_support {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (R : ℝ) (hR : 0 < R) (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    tsupport (pointCoreInnerCutoff R hR φ : ℂ → ℝ) ⊆ closedBall 0 (2 * R) := by
  change tsupport (fun x => pointCutoffBump 0 R hR x * φ x) ⊆ _
  exact tsupport_mul_subset_left.trans (pointCutoffBump_support 0 R hR).subset

theorem pointCore_outer_cutoff_zero {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (R : ℝ) (hR : 0 < R) (φ : TestFunction (pointDomain a y) ℝ ⊤) {x : ℂ}
    (hx : x ∈ closedBall 0 R) : pointCoreOuterCutoff R hR φ x = 0 := by
  change (1 - pointCutoffBump 0 R hR x) * φ x = 0
  rw [pointCutoffBump_one 0 R hR hx]
  ring

theorem pointCore_inner_cutoff_abs_le {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (R : ℝ) (hR : 0 < R) (φ : TestFunction (pointDomain a y) ℝ ⊤) (x : ℂ) :
    |pointCoreInnerCutoff R hR φ x| ≤ |φ x| := by
  change |pointCutoffBump 0 R hR x * φ x| ≤ _
  rw [abs_mul, abs_of_nonneg ((pointCutoffBump 0 R hR).nonneg)]
  exact mul_le_of_le_one_left (abs_nonneg _) ((pointCutoffBump 0 R hR).le_one)

end RepulsiveCoulomb
