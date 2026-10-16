import LeanResearch.RepulsiveCoulomb.PointScoreUncertainty
import LeanResearch.RepulsiveCoulomb.PointPunctureCapacity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The actual normalized ground-state transformation preserves the original
smooth puncture-avoiding core. No separation is imposed. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointGroundState_contDiff {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => φ z * Real.sqrt (pointDensity γ a y z)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∉ pointPunctures a y
  · have hd : ContDiffAt ℝ (⊤ : ℕ∞) (pointDensity γ a y) z :=
      (pointDensity_contDiffAt γ ha y hz).of_le (by simp)
    exact φ.contDiff.contDiffAt.mul (hd.sqrt (ne_of_gt (pointDensity_pos_off_punctures hγ ha y hz)))
  · have hn : z ∉ tsupport (φ : ℂ → ℝ) := fun ht => hz (φ.tsupport_subset ht)
    have he := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : ℂ => (0 : ℝ)) z).congr_of_eventuallyEq
    filter_upwards [he] with x hx
    simp [hx]

def pointGroundStateCore {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) : TestFunction (pointDomain a y) ℝ ⊤ :=
  ⟨fun z => φ z * Real.sqrt (pointDensity γ a y z),
    pointGroundState_contDiff hγ ha y φ, φ.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans φ.tsupport_subset⟩

theorem pointGroundStateCore_apply {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) (z : ℂ) :
    pointGroundStateCore hγ ha y φ z = φ z * Real.sqrt (pointDensity γ a y z) := rfl

theorem pointGroundStateCore_sq {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) (z : ℂ) :
    (pointGroundStateCore hγ ha y φ z) ^ 2 = pointDensity γ a y z * φ z ^ 2 := by
  rw [pointGroundStateCore_apply, mul_pow, Real.sq_sqrt (pointDensity_nonneg hγ ha y z), mul_comm]

end RepulsiveCoulomb
