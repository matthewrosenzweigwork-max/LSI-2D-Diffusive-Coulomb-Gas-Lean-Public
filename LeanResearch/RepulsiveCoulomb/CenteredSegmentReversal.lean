module

public import LeanResearch.RepulsiveCoulomb.MetricCenteredClippedSegments
public import Mathlib.Tactic

@[expose] public section

/-! Actual reversal of finite unit-interval segments, including their globally
 clipped centered samples. This changes no metric or source curve image. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def reverseUnitInterval (t : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨1 - t, sub_nonneg.mpr t.2.2, by linarith [t.2.1]⟩

@[simp] theorem reverseUnitInterval_zero :
    reverseUnitInterval ⟨0, by norm_num⟩ = ⟨1, by norm_num⟩ := by
  apply Subtype.ext
  simp [reverseUnitInterval]

@[simp] theorem reverseUnitInterval_one :
    reverseUnitInterval ⟨1, by norm_num⟩ = ⟨0, by norm_num⟩ := by
  apply Subtype.ext
  simp [reverseUnitInterval]

@[simp] theorem reverseUnitInterval_reverse (t : Icc (0 : ℝ) 1) :
    reverseUnitInterval (reverseUnitInterval t) = t := by
  apply Subtype.ext
  simp [reverseUnitInterval]

theorem reverseUnitInterval_projIcc (x : ℝ) :
    reverseUnitInterval (projIcc 0 1 (by norm_num) x) =
      projIcc 0 1 (by norm_num) (1 - x) := by
  by_cases h0 : x ≤ 0
  · rw [projIcc_of_le_left _ h0, reverseUnitInterval_zero,
      projIcc_of_right_le _ (by linarith : (1 : ℝ) ≤ 1 - x)]
  · by_cases h1 : 1 ≤ x
    · rw [projIcc_of_right_le _ h1, reverseUnitInterval_one,
        projIcc_of_le_left _ (by linarith : 1 - x ≤ (0 : ℝ))]
    · have hx : x ∈ Icc (0 : ℝ) 1 := ⟨(lt_of_not_ge h0).le, (lt_of_not_ge h1).le⟩
      rw [projIcc_of_mem _ hx, projIcc_of_mem _
        (show 1 - x ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hx.1, hx.2])]
      rfl

theorem metricCenteredClippedSegment_reverse {X : Type*}
    (γ : Icc (0 : ℝ) 1 → X) (τ : Icc (0 : ℝ) 1) (L t : ℝ) :
    metricCenteredClippedSegment (fun s => γ (reverseUnitInterval s))
      (reverseUnitInterval τ) L t = metricCenteredClippedSegment γ τ L (-t) := by
  unfold metricCenteredClippedSegment
  dsimp only
  rw [reverseUnitInterval_projIcc]
  congr 2
  dsimp [reverseUnitInterval]
  ring

end RepulsiveCoulomb
