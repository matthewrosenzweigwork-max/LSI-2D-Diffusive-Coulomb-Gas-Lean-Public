import LeanResearch.RepulsiveCoulomb.PointLineCapActualFamily
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith

/-! Records-only, uncompiled. Radius-selected crossings of the ACTUAL caps
escape at the two correct ends. The whole-disk preimage identity proves this
without any continuity or monotonicity assumption on the selected family. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- Totalize a large-radius family without changing it at large radii. -/
def lineCapLargeRadius (R₀ r : ℝ) : ℝ := max r (R₀ + 1)

theorem lineCapLargeRadius_gt (R₀ r : ℝ) : R₀ < lineCapLargeRadius R₀ r := by
  unfold lineCapLargeRadius
  linarith [le_max_right r (R₀ + 1)]

theorem lineCapLargeRadius_tendsto (R₀ : ℝ) :
    Tendsto (lineCapLargeRadius R₀) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with r hr
  exact hr.trans (le_max_left r (R₀ + 1))

theorem lineCapLargeRadius_eventually_eq (R₀ : ℝ) :
    lineCapLargeRadius R₀ =ᶠ[atTop] id := by
  filter_upwards [eventually_ge_atTop (R₀ + 1)] with r hr
  exact max_eq_left hr

def lineCapFamilyAt {c : ℝ → ℂ} {R₀ : ℝ}
    (C : ∀ R : ℝ, R₀ < R → LineCapGeometry c R) (r : ℝ) :
    LineCapGeometry c (lineCapLargeRadius R₀ r) :=
  C (lineCapLargeRadius R₀ r) (lineCapLargeRadius_gt R₀ r)

/-- Any fixed source time eventually lies strictly between the crossings. -/
theorem lineCapFamilyAt_eventually_contains_time {c : ℝ → ℂ} {R₀ : ℝ}
    (C : ∀ R : ℝ, R₀ < R → LineCapGeometry c R) (t : ℝ) :
    ∀ᶠ r in atTop, (lineCapFamilyAt C r).minus < t ∧ t < (lineCapFamilyAt C r).plus := by
  filter_upwards [(lineCapLargeRadius_tendsto R₀).eventually_gt_atTop ‖c t‖] with r hr
  exact ((lineCapFamilyAt C r).disk_preimage t).mp hr

theorem lineCapFamilyAt_plus_tendsto {c : ℝ → ℂ} {R₀ : ℝ}
    (C : ∀ R : ℝ, R₀ < R → LineCapGeometry c R) :
    Tendsto (fun r => (lineCapFamilyAt C r).plus) atTop atTop := by
  apply tendsto_atTop.2
  intro t
  filter_upwards [lineCapFamilyAt_eventually_contains_time C t] with r hr
  exact hr.2.le

theorem lineCapFamilyAt_minus_tendsto {c : ℝ → ℂ} {R₀ : ℝ}
    (C : ∀ R : ℝ, R₀ < R → LineCapGeometry c R) :
    Tendsto (fun r => (lineCapFamilyAt C r).minus) atTop atBot := by
  apply tendsto_atBot.2
  intro t
  filter_upwards [lineCapFamilyAt_eventually_contains_time C t] with r hr
  exact hr.1.le

/-- Retain BOTH actual position directions at the radius crossings. -/
theorem lineCapFamilyAt_position_limits {c : ℝ → ℂ} {R₀ : ℝ}
    (C : ∀ R : ℝ, R₀ < R → LineCapGeometry c R)
    (hp : Tendsto (fun t => c t / (‖c t‖ : ℂ)) atTop (𝓝 (1 : ℂ)))
    (hm : Tendsto (fun t => c t / (‖c t‖ : ℂ)) atBot (𝓝 (-1 : ℂ))) :
    Tendsto (fun r => c (lineCapFamilyAt C r).plus /
      (‖c (lineCapFamilyAt C r).plus‖ : ℂ)) atTop (𝓝 (1 : ℂ)) ∧
    Tendsto (fun r => c (lineCapFamilyAt C r).minus /
      (‖c (lineCapFamilyAt C r).minus‖ : ℂ)) atTop (𝓝 (-1 : ℂ)) :=
  ⟨hp.comp (lineCapFamilyAt_plus_tendsto C), hm.comp (lineCapFamilyAt_minus_tendsto C)⟩

/-- The negative-end hypothesis uses the OUTWARD negative tangent; after
reversing it, both tangents in the oriented line tend to the same vector 1. -/
theorem lineCapFamilyAt_oriented_tangent_limits {c : ℝ → ℂ} {R₀ : ℝ}
    (C : ∀ R : ℝ, R₀ < R → LineCapGeometry c R)
    (hp : Tendsto (fun t => c t / (‖c t‖ : ℂ)) atTop (𝓝 (1 : ℂ)))
    (hm : Tendsto (fun t => c t / (‖c t‖ : ℂ)) atBot (𝓝 (-1 : ℂ)))
    (hvp : Tendsto (fun t => deriv c t / (‖deriv c t‖ : ℂ) -
      c t / (‖c t‖ : ℂ)) atTop (𝓝 0))
    (hvm : Tendsto (fun t => (-deriv c t) / (‖deriv c t‖ : ℂ) -
      c t / (‖c t‖ : ℂ)) atBot (𝓝 0)) :
    Tendsto (fun r => deriv c (lineCapFamilyAt C r).plus /
      (‖deriv c (lineCapFamilyAt C r).plus‖ : ℂ)) atTop (𝓝 (1 : ℂ)) ∧
    Tendsto (fun r => deriv c (lineCapFamilyAt C r).minus /
      (‖deriv c (lineCapFamilyAt C r).minus‖ : ℂ)) atTop (𝓝 (1 : ℂ)) := by
  have hvp' : Tendsto (fun t => deriv c t / (‖deriv c t‖ : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa only [sub_add_cancel, zero_add] using hvp.add hp
  have hvm' : Tendsto (fun t => deriv c t / (‖deriv c t‖ : ℂ)) atBot (𝓝 (1 : ℂ)) := by
    simpa only [sub_add_cancel, zero_add, neg_div, neg_neg] using (hvm.add hm).neg
  exact ⟨hvp'.comp (lineCapFamilyAt_plus_tendsto C),
    hvm'.comp (lineCapFamilyAt_minus_tendsto C)⟩

end RepulsiveCoulomb
