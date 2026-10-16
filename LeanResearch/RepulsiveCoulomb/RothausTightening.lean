module

public import LeanResearch.PeriodicAttractiveLogGas.Rothaus
public import LeanResearch.PeriodicAttractiveLogGas.EntropyL2

@[expose] public section

/-!
General probability-space tightening used in Section 6 of the supplied
repulsive manuscript, source SHA256
334c42429035ed3f994e16ec801ccb5568c43ca85c4750ecb89ef68a7c1f5e42.

This file reuses the existing entropy and Rothaus proofs without any torus
or attractive-Gibbs hypothesis. The analytic Poincare and defective bounds
are explicit premises of this helper, not proved inputs for either main
theorem. The concrete repulsive form and all uniform estimates remain to
be constructed. No main-theorem completion is claimed.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
open PeriodicAttractiveLogGas

namespace RepulsiveCoulomb

/-- Tightening for a bounded observable. The energy `E` is a scalar here;
a later concrete application must identify it and prove both estimates. -/
theorem bounded_defective_lsi_tightening
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} {E A B CP : ℝ}
    (hf : Measurable f) (hbounded : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (hB : 0 ≤ B + 2)
    (hPI : (∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) ≤ CP * E)
    (hdef : entropy μ (fun x ↦ (f x - ∫ y, f y ∂μ) ^ 2) ≤
      ((A * E + B * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ : ℝ) : EReal)) :
    entropy μ (fun x ↦ f x ^ 2) ≤
      (((A + (B + 2) * CP) * E : ℝ) : EReal) := by
  calc
    _ ≤ entropy μ (fun x ↦ (f x - ∫ y, f y ∂μ) ^ 2) +
        ((2 * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ : ℝ) : EReal) :=
      rothaus_centering hf hbounded
    _ ≤ ((A * E + B * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ : ℝ) : EReal) +
        ((2 * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ : ℝ) : EReal) :=
      add_le_add hdef le_rfl
    _ = ((A * E + (B + 2) *
        ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ : ℝ) : EReal) := by
      rw [← EReal.coe_add]
      congr 1
      ring
    _ ≤ (((A + (B + 2) * CP) * E : ℝ) : EReal) := by
      have h := mul_le_mul_of_nonneg_left hPI hB
      exact_mod_cast (show A * E + (B + 2) *
        (∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) ≤ (A + (B + 2) * CP) * E by
          nlinarith only [h])

/-- Algebraic lower rate of Section 6. This does not assert that the four
input constants have been constructed for the gas. -/
def assembledRate (oneSite defect symmetric relative : ℝ) : ℝ :=
  2 / (4 / oneSite + (2 * defect + 2) * (symmetric + relative))

theorem assembledRate_pos {oneSite defect symmetric relative : ℝ}
    (hOne : 0 < oneSite) (hDefect : 0 ≤ defect)
    (hSymmetric : 0 ≤ symmetric) (hRelative : 0 ≤ relative) :
    0 < assembledRate oneSite defect symmetric relative := by
  unfold assembledRate
  apply div_pos (by norm_num)
  exact add_pos_of_pos_of_nonneg (div_pos (by norm_num) hOne)
    (mul_nonneg (by linarith) (add_nonneg hSymmetric hRelative))

theorem two_div_assembledRate {oneSite defect symmetric relative : ℝ}
    (hOne : 0 < oneSite) (hDefect : 0 ≤ defect)
    (hSymmetric : 0 ≤ symmetric) (hRelative : 0 ≤ relative) :
    2 / assembledRate oneSite defect symmetric relative =
      4 / oneSite + (2 * defect + 2) * (symmetric + relative) := by
  have hden : 0 < 4 / oneSite + (2 * defect + 2) * (symmetric + relative) :=
    add_pos_of_pos_of_nonneg (div_pos (by norm_num) hOne)
      (mul_nonneg (by linarith) (add_nonneg hSymmetric hRelative))
  unfold assembledRate
  field_simp [ne_of_gt hden]

/-- Entropy lower semicontinuity transfers a core bound to its graph
closure. Closability and identification of the concrete repulsive domain
remain separate analytic obligations. -/
theorem entropy_bound_on_graph_closure
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {V : Type*} [NormedAddCommGroup V]
    {core : Set (Lp ℝ 2 μ × Lp V 2 μ)} {K : ℝ}
    (hcore : ∀ z ∈ core,
      entropy μ (fun x ↦ (z.1 x) ^ 2) ≤ ((K * ‖z.2‖ ^ 2 : ℝ) : EReal))
    {z : Lp ℝ 2 μ × Lp V 2 μ} (hz : z ∈ closure core) :
    entropy μ (fun x ↦ (z.1 x) ^ 2) ≤ ((K * ‖z.2‖ ^ 2 : ℝ) : EReal) := by
  have hcoef : 2 * (K / 2) = K := by ring
  have h := entropy_sq_le_on_graph_closure (C := K / 2)
    (core := core) (z := z) (by
      intro w hw
      simpa only [hcoef] using hcore w hw) hz
  simpa only [hcoef] using h

end RepulsiveCoulomb
