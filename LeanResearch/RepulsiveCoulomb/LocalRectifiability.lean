module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

@[expose] public section

/-! Local-to-global rectifiability on the compact unit interval. A Lebesgue
number gives a finite subdivision; variation is then additive over its cells. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem boundedVariationOn_unitInterval_of_local {X : Type*} [PseudoEMetricSpace X]
    (f : ℝ → X)
    (hlocal : ∀ x ∈ Icc (0 : ℝ) 1, ∃ U : Set ℝ,
      IsOpen U ∧ x ∈ U ∧ BoundedVariationOn f (Icc (0 : ℝ) 1 ∩ U)) :
    BoundedVariationOn f (Icc (0 : ℝ) 1) := by
  classical
  choose U hopen hmem hb using fun x : Icc (0 : ℝ) 1 => hlocal x x.2
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hopen
    (show Icc (0 : ℝ) 1 ⊆ ⋃ x, U x from fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hmem _⟩)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  let E : ℕ → ℝ := fun i => i / (n + 1 : ℝ)
  have hden : 0 < (n + 1 : ℝ) := by positivity
  have hE : Monotone E := fun i j hij =>
    div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) hden.le
  have hE0 : E 0 = 0 := by simp [E]
  have hEn : E (n + 1) = 1 := by simp [E, Nat.cast_add, Nat.cast_one, hden.ne']
  have hstep (i : ℕ) : E (i + 1) - E i = 1 / (n + 1 : ℝ) := by
    simp only [E, Nat.cast_add, Nat.cast_one]
    ring
  have hfinite (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      BoundedVariationOn f (Icc (E i) (E (i + 1))) := by
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    have hEi : E i ∈ Icc (0 : ℝ) 1 := by
      constructor
      · rw [← hE0]; exact hE (Nat.zero_le i)
      · rw [← hEn]; exact hE hi'.le
    obtain ⟨x, hx⟩ := hcover (E i) hEi
    apply (hb x).mono
    intro v hv
    refine ⟨⟨hEi.1.trans hv.1, ?_⟩, hx ?_⟩
    · apply hv.2.trans
      rw [← hEn]
      exact hE (by omega)
    · rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hv.1)]
      calc
        v - E i ≤ E (i + 1) - E i := sub_le_sub_right hv.2 _
        _ = 1 / (n + 1 : ℝ) := hstep i
        _ < δ := hn
  change eVariationOn f (Icc (0 : ℝ) 1) ≠ ⊤
  have he := eVariationOn.sum' f hE (n := n + 1)
  rw [hE0, hEn] at he
  rw [← he]
  exact ENNReal.sum_ne_top.mpr hfinite

end RepulsiveCoulomb
