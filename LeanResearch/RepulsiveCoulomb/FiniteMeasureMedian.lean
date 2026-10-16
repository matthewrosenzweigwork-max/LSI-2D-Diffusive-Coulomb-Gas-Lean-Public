module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Tactic

@[expose] public section

/-! Actual medians for bounded measurable observables under a finite nonzero
measure. Strict sub- and superlevel sets both have at most half the mass;
atoms at the median are allowed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem measureReal_iUnion_le_of_monotone {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {S : ℕ → Set X} (hS : Monotone S)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ n, μ.real (S n) ≤ K) :
    μ.real (⋃ n, S n) ≤ K := by
  apply ENNReal.toReal_le_of_le_ofReal hK
  rw [hS.measure_iUnion]
  exact iSup_le (fun n => (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hK).mpr (hbound n))

theorem measureReal_strict_lower_limit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (m : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t < m, μ.real {x | f x < t} ≤ K) : μ.real {x | f x < m} ≤ K := by
  let S : ℕ → Set X := fun n => {x | f x < m - 1 / ((n : ℝ) + 1)}
  have hS : Monotone S := by
    intro i j hij x hx
    have he := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (i : ℝ) + 1)
      (show (i : ℝ) + 1 ≤ (j : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right hij 1)
    dsimp [S] at *
    linarith
  have he : {x | f x < m} = ⋃ n, S n := by
    ext x
    constructor
    · intro hx
      change f x < m at hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < m - f x by linarith)
      exact mem_iUnion.mpr ⟨n, by dsimp [S]; exact (by linarith)⟩
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
      dsimp [S] at hn
      change f x < m
      linarith
  rw [he]
  exact measureReal_iUnion_le_of_monotone μ hS hK (fun n => hbound _ (by
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith))

theorem measureReal_strict_upper_limit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (m : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t, m < t → μ.real {x | t ≤ f x} ≤ K) : μ.real {x | m < f x} ≤ K := by
  let S : ℕ → Set X := fun n => {x | m + 1 / ((n : ℝ) + 1) ≤ f x}
  have hS : Monotone S := by
    intro i j hij x hx
    have he := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (i : ℝ) + 1)
      (show (i : ℝ) + 1 ≤ (j : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right hij 1)
    dsimp [S] at *
    linarith
  have he : {x | m < f x} = ⋃ n, S n := by
    ext x
    constructor
    · intro hx
      change m < f x at hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < f x - m by linarith)
      exact mem_iUnion.mpr ⟨n, by dsimp [S]; exact (by linarith)⟩
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
      dsimp [S] at hn
      change m < f x
      linarith
  rw [he]
  exact measureReal_iUnion_le_of_monotone μ hS hK (fun n => hbound _ (by
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith))

theorem exists_median_of_ae_bounded {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    (f : X → ℝ) (hf : Measurable f) {L U : ℝ}
    (hb : ∀ᵐ x ∂μ, L ≤ f x ∧ f x ≤ U) :
    ∃ m : ℝ, μ.real {x | f x < m} ≤ μ.real univ / 2 ∧
      μ.real {x | m < f x} ≤ μ.real univ / 2 := by
  let A : Set ℝ := {t | μ.real {x | f x < t} ≤ μ.real univ / 2}
  have hmass : 0 < μ.real univ := measureReal_univ_pos
  have hhalf : 0 ≤ μ.real univ / 2 := by positivity
  have hL : L ∈ A := by
    have he : {x | f x < L} =ᵐ[μ] ∅ := by
      filter_upwards [hb] with x hx
      change (f x < L) = False
      simp [not_lt_of_ge hx.1]
    change μ.real {x | f x < L} ≤ _
    rw [measureReal_congr he]
    simpa using hhalf
  have hA : BddAbove A := by
    refine ⟨U, ?_⟩
    intro t ht
    by_contra h
    have hut : U < t := lt_of_not_ge h
    have he : {x | f x < t} =ᵐ[μ] univ := by
      filter_upwards [hb] with x hx
      change (f x < t) = True
      simp [hx.2.trans_lt hut]
    change μ.real {x | f x < t} ≤ μ.real univ / 2 at ht
    rw [measureReal_congr he] at ht
    linarith
  refine ⟨sSup A, measureReal_strict_lower_limit μ f _ hhalf ?_,
    measureReal_strict_upper_limit μ f _ hhalf ?_⟩
  · intro t ht
    obtain ⟨a, ha, hta⟩ := exists_lt_of_lt_csSup ⟨L, hL⟩ ht
    exact (measureReal_mono (fun x hx => lt_trans hx hta)).trans ha
  · intro t ht
    have hn : t ∉ A := by
      intro h
      exact (not_le_of_gt ht) (le_csSup hA h)
    have hm : μ.real univ / 2 < μ.real {x | f x < t} := lt_of_not_ge hn
    have he := measureReal_add_measureReal_compl (μ := μ) (measurableSet_lt hf (measurable_const (a := t)))
    have hcomp : {x | f x < t}ᶜ = {x | t ≤ f x} := by ext x; simp
    rw [hcomp] at he
    linarith

end RepulsiveCoulomb
