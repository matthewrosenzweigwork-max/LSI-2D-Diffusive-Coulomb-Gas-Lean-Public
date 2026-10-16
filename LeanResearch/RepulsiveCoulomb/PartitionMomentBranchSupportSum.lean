module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDiagramCounting
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-! Finite support-count summation for actual ordered words. This file is pure
finite algebra and does not postulate any analytic or correlation theorem.
It consumes the label-preserving injection and binomial count in the existing
EquilibriumBranchDiagramCounting source. Records-only. -/

noncomputable section
open scoped BigOperators Classical
namespace RepulsiveCoulomb

/-- A subset of words with a fixed active count obeys the same explicit count. -/
theorem partitionMoment_count_subfamily {N p : ℕ}
    (s : Finset (Fin p → Fin N × Fin N)) (v : ℕ) :
    (s.filter (fun e => (equilibriumDiagramActive e).card = v)).card ≤
      N ^ v * v ^ (2 * p) := by
  apply (Finset.card_le_card ?_).trans (equilibriumDiagram_count_active_card_le_pow N p v)
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩

/-- All nonempty words have a positive active count, regardless of repeated
or reversed edges. -/
theorem partitionMoment_active_card_pos {N p : ℕ}
    (hp : 0 < p) (e : Fin p → Fin N × Fin N) :
    0 < (equilibriumDiagramActive e).card := by
  let j : Fin p := ⟨0, hp⟩
  exact Finset.card_pos.mpr ⟨(e j).1, (equilibriumDiagram_endpoints_active e j).1⟩

/-- Summing at most p support-count classes with the explicit label count.
The low-count class has at most p-r active labels. This is the exact finite
source of the improved N^(-r) contribution after normalization. -/
theorem partitionMoment_support_sum_le {N p r : ℕ}
    (hN : 1 ≤ N)
    (s : Finset (Fin p → Fin N × Fin N))
    (hsupport : ∀ e ∈ s, 1 ≤ (equilibriumDiagramActive e).card ∧
      (equilibriumDiagramActive e).card ≤ p)
    (a : (Fin p → Fin N × Fin N) → ℝ)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hlow : ∀ e ∈ s, (equilibriumDiagramActive e).card ≤ p - r → a e ≤ A)
    (hhigh : ∀ e ∈ s, p - r < (equilibriumDiagramActive e).card → a e ≤ C) :
    (∑ e ∈ s, a e) ≤
      (p : ℝ) ^ (2 * p + 1) * ((N : ℝ) ^ (p - r) * A + (N : ℝ) ^ p * C) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) ≤ N := le_trans (by norm_num) hNr
  have hpr : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  let H : ℝ := (p : ℝ) ^ (2 * p) *
    ((N : ℝ) ^ (p - r) * A + (N : ℝ) ^ p * C)
  have hmap : ∀ e ∈ s, (equilibriumDiagramActive e).card ∈ Finset.Icc 1 p := by
    intro e he
    exact Finset.mem_Icc.mpr (hsupport e he)
  have hgroup (v : ℕ) (hv : v ∈ Finset.Icc 1 p) :
      (∑ e ∈ s with (equilibriumDiagramActive e).card = v, a e) ≤ H := by
    have hvp : v ≤ p := (Finset.mem_Icc.mp hv).2
    have hvpr : (v : ℝ) ≤ p := by exact_mod_cast hvp
    have hvpow : (v : ℝ) ^ (2 * p) ≤ (p : ℝ) ^ (2 * p) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hvpr _
    have hcount : ((s.filter (fun e => (equilibriumDiagramActive e).card = v)).card : ℝ) ≤
        (N : ℝ) ^ v * (v : ℝ) ^ (2 * p) := by
      exact_mod_cast partitionMoment_count_subfamily s v
    by_cases hl : v ≤ p - r
    · have hNv : (N : ℝ) ^ v ≤ (N : ℝ) ^ (p - r) := pow_le_pow_right₀ hNr hl
      have hcount' : ((s.filter (fun e => (equilibriumDiagramActive e).card = v)).card : ℝ) ≤
          (N : ℝ) ^ (p - r) * (p : ℝ) ^ (2 * p) :=
        hcount.trans (mul_le_mul hNv hvpow (by positivity) (by positivity))
      calc
        (∑ e ∈ s with (equilibriumDiagramActive e).card = v, a e) ≤
            ∑ _e ∈ s with (equilibriumDiagramActive _e).card = v, A := by
          apply Finset.sum_le_sum
          intro e he
          have hes := (Finset.mem_filter.mp he).1
          have hev := (Finset.mem_filter.mp he).2
          exact hlow e hes (by simpa only [hev] using hl)
        _ = ((s.filter (fun e => (equilibriumDiagramActive e).card = v)).card : ℝ) * A := by
          simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((N : ℝ) ^ (p - r) * (p : ℝ) ^ (2 * p)) * A :=
          mul_le_mul_of_nonneg_right hcount' hA
        _ ≤ H := by
          dsimp [H]
          have hh : 0 ≤ (p : ℝ) ^ (2 * p) * ((N : ℝ) ^ p * C) := by positivity
          nlinarith
    · have hNv : (N : ℝ) ^ v ≤ (N : ℝ) ^ p := pow_le_pow_right₀ hNr hvp
      have hcount' : ((s.filter (fun e => (equilibriumDiagramActive e).card = v)).card : ℝ) ≤
          (N : ℝ) ^ p * (p : ℝ) ^ (2 * p) :=
        hcount.trans (mul_le_mul hNv hvpow (by positivity) (by positivity))
      calc
        (∑ e ∈ s with (equilibriumDiagramActive e).card = v, a e) ≤
            ∑ _e ∈ s with (equilibriumDiagramActive _e).card = v, C := by
          apply Finset.sum_le_sum
          intro e he
          have hes := (Finset.mem_filter.mp he).1
          have hev := (Finset.mem_filter.mp he).2
          exact hhigh e hes (by simpa only [hev] using Nat.lt_of_not_ge hl)
        _ = ((s.filter (fun e => (equilibriumDiagramActive e).card = v)).card : ℝ) * C := by
          simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((N : ℝ) ^ p * (p : ℝ) ^ (2 * p)) * C :=
          mul_le_mul_of_nonneg_right hcount' hC
        _ ≤ H := by
          dsimp [H]
          have hh : 0 ≤ (p : ℝ) ^ (2 * p) * ((N : ℝ) ^ (p - r) * A) := by positivity
          nlinarith
  calc
    (∑ e ∈ s, a e) =
        ∑ v ∈ Finset.Icc 1 p, ∑ e ∈ s with (equilibriumDiagramActive e).card = v, a e :=
      (Finset.sum_fiberwise_of_maps_to hmap a).symm
    _ ≤ ∑ _v ∈ Finset.Icc 1 p, H := Finset.sum_le_sum hgroup
    _ = (p : ℝ) * H := by simp [Nat.card_Icc, nsmul_eq_mul]
    _ = _ := by dsimp [H]; rw [pow_succ]; ring

/-- Exact cancellation of the normalized powers of N. -/
theorem partitionMoment_normalize_support_bound {N p r : ℕ}
    (hN : 0 < N) (hrp : r ≤ p) (A C : ℝ) :
    (1 / (N : ℝ)) ^ p *
        ((p : ℝ) ^ (2 * p + 1) * ((N : ℝ) ^ (p - r) * A + (N : ℝ) ^ p * C)) =
      (p : ℝ) ^ (2 * p + 1) * (A / (N : ℝ) ^ r + C) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hNpow : (N : ℝ) ^ p = (N : ℝ) ^ (p - r) * (N : ℝ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hrp]
  rw [one_div, inv_pow]
  field_simp [hN0]
  rw [hNpow]
  ring

end RepulsiveCoulomb
