import LeanResearch.RepulsiveCoulomb.PoleBranchPositiveCoreEntropy

/-! RECORDS-ONLY UNCOMPILED. The actual optimal LSI rate is the supremum of
zero and every positive rate satisfying the literal inequality on the full
original physical form. A genuine positive-entropy core test bounds the set.
The lower-rate bridge explicitly consumes an actual full-form LSI; this file
does not prove that analytic inequality. -/
noncomputable section
open Set MeasureTheory
open PeriodicAttractiveLogGas
namespace RepulsiveCoulomb

def poleBranchAdmissibleLSIRate (N : ℕ) {β : ℝ} (hβ : 0 < β) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ u : CoulombFormDomain N hβ,
    entropy (coulombMeasure N β) (fun z => (coulombFormValueL N hβ u z) ^ 2) ≤
      (((2 / ρ) * coulombFormEnergy N hβ u : ℝ) : EReal)

def poleBranchLSIRates (N : ℕ) {β : ℝ} (hβ : 0 < β) : Set ℝ :=
  insert 0 {ρ | poleBranchAdmissibleLSIRate N hβ ρ}

def poleBranchOptimalLSIRate (N : ℕ) {β : ℝ} (hβ : 0 < β) : ℝ :=
  sSup (poleBranchLSIRates N hβ)

theorem poleBranchLSIRates_nonempty (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (poleBranchLSIRates N hβ).Nonempty := ⟨0, Or.inl rfl⟩

theorem poleBranchLSIRates_nonneg {N : ℕ} {β ρ : ℝ} (hβ : 0 < β)
    (hρ : ρ ∈ poleBranchLSIRates N hβ) : 0 ≤ ρ := by
  rcases hρ with rfl | ⟨hρ, hLSI⟩
  · exact le_rfl
  · exact hρ.le

/-- Every admissible rate is bounded by the same genuine finite-entropy test. -/
theorem poleBranchLSIRates_le_entropy_test {N : ℕ} {β H : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) (hH : 0 < H)
    (he : entropy (coulombMeasure N β) (fun z => (coulombFormValueL N hβ u z) ^ 2) = (H : EReal)) :
    ∀ ρ ∈ poleBranchLSIRates N hβ, ρ ≤ (2 * coulombFormEnergy N hβ u) / H := by
  intro ρ hρ
  rcases hρ with rfl | ⟨hρ, hLSI⟩
  · exact div_nonneg (mul_nonneg (by norm_num) (coulombFormEnergy_nonneg N hβ u)) hH.le
  · have hbound := hLSI u
    rw [he] at hbound
    have hreal : H ≤ (2 / ρ) * coulombFormEnergy N hβ u := by exact_mod_cast hbound
    have hdiv : H ≤ (2 * coulombFormEnergy N hβ u) / ρ := by
      convert hreal using 1 <;> ring
    have hmul := (le_div_iff₀ hρ).mp hdiv
    apply (le_div_iff₀ hH).mpr
    nlinarith

theorem poleBranchLSIRates_bddAbove (N : ℕ) (hN : 2 ≤ N) {β : ℝ} (hβ : 0 < β) :
    BddAbove (poleBranchLSIRates N hβ) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 2 := ⟨N - 2, by omega⟩
  obtain ⟨u, H, hH, he⟩ := poleBranch_exists_form_positive_entropy n hβ
  exact ⟨(2 * coulombFormEnergy (n + 2) hβ u) / H,
    poleBranchLSIRates_le_entropy_test hβ u hH he⟩

theorem poleBranchOptimalLSIRate_nonneg (N : ℕ) (hN : 2 ≤ N) {β : ℝ} (hβ : 0 < β) :
    0 ≤ poleBranchOptimalLSIRate N hβ :=
  le_csSup (poleBranchLSIRates_bddAbove N hN hβ) (Or.inl rfl)

theorem poleBranch_admissible_le_optimalLSIRate {N : ℕ} (hN : 2 ≤ N) {β ρ : ℝ}
    (hβ : 0 < β) (hρ : poleBranchAdmissibleLSIRate N hβ ρ) :
    ρ ≤ poleBranchOptimalLSIRate N hβ :=
  le_csSup (poleBranchLSIRates_bddAbove N hN hβ) (Or.inr hρ)

theorem poleBranchOptimalLSIRate_le {N : ℕ} {β C : ℝ} (hβ : 0 < β) (hC : 0 ≤ C)
    (hbound : ∀ ρ, poleBranchAdmissibleLSIRate N hβ ρ → ρ ≤ C) :
    poleBranchOptimalLSIRate N hβ ≤ C := by
  apply csSup_le (poleBranchLSIRates_nonempty N hβ)
  intro ρ hρ
  rcases hρ with rfl | hρ
  · exact hC
  · exact hbound ρ hρ

theorem poleBranchOptimalLSIRate_le_entropy_test {N : ℕ} {β H : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) (hH : 0 < H)
    (he : entropy (coulombMeasure N β) (fun z => (coulombFormValueL N hβ u z) ^ 2) = (H : EReal)) :
    poleBranchOptimalLSIRate N hβ ≤ (2 * coulombFormEnergy N hβ u) / H :=
  csSup_le (poleBranchLSIRates_nonempty N hβ) (poleBranchLSIRates_le_entropy_test hβ u hH he)

/-- Explicitly conditional on an actual original full-form inequality. -/
theorem poleBranchOptimalLSIRate_pos_of_full_lsi {N : ℕ} (hN : 2 ≤ N) {β ρ : ℝ}
    (hβ : 0 < β) (hρ : 0 < ρ)
    (hLSI : ∀ u : CoulombFormDomain N hβ,
      entropy (coulombMeasure N β) (fun z => (coulombFormValueL N hβ u z) ^ 2) ≤
        (((2 / ρ) * coulombFormEnergy N hβ u : ℝ) : EReal)) :
    0 < poleBranchOptimalLSIRate N hβ :=
  hρ.trans_le (poleBranch_admissible_le_optimalLSIRate hN hβ ⟨hρ, hLSI⟩)


theorem poleBranchAdmissibleLSIRate_mono {N : ℕ} {β ρ σ : ℝ} (hβ : 0 < β)
    (hρ : poleBranchAdmissibleLSIRate N hβ ρ) (hσ : 0 < σ) (hσρ : σ ≤ ρ) :
    poleBranchAdmissibleLSIRate N hβ σ := by
  refine ⟨hσ, ?_⟩
  intro u
  have hc : 2 / ρ ≤ 2 / σ := div_le_div_of_nonneg_left (by norm_num) hσ hσρ
  have henergy := mul_le_mul_of_nonneg_right hc (coulombFormEnergy_nonneg N hβ u)
  exact (hρ.2 u).trans (by exact_mod_cast henergy)

/-- The positive optimal supremum is itself admissible; this is an order/limit
closure fact, not a proof that a positive LSI rate exists. -/
theorem poleBranchOptimalLSIRate_admissible_of_pos {N : ℕ} (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 < β) (hpos : 0 < poleBranchOptimalLSIRate N hβ) :
    poleBranchAdmissibleLSIRate N hβ (poleBranchOptimalLSIRate N hβ) := by
  obtain ⟨ρ, hρmem, hρpos⟩ := exists_lt_of_lt_csSup (poleBranchLSIRates_nonempty N hβ) hpos
  have hρ : poleBranchAdmissibleLSIRate N hβ ρ := by
    rcases hρmem with rfl | hρ
    · exact (lt_irrefl 0 hρpos).elim
    · exact hρ
  refine ⟨hpos, ?_⟩
  intro u
  let H : EReal := entropy (coulombMeasure N β) (fun z => (coulombFormValueL N hβ u z) ^ 2)
  by_cases hnonpos : H ≤ 0
  · have hR : 0 ≤ (2 / poleBranchOptimalLSIRate N hβ) * coulombFormEnergy N hβ u :=
      mul_nonneg (div_nonneg (by norm_num) hpos.le) (coulombFormEnergy_nonneg N hβ u)
    exact hnonpos.trans (by exact_mod_cast hR)
  · have hH : 0 < H := lt_of_not_ge hnonpos
    have htop : H ≠ ⊤ := ne_of_lt ((hρ.2 u).trans_lt (EReal.coe_lt_top _))
    have hbot : H ≠ ⊥ := ne_of_gt ((show (⊥ : EReal) < 0 by simp).trans hH)
    have hreal : (H.toReal : EReal) = H := EReal.coe_toReal htop hbot
    have hrealpos : 0 < H.toReal := EReal.toReal_pos hH htop
    have hbound := poleBranchOptimalLSIRate_le_entropy_test hβ u hrealpos hreal.symm
    have hmul := (le_div_iff₀ hrealpos).mp hbound
    have hdiv : H.toReal ≤ (2 * coulombFormEnergy N hβ u) / poleBranchOptimalLSIRate N hβ :=
      (le_div_iff₀ hpos).mpr (by nlinarith)
    have hineq : H.toReal ≤ (2 / poleBranchOptimalLSIRate N hβ) * coulombFormEnergy N hβ u := by
      convert hdiv using 1 <;> ring
    change H ≤ _
    rw [← hreal]
    exact_mod_cast hineq

theorem poleBranchAdmissibleLSIRate_iff_le_optimal {N : ℕ} (hN : 2 ≤ N)
    {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ) :
    poleBranchAdmissibleLSIRate N hβ ρ ↔ ρ ≤ poleBranchOptimalLSIRate N hβ := by
  constructor
  · exact poleBranch_admissible_le_optimalLSIRate hN hβ
  · intro hle
    exact poleBranchAdmissibleLSIRate_mono hβ
      (poleBranchOptimalLSIRate_admissible_of_pos hN hβ (hρ.trans_le hle)) hρ hle

end RepulsiveCoulomb
