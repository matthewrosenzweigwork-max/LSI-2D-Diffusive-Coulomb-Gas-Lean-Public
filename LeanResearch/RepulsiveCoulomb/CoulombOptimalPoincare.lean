module

public import LeanResearch.RepulsiveCoulomb.CoulombCompactTemperaturePoincare

@[expose] public section

/-! RECORDS-ONLY UNCHECKED DRAFT. The actual optimal Poincare coefficient,
not a renamed admissible witness. Finiteness is proved for particle counts>=2. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace RepulsiveCoulomb

def coulombPoincareQuotients (N : ℕ) {β : ℝ} (hβ : 0 < β) : Set ℝ :=
  insert 0 (range (fun u : {u : CoulombFormDomain N hβ // 0 < coulombFormEnergy N hβ u} =>
    variance (coulombFormValueL N hβ u.val : CoulombConfig N → ℝ) (coulombMeasure N β) /
      coulombFormEnergy N hβ u.val))

def coulombOptimalPoincare (N : ℕ) {β : ℝ} (hβ : 0 < β) : ℝ :=
  sSup (coulombPoincareQuotients N hβ)

theorem coulombPoincareQuotients_nonempty (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (coulombPoincareQuotients N hβ).Nonempty := ⟨0, Or.inl rfl⟩

theorem coulombPoincareQuotients_le {N : ℕ} {β C : ℝ} (hβ : 0 < β) (hC : 0 ≤ C)
    (hPI : ∀ u : CoulombFormDomain N hβ,
      variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
        C * coulombFormEnergy N hβ u) : ∀ q ∈ coulombPoincareQuotients N hβ, q ≤ C := by
  intro q hq
  rcases hq with rfl | ⟨u, rfl⟩
  · exact hC
  · exact (div_le_iff₀ u.property).mpr (hPI u.val)

theorem coulombPoincareQuotients_bddAbove (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    BddAbove (coulombPoincareQuotients (N + 2) hβ) := by
  obtain ⟨C, hC, hPI⟩ := coulomb_fixed_particle_poincare N hβ
  exact ⟨C, coulombPoincareQuotients_le hβ hC.le hPI⟩

theorem coulombOptimalPoincare_nonneg (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    0 ≤ coulombOptimalPoincare (N + 2) hβ :=
  le_csSup (coulombPoincareQuotients_bddAbove N hβ) (Or.inl rfl)

theorem coulombOptimalPoincare_le {N : ℕ} {β C : ℝ} (hβ : 0 < β) (hC : 0 ≤ C)
    (hPI : ∀ u : CoulombFormDomain N hβ,
      variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
        C * coulombFormEnergy N hβ u) : coulombOptimalPoincare N hβ ≤ C :=
  csSup_le (coulombPoincareQuotients_nonempty N hβ) (coulombPoincareQuotients_le hβ hC hPI)

theorem coulombOptimalPoincare_inequality (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain (N + 2) hβ) :
    variance (coulombFormValueL (N + 2) hβ u : CoulombConfig (N + 2) → ℝ)
      (coulombMeasure (N + 2) β) ≤
      coulombOptimalPoincare (N + 2) hβ * coulombFormEnergy (N + 2) hβ u := by
  by_cases hE : 0 < coulombFormEnergy (N + 2) hβ u
  · have hq : variance (coulombFormValueL (N + 2) hβ u : CoulombConfig (N + 2) → ℝ)
        (coulombMeasure (N + 2) β) / coulombFormEnergy (N + 2) hβ u ≤
        coulombOptimalPoincare (N + 2) hβ :=
      le_csSup (coulombPoincareQuotients_bddAbove N hβ) (Or.inr ⟨⟨u, hE⟩, rfl⟩)
    exact (div_le_iff₀ hE).mp hq
  · have hzero : coulombFormEnergy (N + 2) hβ u = 0 := by
      have hn : 0 ≤ coulombFormEnergy (N + 2) hβ u := sq_nonneg _
      linarith
    obtain ⟨C, _hC, hPI⟩ := coulomb_fixed_particle_poincare N hβ
    simpa only [hzero, mul_zero] using hPI u

theorem coulombOptimalPoincare_compact_temperature_bound (N : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ β (hβ : β ∈ Set.Icc a b),
      coulombOptimalPoincare (N + 2) (ha.trans_le hβ.1) ≤ C := by
  obtain ⟨C, hC, hPI⟩ := coulomb_compact_temperature_poincare N ha hab
  exact ⟨C, hC, fun β hβ => coulombOptimalPoincare_le (ha.trans_le hβ.1) hC.le (hPI β hβ)⟩

end RepulsiveCoulomb
