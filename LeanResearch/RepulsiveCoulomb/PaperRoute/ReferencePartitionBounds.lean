import LeanResearch.RepulsiveCoulomb.PaperRoute.ReferencePolynomialIntegrability
import LeanResearch.RepulsiveCoulomb.PaperRoute.DGFixedCoupling
import LeanResearch.RepulsiveCoulomb.PaperRoute.ExponentialHolder

/-! The fixed-coupling partition bound is transported to lower couplings by
actual Hölder. Constants are selected before beta, the physical reference,
and particle number. The canonical energy remains unchanged. -/
noncomputable section
open MeasureTheory Real
namespace RepulsiveCoulomb.PaperRoute

/-- Actual fixed-to-lower-coupling interpolation, including integrability. -/
theorem paper_reference_partition_holder {β t T : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N)
    (ht : 0 < t) (htT : t ≤ T) :
    Integrable (fun z : Fin N → ℂ => Real.exp (-t * equilibriumModulatedEnergy R.density z))
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) ∧
    equilibriumReferencePartition N t R ≤ (equilibriumReferencePartition N T R) ^ (t / T) :=
  exponential_integral_holder _
    (equilibriumModulatedEnergy_measurable R.smooth.continuous.measurable) ht htT
    (paper_reference_modulated_exp_integrable_polynomial hβ R hN (ht.trans_le htT).le)

/-- Only T controls C. The all-coupling conclusion is obtained by the new
Hölder proof, not by selecting an existing stronger all-coupling endpoint. -/
theorem paper_reference_partition_uniform {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ β (_hβ : 0 < β) (R : EquilibriumConstructedReference β),
      ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ T → equilibriumReferencePartition N t R ≤ C := by
  obtain ⟨C, hC, hfixed⟩ := paper_dg_fixed_coupling hT
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro β hβ R N hN t ht htT
  rcases ht.eq_or_lt with rfl | ht
  · simpa only [equilibriumReferencePartition, neg_zero, zero_mul, Real.exp_zero,
      integral_const, probReal_univ, one_smul] using (le_max_left (1 : ℝ) C)
  exact exponential_integral_le_max_of_holder _
    (equilibriumModulatedEnergy_measurable R.smooth.continuous.measurable) ht htT
    (paper_reference_modulated_exp_integrable_polynomial hβ R (by omega) hT.le)
    (hfixed β hβ R N hN)

/-- The actual two partition bounds required by the entropy consumer, with
one common constant chosen before the supplied physical reference. -/
theorem paper_reference_partition_pair {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : EquilibriumConstructedReference β, ∀ N : ℕ, 2 ≤ N →
      equilibriumReferencePartition N β R ≤ C ∧
      equilibriumReferencePartition N (6 * β) R ≤ C := by
  obtain ⟨C, hC, hb⟩ := paper_reference_partition_uniform (show 0 < 6 * β by positivity)
  exact ⟨C, hC, fun R N hN => ⟨hb β hβ R N hN β hβ.le (by linarith),
    hb β hβ R N hN (6 * β) (by positivity) le_rfl⟩⟩

/-- Exact compact-temperature quantifiers. One T=6*b is fixed before beta,
the reference and N; no monotonicity of chosen reference witnesses is used. -/
theorem paper_reference_partition_pair_compact {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, a ≤ β → β ≤ b →
      ∀ R : EquilibriumConstructedReference β, ∀ N : ℕ, 2 ≤ N →
        equilibriumReferencePartition N β R ≤ C ∧
        equilibriumReferencePartition N (6 * β) R ≤ C := by
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨C, hC, hbound⟩ := paper_reference_partition_uniform (show 0 < 6 * b by positivity)
  refine ⟨C, hC, ?_⟩
  intro β hlo hhi R N hN
  have hβ : 0 < β := ha.trans_le hlo
  exact ⟨hbound β hβ R N hN β hβ.le (by linarith),
    hbound β hβ R N hN (6 * β) (by positivity) (by linarith)⟩

end RepulsiveCoulomb.PaperRoute
