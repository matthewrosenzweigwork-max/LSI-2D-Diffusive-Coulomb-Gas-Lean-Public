import LeanResearch.RepulsiveCoulomb.PaperRoute.ReferenceGibbsIntegrability
import LeanResearch.RepulsiveCoulomb.PaperRoute.DiskSpatialGibbsBounds

/-! Parameterized authored entropy route. The supplied physical reference is
explicit. The exact fixed-T/Hölder theorem is used at T=2*(1+ell)*b; no old
all-coupling partition or internal old one-body moment selector is used. -/
noncomputable section
open Set MeasureTheory InformationTheory Real
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem paper_reference_partition_pair_compact_ell_via_spatial {a b ℓ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, a ≤ β → β ≤ b →
      ∀ R : EquilibriumConstructedReference β, ∀ N : ℕ, 2 ≤ N →
        equilibriumReferencePartition N β R ≤ C ∧
        equilibriumReferencePartition N (2 * (1 + ℓ) * β) R ≤ C := by
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨C, hC, hbound⟩ := paper_spatial_partition_uniform
    (show 0 < 2 * (1 + ℓ) * b by positivity)
  refine ⟨C, hC, ?_⟩
  intro β hlo hhi R N hN
  have hβ : 0 < β := ha.trans_le hlo
  have hscale : 0 ≤ 2 * (1 + ℓ) := by positivity
  have ht := mul_le_mul_of_nonneg_left hhi hscale
  have hβT : β ≤ 2 * (1 + ℓ) * b := by nlinarith
  have h1 := hbound β hβ R N hN β hβ.le hβT
  have h2 := hbound β hβ R N hN (2 * (1 + ℓ) * β) (by positivity) ht
  rw [paper_reference_spatial_partition_eq hβ R (by omega) β] at h1
  rw [paper_reference_spatial_partition_eq hβ R (by omega) (2 * (1 + ℓ) * β)] at h2
  exact ⟨h1, h2⟩

theorem paper_compact_reference_integral_bounds_ell_disk {a b ℓ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hℓ : 0 < ℓ) :
    ∃ C M : ℝ, 0 < C ∧ 0 < M ∧ ∀ (β : ℝ), a ≤ β → β ≤ b →
      ∀ R : EquilibriumConstructedReference β, ∀ N : ℕ, 2 ≤ N →
        Integrable (fun z : CoulombConfig N => Real.exp
          (-ℓ * β * conditionalEntropyBranchThermalB R z)) (coulombMeasure N β) ∧
        equilibriumReferencePartition N β R ≤ C ∧
        equilibriumReferencePartition N (2 * (1 + ℓ) * β) R ≤ C ∧
        (∫ z : CoulombConfig N, Real.exp (-ℓ * β * conditionalEntropyBranchThermalB R z) ∂coulombMeasure N β) ≤ M := by
  obtain ⟨C, hC, hpart⟩ := paper_reference_partition_pair_compact_ell_via_spatial ha hab hℓ
  let L := 2 * equilibriumCompactLogBound a + 1 / 2
  let k := Real.exp (-b * L / 2)
  let J := paperDiskCompactPotentialBound a b (2 * ℓ)
  let M := k⁻¹ * C ^ (1 / 2 : ℝ) * J ^ (1 / 2 : ℝ)
  have hk : 0 < k := Real.exp_pos _
  have hJ : 0 < J := paperDiskCompactPotentialBound_pos ha b (2 * ℓ)
  have hM : 0 < M :=
    mul_pos (mul_pos (inv_pos.mpr hk) (Real.rpow_pos_of_pos hC _))
      (Real.rpow_pos_of_pos hJ _)
  refine ⟨C, M, hC, hM, ?_⟩
  intro β hlo hhi R N hN
  have hβ : 0 < β := ha.trans_le hlo
  have hn : 0 < N := by omega
  obtain ⟨hK, hK6⟩ := hpart β hlo hhi R N hN
  obtain ⟨hUi, hUb⟩ := paper_reference_potential_exponential_bound_disk
    ha hlo hhi (by positivity : (0 : ℝ) < 2 * ℓ) R
  have hm := paper_physical_gibbs_defect_moment_of_oneBody hβ
    hℓ R hUi hn
  have hc : |equilibriumDensityInteraction R.density| ≤ L :=
    equilibriumReference_interaction_abs_bound ha hlo R
  have hL : 0 ≤ L := (abs_nonneg _).trans hc
  have hcl := (abs_le.mp hc).1
  have h1 := mul_le_mul_of_nonneg_left hcl hβ.le
  have h2 := mul_le_mul_of_nonneg_right hhi hL
  have hexp : -b * L / 2 ≤ β * equilibriumDensityInteraction R.density / 2 := by
    nlinarith
  have hKa : k ≤ equilibriumReferencePartition N β R :=
    (Real.exp_le_exp.mpr hexp).trans (paper_reference_partition_lower_polynomial hβ R hn hβ.le)
  have hInv : (equilibriumReferencePartition N β R)⁻¹ ≤ k⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hk hKa
  have hK6p := paper_reference_partition_pos_polynomial hβ R hn (by positivity : 0 ≤ 2 * (1 + ℓ) * β)
  have hRoot : (equilibriumReferencePartition N (2 * (1 + ℓ) * β) R) ^ (1 / 2 : ℝ) ≤ C ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hK6p.le hK6 (by norm_num)
  have hU0 : 0 ≤ ∫ x : ℂ, Real.exp (-(2 * ℓ) * β * equilibriumDensityPotential R.density x) ∂R.measure :=
    integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hURoot := Real.rpow_le_rpow hU0 hUb (by norm_num : (0 : ℝ) ≤ 1 / 2)
  refine ⟨by simpa only [conditionalEntropyBranchThermalB] using hm.1, hK, hK6, ?_⟩
  have hb : (∫ z : CoulombConfig N, Real.exp (-ℓ * β * conditionalEntropyBranchThermalB R z) ∂coulombMeasure N β) ≤
      (equilibriumReferencePartition N β R)⁻¹ *
        (equilibriumReferencePartition N (2 * (1 + ℓ) * β) R) ^ (1 / 2 : ℝ) *
          (∫ x : ℂ, Real.exp (-(2 * ℓ) * β * equilibriumDensityPotential R.density x)
            ∂R.measure) ^ (1 / 2 : ℝ) := by
    simpa only [conditionalEntropyBranchThermalB] using hm.2
  apply hb.trans
  exact mul_le_mul
    (mul_le_mul hInv hRoot (Real.rpow_nonneg hK6p.le _) (inv_nonneg.mpr hk.le))
    hURoot (Real.rpow_nonneg hU0 _)
    (mul_nonneg (inv_nonneg.mpr hk.le) (Real.rpow_nonneg hC.le _))


/-- Literal finite-parameter Gibbs exponential integrability, supplied by the
new disk one-body estimate on the actual physical reference. -/
theorem paper_defect_exp_integrable_disk {N : ℕ} {β ℓ : ℝ}
    (hN : 0 < N) (hβ : 0 < β) (hℓ : 0 < ℓ) (R : EquilibriumConstructedReference β) :
    Integrable (fun z : CoulombConfig N =>
      Real.exp (-ℓ * β * conditionalEntropyBranchThermalB R z)) (coulombMeasure N β) := by
  have hU := (paper_reference_potential_exponential_bound_disk hβ le_rfl le_rfl
    (show 0 < 2 * ℓ by positivity) R).1
  simpa only [conditionalEntropyBranchThermalB] using
    (paper_physical_gibbs_defect_moment_of_oneBody hβ hℓ R hU hN).1

/-- Arbitrary labeled finite-KL competitors; the exponential input is
actually derived, with no symmetry or factorization certificate. -/
theorem paper_entropy_factorization_disk {N : ℕ} {β ℓ : ℝ}
    (hβ : 0 < β) (hℓ : 1 < ℓ) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig (N + 1))} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB R) Q) :
    (1 - 1 / ℓ) * (klDiv Q (coulombMeasure (N + 1) β)).toReal -
      conditionalEntropyBranchDefect (N := N + 1) R ℓ ≤
        (conditionalEntropyBranchCoulombS hβ Q).toReal :=
  conditionalEntropyBranch_factorization_defect_of_exp_integrable hβ R hKL hB hℓ
    (paper_defect_exp_integrable_disk (Nat.succ_pos N) hβ (zero_lt_one.trans hℓ) R)

theorem paper_finite_defect_nonneg_disk {N : ℕ} {β ℓ : ℝ}
    (hN : 0 < N) (hβ : 0 < β) (hℓ : 1 < ℓ) (R : EquilibriumConstructedReference β) :
    0 ≤ conditionalEntropyBranchDefect (N := N) R ℓ := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 1 := ⟨N - 1, by omega⟩
  exact conditionalEntropyBranch_defect_nonneg_of_integrable hβ R
    (paper_thermal_B_gibbs_integrable_polynomial hN hβ R) hℓ
    (paper_defect_exp_integrable_disk hN hβ (zero_lt_one.trans hℓ) R)

/-- One finite nonnegative bound precedes beta, R and every particle count.
This is the all-ell compact-defect row, not merely pointwise finiteness. -/
theorem paper_finite_defect_compact_uniform_disk {a b ℓ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hℓ : 1 < ℓ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ β : ℝ, a ≤ β → β ≤ b →
      ∀ R : EquilibriumConstructedReference β, ∀ N : ℕ, 2 ≤ N →
        0 ≤ conditionalEntropyBranchDefect (N := N) R ℓ ∧
          conditionalEntropyBranchDefect (N := N) R ℓ ≤ D := by
  obtain ⟨C, M, _hC, _hM, hb⟩ := paper_compact_reference_integral_bounds_ell_disk
    ha hab (zero_lt_one.trans hℓ)
  refine ⟨max 0 (Real.log C + Real.log M / ℓ), le_max_left _ _, ?_⟩
  intro β hlo hhi R N hN
  have hβ : 0 < β := ha.trans_le hlo
  let := coulombMeasure_isProbability (N := N) hβ
  have h := hb β hlo hhi R N hN
  refine ⟨paper_finite_defect_nonneg_disk (by omega) hβ hℓ R, ?_⟩
  have hkp := equilibriumReferencePartition_canonical_pos hβ R N
  have hep := integral_exp_pos h.1
  have hk := Real.log_le_log hkp h.2.1
  have hm := Real.log_le_log hep h.2.2.2
  unfold conditionalEntropyBranchDefect
  exact (add_le_add hk (div_le_div_of_nonneg_right hm
    (zero_lt_one.trans hℓ).le)).trans (le_max_right _ _)

def paperUniformEntropyDefectAt {β : ℝ} (R : EquilibriumConstructedReference β)
    (ℓ : ℝ) : ℝ :=
  sSup (Set.range (fun n : ℕ => conditionalEntropyBranchDefect (N := n + 2) R ℓ))

theorem paperUniformEntropyDefectAt_two {β : ℝ} (R : EquilibriumConstructedReference β) :
    paperUniformEntropyDefectAt R 2 = paperUniformEntropyDefect R := rfl

theorem paper_uniform_defectAt_compact_disk {a b ℓ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hℓ : 1 < ℓ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ β : ℝ, a ≤ β → β ≤ b →
      ∀ R : EquilibriumConstructedReference β,
        0 ≤ paperUniformEntropyDefectAt R ℓ ∧
          paperUniformEntropyDefectAt R ℓ ≤ D ∧
          ∀ N : ℕ, 2 ≤ N →
            conditionalEntropyBranchDefect (N := N) R ℓ ≤ paperUniformEntropyDefectAt R ℓ := by
  obtain ⟨D, hD, hb⟩ := paper_finite_defect_compact_uniform_disk ha hab hℓ
  refine ⟨D, hD, ?_⟩
  intro β hlo hhi R
  have h := hb β hlo hhi R
  have hBound : BddAbove (Set.range (fun n : ℕ =>
      conditionalEntropyBranchDefect (N := n + 2) R ℓ)) := by
    refine ⟨D, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (h (n + 2) (by omega)).2
  have hle (N : ℕ) (hN : 2 ≤ N) :
      conditionalEntropyBranchDefect (N := N) R ℓ ≤ paperUniformEntropyDefectAt R ℓ := by
    apply le_csSup hBound
    refine ⟨N - 2, ?_⟩
    change conditionalEntropyBranchDefect (N := N - 2 + 2) R ℓ =
      conditionalEntropyBranchDefect (N := N) R ℓ
    rw [Nat.sub_add_cancel hN]
  refine ⟨(h 2 le_rfl).1.trans (hle 2 le_rfl), ?_, hle⟩
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨n, rfl⟩
  exact (h (n + 2) (by omega)).2

/-- Fixed-temperature all-ell statement is the singleton compact case. -/
theorem paper_uniform_defectAt_finite_disk {β ℓ : ℝ}
    (hβ : 0 < β) (hℓ : 1 < ℓ) (R : EquilibriumConstructedReference β) :
    0 ≤ paperUniformEntropyDefectAt R ℓ ∧
      ∃ D : ℝ, paperUniformEntropyDefectAt R ℓ ≤ D ∧
        ∀ N : ℕ, 2 ≤ N →
          conditionalEntropyBranchDefect (N := N) R ℓ ≤ paperUniformEntropyDefectAt R ℓ := by
  obtain ⟨D, _hD, hb⟩ := paper_uniform_defectAt_compact_disk hβ le_rfl hℓ
  have h := hb β le_rfl le_rfl R
  exact ⟨h.1, D, h.2⟩

end RepulsiveCoulomb.PaperRoute
