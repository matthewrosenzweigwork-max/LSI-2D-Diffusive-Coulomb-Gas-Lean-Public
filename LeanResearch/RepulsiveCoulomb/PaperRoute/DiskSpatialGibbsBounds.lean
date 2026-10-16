module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalDiskReferenceBounds
public import LeanResearch.RepulsiveCoulomb.PaperRoute.GibbsMomentFromOneBody
public import LeanResearch.RepulsiveCoulomb.PaperRoute.SpatialReferenceLabeledLSI

@[expose] public section

/-! Additive disk-normalized physical Gibbs moment application. Constants
are chosen from the spatial fixed-coupling/Hölder theorem before beta,R,N.
The old whole-plane thermal normalizer is not a selected proof step. -/
noncomputable section
open Set MeasureTheory Real
namespace RepulsiveCoulomb.PaperRoute

theorem paper_log_defect_bound {K L M E : ℝ}
    (hK : 0 < K) (hL : 0 < L) (hM : 0 < M) (hE : 0 < E)
    (h : E ≤ K⁻¹ * L ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ)) :
    Real.log K + Real.log E / 2 ≤
      Real.log K / 2 + Real.log L / 4 + Real.log M / 4 := by
  have hl := Real.log_le_log hE h
  rw [Real.log_mul (mul_pos (inv_pos.mpr hK) (Real.rpow_pos_of_pos hL _)).ne'
      (Real.rpow_pos_of_pos hM _).ne',
    Real.log_mul (inv_pos.mpr hK).ne' (Real.rpow_pos_of_pos hL _).ne',
    Real.log_inv, Real.log_rpow hL, Real.log_rpow hM] at hl
  linarith

/-- Exact three-log display, now with actual one-body integrability supplied
by the new disk envelope rather than selected internally by the old helper. -/
theorem paper_defect_two_log_bound_of_oneBody {N : ℕ} {β : ℝ}
    (hN : 0 < N) (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    (hU : Integrable (fun x : ℂ => Real.exp (-4 * β *
      equilibriumDensityPotential R.density x)) (R.measure : Measure ℂ)) :
    conditionalEntropyBranchDefect (N := N) R 2 ≤
      (1 / 2 : ℝ) * Real.log (equilibriumReferencePartition N β R) +
      (1 / 4 : ℝ) * Real.log (equilibriumReferencePartition N (6 * β) R) +
      (1 / 4 : ℝ) * Real.log (∫ x : ℂ,
        Real.exp (-4 * β * equilibriumDensityPotential R.density x) ∂R.measure) := by
  let := coulombMeasure_isProbability (N := N) hβ
  have hm := paper_physical_gibbs_defect_moment_of_oneBody hβ
    (by norm_num : (0 : ℝ) < 2) R (by simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using hU) hN
  have hE := integral_exp_pos hm.1
  change 0 < (∫ z : CoulombConfig N, Real.exp
    (-2 * β * conditionalEntropyBranchThermalB R z) ∂coulombMeasure N β) at hE
  have hK := equilibriumReferencePartition_canonical_pos hβ R N
  have hL := paper_reference_partition_pos_polynomial hβ R hN (by positivity : 0 ≤ 6 * β)
  have hM := integral_exp_pos hU
  have hb := hm.2
  norm_num at hb
  have h := paper_log_defect_bound hK hL hM hE (by
    simpa only [conditionalEntropyBranchThermalB, neg_mul] using hb)
  unfold conditionalEntropyBranchDefect
  convert h using 1; ring

/-- Genuine exponential integrability and its uniform bound, together with
both partition bounds. This is still conditional on physical reference data,
not on an entropy or functional-inequality certificate. -/
theorem paper_compact_reference_integral_bounds_disk {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ C M : ℝ, 0 < C ∧ 0 < M ∧ ∀ (β : ℝ), a ≤ β → β ≤ b →
      ∀ R : EquilibriumConstructedReference β, ∀ N : ℕ, 2 ≤ N →
        Integrable (fun z : CoulombConfig N => Real.exp
          (-2 * β * conditionalEntropyBranchThermalB R z)) (coulombMeasure N β) ∧
        equilibriumReferencePartition N β R ≤ C ∧
        equilibriumReferencePartition N (6 * β) R ≤ C ∧
        paperGibbsEntropyMoment R N ≤ M := by
  obtain ⟨C, hC, hpart⟩ := paper_reference_partition_pair_compact_via_spatial ha hab
  let L := 2 * equilibriumCompactLogBound a + 1 / 2
  let k := Real.exp (-b * L / 2)
  let J := paperDiskCompactPotentialBound a b 4
  let M := k⁻¹ * C ^ (1 / 2 : ℝ) * J ^ (1 / 2 : ℝ)
  have hk : 0 < k := Real.exp_pos _
  have hJ : 0 < J := paperDiskCompactPotentialBound_pos ha b 4
  have hM : 0 < M :=
    mul_pos (mul_pos (inv_pos.mpr hk) (Real.rpow_pos_of_pos hC _))
      (Real.rpow_pos_of_pos hJ _)
  refine ⟨C, M, hC, hM, ?_⟩
  intro β hlo hhi R N hN
  have hβ : 0 < β := ha.trans_le hlo
  have hn : 0 < N := by omega
  obtain ⟨hK, hK6⟩ := hpart β hlo hhi R N hN
  obtain ⟨hUi, hUb⟩ := paper_reference_potential_exponential_bound_disk
    ha hlo hhi (by norm_num : (0 : ℝ) < 4) R
  have hm := paper_physical_gibbs_defect_moment_of_oneBody hβ
    (by norm_num : (0 : ℝ) < 2) R (by simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using hUi) hn
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
  have hK6p := paper_reference_partition_pos_polynomial hβ R hn (by positivity : 0 ≤ 6 * β)
  have hRoot : (equilibriumReferencePartition N (6 * β) R) ^ (1 / 2 : ℝ) ≤ C ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hK6p.le hK6 (by norm_num)
  have hU0 : 0 ≤ ∫ x : ℂ, Real.exp (-4 * β * equilibriumDensityPotential R.density x) ∂R.measure :=
    integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hURoot := Real.rpow_le_rpow hU0 hUb (by norm_num : (0 : ℝ) ≤ 1 / 2)
  refine ⟨by simpa only [conditionalEntropyBranchThermalB] using hm.1, hK, hK6, ?_⟩
  have hb : paperGibbsEntropyMoment R N ≤
      (equilibriumReferencePartition N β R)⁻¹ *
        (equilibriumReferencePartition N (6 * β) R) ^ (1 / 2 : ℝ) *
          (∫ x : ℂ, Real.exp (-4 * β * equilibriumDensityPotential R.density x)
            ∂R.measure) ^ (1 / 2 : ℝ) := by
    simpa only [paperGibbsEntropyMoment, conditionalEntropyBranchThermalB,
      show (2 : ℝ) * (1 + 2) = 6 by norm_num,
      show (2 : ℝ) * 2 = 4 by norm_num] using hm.2
  apply hb.trans
  exact mul_le_mul
    (mul_le_mul hInv hRoot (Real.rpow_nonneg hK6p.le _) (inv_nonneg.mpr hk.le))
    hURoot (Real.rpow_nonneg hU0 _)
    (mul_nonneg (inv_nonneg.mpr hk.le) (Real.rpow_nonneg hC.le _))

end RepulsiveCoulomb.PaperRoute
