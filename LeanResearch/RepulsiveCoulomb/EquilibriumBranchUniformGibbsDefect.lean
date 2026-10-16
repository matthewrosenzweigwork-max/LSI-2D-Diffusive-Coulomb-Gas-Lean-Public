module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchGibbsDefectMoment
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchUniformPartition

@[expose] public section

/-! The manuscript's actual Gibbs defect moment is uniformly bounded for
all particle numbers on compact positive-temperature intervals. The final
logarithmic defect has a finite nonnegative upper bound; its own nonnegativity
is a separate conditional-entropy consequence. Records-only uncompiled source. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators
namespace RepulsiveCoulomb

def equilibriumGibbsDefectMoment {β : ℝ} (N : ℕ) (ℓ : ℝ)
    (R : EquilibriumConstructedReference β) : ℝ :=
  ∫ z : CoulombConfig N, Real.exp (-ℓ * β *
    equilibriumDefectEnergy R.density (WithLp.ofLp z)) ∂coulombMeasure N β

theorem equilibriumGibbsDefectMoment_pos {β ℓ : ℝ} (hβ : 0 < β) (hℓ : 0 < ℓ)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) :
    0 < equilibriumGibbsDefectMoment N ℓ R := by
  letI := coulombMeasure_isProbability (N := N) hβ
  exact integral_exp_pos (equilibriumReference_physical_gibbs_defect_moment hβ hℓ R hN).1

/-- Genuine Gibbs defect-moment bound, uniform in N and beta on the given
compact interval, with ell fixed at any positive value. -/
theorem equilibriumGibbsDefectMoment_compact_upper {βlo βhi ℓ : ℝ}
    (hlo : 0 < βlo) (hord : βlo ≤ βhi) (hℓ : 0 < ℓ) :
    ∃ B : ℝ, 0 < B ∧ ∀ β (hβlo : βlo ≤ β) (hβhi : β ≤ βhi)
      (R : EquilibriumConstructedReference β), ∀ N : ℕ, 2 ≤ N →
      equilibriumGibbsDefectMoment N ℓ R ≤ B := by
  let T := 2 * (1 + ℓ) * βhi
  have hhi : 0 < βhi := hlo.trans_le hord
  have hT : 0 < T := by dsimp only [T]; positivity
  obtain ⟨C, hC, hCbound⟩ := equilibriumReferencePartition_uniform hT
  let L := 2 * equilibriumCompactLogBound βlo + 1 / 2
  let a := Real.exp (-T * L / 2)
  have ha : 0 < a := Real.exp_pos _
  let M := 1 + |equilibriumCompactPotentialBound βlo βhi (2 * ℓ)|
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨a⁻¹ * C ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ),
    mul_pos (mul_pos (inv_pos.mpr ha) (Real.rpow_pos_of_pos hC _))
      (Real.rpow_pos_of_pos hM _), ?_⟩
  intro β hβlo hβhi R N hN
  have hβ : 0 < β := hlo.trans_le hβlo
  have hn : 0 < N := by omega
  have hβT : β ≤ T := by dsimp only [T]; nlinarith
  have ht : 0 < 2 * (1 + ℓ) * β := by positivity
  have htT : 2 * (1 + ℓ) * β ≤ T := by
    dsimp only [T]
    nlinarith
  have hKa : a ≤ equilibriumReferencePartition N β R := by
    have hc : |equilibriumDensityInteraction R.density| ≤ L :=
      equilibriumReference_interaction_abs_bound hlo hβlo R
    have hL0 : 0 ≤ L := (abs_nonneg _).trans hc
    have hcl := (abs_le.mp hc).1
    have hm := mul_le_mul_of_nonneg_left hcl hβ.le
    have hTβ := mul_le_mul_of_nonneg_right hβT hL0
    apply (Real.exp_le_exp.mpr (show -T * L / 2 ≤
      β * equilibriumDensityInteraction R.density / 2 by nlinarith)).trans
    exact equilibriumReferencePartition_lower hβ R hn hβ.le
  have hKt := hCbound β hβ R N hN (2 * (1 + ℓ) * β) ht.le htT
  have hKpos := equilibriumReferencePartition_canonical_pos hβ R N
  have hKtpos := equilibriumReferencePartition_pos hβ R hn ht.le
  have hInv : (equilibriumReferencePartition N β R)⁻¹ ≤ a⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le ha hKa
  have hKr := Real.rpow_le_rpow hKtpos.le hKt (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hU := (equilibriumReference_potential_exponential_bound (θ := 2 * ℓ) hlo hβlo hβhi
    (mul_pos (by norm_num : (0 : ℝ) < 2) hℓ) R).2
  have hUM : (∫ x : ℂ, Real.exp (-(2 * ℓ) * β * equilibriumDensityPotential R.density x)
      ∂R.measure) ≤ M := by
    calc
      _ ≤ equilibriumCompactPotentialBound βlo βhi (2 * ℓ) := hU
      _ ≤ |equilibriumCompactPotentialBound βlo βhi (2 * ℓ)| := le_abs_self _
      _ ≤ M := by dsimp only [M]; linarith
  have hU0 : 0 ≤ ∫ x : ℂ, Real.exp (-(2 * ℓ) * β * equilibriumDensityPotential R.density x)
      ∂R.measure := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hUr := Real.rpow_le_rpow hU0 hUM (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hb := (equilibriumReference_physical_gibbs_defect_moment hβ hℓ R hn).2
  change equilibriumGibbsDefectMoment N ℓ R ≤ _ at hb
  apply hb.trans
  exact mul_le_mul
    (mul_le_mul hInv hKr (Real.rpow_nonneg hKtpos.le _) (inv_nonneg.mpr ha.le)) hUr
    (Real.rpow_nonneg hU0 _) (mul_nonneg (inv_nonneg.mpr ha.le) (Real.rpow_nonneg hC.le _))

/-- A finite, nonnegative uniform upper bound for the exact logarithmic
quantity whose supremum defines the manuscript additive defect. -/
theorem equilibriumGibbsDefect_compact_upper {βlo βhi ℓ : ℝ}
    (hlo : 0 < βlo) (hord : βlo ≤ βhi) (hℓ : 0 < ℓ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ β (hβlo : βlo ≤ β) (hβhi : β ≤ βhi)
      (R : EquilibriumConstructedReference β), ∀ N : ℕ, 2 ≤ N →
      Real.log (equilibriumReferencePartition N β R) +
        ℓ⁻¹ * Real.log (equilibriumGibbsDefectMoment N ℓ R) ≤ D := by
  have hhi : 0 < βhi := hlo.trans_le hord
  obtain ⟨C, hC, hCbound⟩ := equilibriumReferencePartition_uniform hhi
  obtain ⟨B, hB, hBbound⟩ := equilibriumGibbsDefectMoment_compact_upper hlo hord hℓ
  refine ⟨max 0 (Real.log C + ℓ⁻¹ * Real.log B), le_max_left _ _, ?_⟩
  intro β hβlo hβhi R N hN
  have hβ : 0 < β := hlo.trans_le hβlo
  have hn : 0 < N := by omega
  have hK := Real.log_le_log (equilibriumReferencePartition_canonical_pos hβ R N)
    (hCbound β hβ R N hN β hβ.le hβhi)
  have hE := Real.log_le_log (equilibriumGibbsDefectMoment_pos hβ hℓ R hn)
    (hBbound β hβlo hβhi R N hN)
  exact (add_le_add hK (mul_le_mul_of_nonneg_left hE (inv_nonneg.mpr hℓ.le))).trans (le_max_right _ _)

/-- Selected-reference specialization with precisely the manuscript ranges
beta in a compact positive interval, ell>1 and every N>=2. -/
theorem equilibriumConstructedReference_gibbs_defect_compact {βlo βhi ℓ : ℝ}
    (hlo : 0 < βlo) (hord : βlo ≤ βhi) (hℓ : 1 < ℓ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ β (hβlo : βlo ≤ β) (hβhi : β ≤ βhi),
      ∀ N : ℕ, 2 ≤ N →
      Real.log (equilibriumReferencePartition N β (equilibriumConstructedReference β (hlo.trans_le hβlo))) +
        ℓ⁻¹ * Real.log (equilibriumGibbsDefectMoment N ℓ
          (equilibriumConstructedReference β (hlo.trans_le hβlo))) ≤ D := by
  obtain ⟨D, hD, hb⟩ := equilibriumGibbsDefect_compact_upper hlo hord (show 0 < ℓ by linarith)
  exact ⟨D, hD, fun β hβlo hβhi N hN =>
    hb β hβlo hβhi (equilibriumConstructedReference β (hlo.trans_le hβlo)) N hN⟩

end RepulsiveCoulomb
