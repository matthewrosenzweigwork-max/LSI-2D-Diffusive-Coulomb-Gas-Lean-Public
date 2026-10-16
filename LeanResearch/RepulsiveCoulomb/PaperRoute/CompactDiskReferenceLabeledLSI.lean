module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.DiskSpatialGibbsBounds
public import LeanResearch.RepulsiveCoulomb.PaperRoute.LabeledEntropyFromExplicitMoments
public import LeanResearch.RepulsiveCoulomb.PaperRoute.CompactResolventLabeledPoincare

@[expose] public section

/-! Additive compact-temperature assembly. The common defect is the
literal supremum over the supplied reference family, not a convenient upper
bound renamed as that supremum. All integral prerequisites are discharged by
the new disk envelope and the genuine spatial fixed-T/Hölder theorem. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real
open PeriodicAttractiveLogGas
namespace RepulsiveCoulomb.PaperRoute

def paperCompactEntropyDefect {a b : ℝ}
    (R : (β : Set.Icc a b) → EquilibriumConstructedReference β.1) : ℝ :=
  sSup (Set.range (fun β : Set.Icc a b => paperUniformEntropyDefect (R β)))

def paperCompactLabeledRateFromReferenceFamily {a b : ℝ} (ha : 0 < a)
    (R : (β : Set.Icc a b) → EquilibriumConstructedReference β.1) : ℝ :=
  assembledRate (paperOneSiteIntervalRate a b) (paperCompactEntropyDefect R)
    (poleBranchSymmetricIntervalSup ha b) (paperCrelInterval a b)

theorem paper_compact_reference_defect_bddAbove {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (R : (β : Set.Icc a b) → EquilibriumConstructedReference β.1) :
    BddAbove (Set.range (fun β : Set.Icc a b => paperUniformEntropyDefect (R β))) := by
  obtain ⟨C, M, _hC, _hM, hb⟩ := paper_compact_reference_integral_bounds_disk ha hab
  refine ⟨max 0 (Real.log C + Real.log M / 2), ?_⟩
  rintro _ ⟨β, rfl⟩
  have hβ : 0 < β.1 := ha.trans_le β.2.1
  have h := hb β.1 β.2.1 β.2.2 (R β)
  exact paper_uniform_defect_le_of_exp_integrable hβ (R β)
    (fun N hN => (h N hN).1) (fun N hN => (h N hN).2.1)
    (fun N hN => (h N hN).2.2.2)

theorem paper_reference_defect_le_compact {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (R : (β : Set.Icc a b) → EquilibriumConstructedReference β.1)
    (β : Set.Icc a b) :
    paperUniformEntropyDefect (R β) ≤ paperCompactEntropyDefect R :=
  le_csSup (paper_compact_reference_defect_bddAbove ha hab R) ⟨β, rfl⟩

theorem paper_compact_reference_defect_nonneg {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (R : (β : Set.Icc a b) → EquilibriumConstructedReference β.1) :
    0 ≤ paperCompactEntropyDefect R := by
  let β₀ : Set.Icc a b := ⟨a, le_rfl, hab⟩
  obtain ⟨C, M, _hC, _hM, hb⟩ := paper_compact_reference_integral_bounds_disk ha hab
  have h := hb a le_rfl hab (R β₀)
  have hn := paper_uniform_defect_nonneg_of_exp_integrable ha (R β₀)
    (fun N hN => (h N hN).1) (fun N hN => (h N hN).2.1)
    (fun N hN => (h N hN).2.2.2)
  exact hn.trans (paper_reference_defect_le_compact ha hab R β₀)

theorem paperCompactLabeledRateFromReferenceFamily_pos {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (R : (β : Set.Icc a b) → EquilibriumConstructedReference β.1) :
    0 < paperCompactLabeledRateFromReferenceFamily ha R :=
  assembledRate_pos (paperOneSiteIntervalRate_pos (b := b) ha)
    (paper_compact_reference_defect_nonneg ha hab R)
    (poleBranchSymmetricIntervalSup_pos ha hab).le (paperCrelInterval_pos (b := b) ha).le

theorem paper_full_defective_compact_via_disk_reference_family {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (R : (β : Set.Icc a b) → EquilibriumConstructedReference β.1)
    (β : Set.Icc a b) (N : ℕ) (hN : 2 ≤ N)
    (u : CoulombFormDomain N (ha.trans_le β.2.1)) :
    entropy (coulombMeasure N β.1)
      (fun z => (coulombFormValueL N (ha.trans_le β.2.1) u z) ^ 2) ≤
      (((4 / paperOneSiteIntervalRate a b) * coulombFormEnergy N (ha.trans_le β.2.1) u +
        2 * paperCompactEntropyDefect R *
          (∫ z, (coulombFormValueL N (ha.trans_le β.2.1) u z) ^ 2 ∂coulombMeasure N β.1) : ℝ) : EReal) := by
  obtain ⟨C, M, _hC, _hM, hb⟩ := paper_compact_reference_integral_bounds_disk ha hab
  have hβ : 0 < β.1 := ha.trans_le β.2.1
  have h := hb β.1 β.2.1 β.2.2 (R β)
  have hExp := fun N hN => (h N hN).1
  have hK := fun N hN => (h N hN).2.1
  have hM := fun N hN => (h N hN).2.2.2
  exact paper_full_defective_compact_of_integrable ha hβ β.2.1 β.2.2 (R β)
    (paper_compact_reference_defect_nonneg ha hab R) hExp
    (fun N hN => (paper_defect_le_uniform_of_exp_integrable hβ (R β) hExp hK hM hN).trans
      (paper_reference_defect_le_compact ha hab R β)) N hN u

theorem paper_full_labeled_lsi_compact_via_disk_reference_family {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (R : (β : Set.Icc a b) → EquilibriumConstructedReference β.1)
    (β : Set.Icc a b) (N : ℕ) (hN : 2 ≤ N)
    (u : CoulombFormDomain N (ha.trans_le β.2.1)) :
    entropy (coulombMeasure N β.1)
      (fun z => (coulombFormValueL N (ha.trans_le β.2.1) u z) ^ 2) ≤
      (((2 / paperCompactLabeledRateFromReferenceFamily ha R) *
        coulombFormEnergy N (ha.trans_le β.2.1) u : ℝ) : EReal) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 2 := ⟨N - 2, by omega⟩
  have hβ : 0 < β.1 := ha.trans_le β.2.1
  have hD := paper_compact_reference_defect_nonneg ha hab R
  have h := coulomb_form_tightening hβ
    (show 0 ≤ 2 * paperCompactEntropyDefect R + 2 by positivity)
    (fun v => paper_full_labeled_poincare_compact_via_resolvent
      ha hab hβ β.2.1 β.2.2 (n + 2) (by omega) v)
    (fun v => paper_full_defective_compact_via_disk_reference_family
      ha hab R β (n + 2) (by omega) v) u
  have he := two_div_assembledRate (paperOneSiteIntervalRate_pos (b := b) ha) hD
    (poleBranchSymmetricIntervalSup_pos ha hab).le (paperCrelInterval_pos (b := b) ha).le
  simpa only [paperCompactLabeledRateFromReferenceFamily, he] using h

/-- The rate, with the manuscript's literal D_I and exact coefficient, is
fixed before beta, particle count and observable. A new physical family is
still supplied until the new thermal constructor is sealed. -/
theorem paper_uniform_labeled_lsi_via_disk_reference_family {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (R : (β : Set.Icc a b) → EquilibriumConstructedReference β.1) :
    0 < paperCompactLabeledRateFromReferenceFamily ha R ∧
      ∀ (β : Set.Icc a b) (N : ℕ), 2 ≤ N →
        ∀ u : CoulombFormDomain N (ha.trans_le β.2.1),
          entropy (coulombMeasure N β.1)
            (fun z => (coulombFormValueL N (ha.trans_le β.2.1) u z) ^ 2) ≤
            (((2 / paperCompactLabeledRateFromReferenceFamily ha R) *
              coulombFormEnergy N (ha.trans_le β.2.1) u : ℝ) : EReal) :=
  ⟨paperCompactLabeledRateFromReferenceFamily_pos ha hab R,
    paper_full_labeled_lsi_compact_via_disk_reference_family ha hab R⟩

/-- Fixed-temperature exact rate with the thermal disk edge selected in all
moment, positivity, factorization and closed-form entropy applications. -/
theorem paperLabeledRateFromReference_pos_via_disk {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) : 0 < paperLabeledRateFromReference hβ R := by
  obtain ⟨C, M, _hC, _hM, hb⟩ := paper_compact_reference_integral_bounds_disk hβ le_rfl
  have h := hb β le_rfl le_rfl R
  exact assembledRate_pos (paperOneSiteRate_pos hβ)
    (paper_uniform_defect_nonneg_of_exp_integrable hβ R
      (fun N hN => (h N hN).1) (fun N hN => (h N hN).2.1)
      (fun N hN => (h N hN).2.2.2))
    (poleBranchSymmetricPoincareConstant_pos hβ).le (paperCrel_pos hβ).le

theorem paper_full_labeled_lsi_via_disk_reference {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) (N : ℕ) (hN : 2 ≤ N)
    (u : CoulombFormDomain N hβ) :
    entropy (coulombMeasure N β) (fun z => (coulombFormValueL N hβ u z) ^ 2) ≤
      (((2 / paperLabeledRateFromReference hβ R) * coulombFormEnergy N hβ u : ℝ) : EReal) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 2 := ⟨N - 2, by omega⟩
  obtain ⟨C, M, _hC, _hM, hb⟩ := paper_compact_reference_integral_bounds_disk hβ le_rfl
  have hm := hb β le_rfl le_rfl R
  have hExp := fun N hN => (hm N hN).1
  have hK := fun N hN => (hm N hN).2.1
  have hM := fun N hN => (hm N hN).2.2.2
  have hD := paper_uniform_defect_nonneg_of_exp_integrable hβ R hExp hK hM
  have h := coulomb_form_tightening hβ
    (show 0 ≤ 2 * paperUniformEntropyDefect R + 2 by positivity)
    (fun v => paper_full_labeled_poincare_via_resolvent hβ (n + 2) (by omega) v)
    (fun v => paper_full_defective_of_reference_bounds_of_exp_integrable
      hβ R hExp hK hM (n + 2) (by omega) v) u
  have he := two_div_assembledRate (paperOneSiteRate_pos hβ) hD
    (poleBranchSymmetricPoincareConstant_pos hβ).le (paperCrel_pos hβ).le
  simpa only [paperLabeledRateFromReference, he] using h

end RepulsiveCoulomb.PaperRoute
