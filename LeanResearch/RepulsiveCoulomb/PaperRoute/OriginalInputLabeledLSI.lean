module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalOriginalReference
public import LeanResearch.RepulsiveCoulomb.PaperRoute.CompactDiskReferenceLabeledLSI
public meta import Lean.Meta.Tactic.AuxLemma
public meta import Lean.Elab.Command

@[expose] public section

/-! Original-input full-form labeled LSI. The physical reference is the
NEW actual thermal constructor, and the supplied-reference consumer is the
latest disk/moment/spatial/compact-resolvent assembly. The compact rate uses
its literal family supremum and is fixed before temperature, particle count
and observable. Higher-order thermal derivative tails remain a separate
open manuscript clause, not a hidden field of the physical record. -/
noncomputable section
open MeasureTheory Set
open PeriodicAttractiveLogGas
namespace RepulsiveCoulomb.PaperRoute

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- Fixed-temperature rate evaluated on the actual NEW physical reference. -/
def paperOriginalLabeledRate {β : ℝ} (hβ : 0 < β) : ℝ :=
  paperLabeledRateFromReference hβ (thermalConstructedReference β hβ)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem paperOriginalLabeledRate_pos {β : ℝ} (hβ : 0 < β) :
    0 < paperOriginalLabeledRate hβ :=
  paperLabeledRateFromReference_pos_via_disk hβ (thermalConstructedReference β hβ)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- No thermal reference, moment bound, PI/LSI certificate, or entropy
prerequisite is supplied by the caller. The domain is the original full
closed Coulomb form domain and the measure is the original labeled law. -/
theorem paper_full_labeled_lsi_original {β : ℝ} (hβ : 0 < β)
    (N : ℕ) (hN : 2 ≤ N) (u : CoulombFormDomain N hβ) :
    entropy (coulombMeasure N β) (fun z => (coulombFormValueL N hβ u z)^2) ≤
      (((2 / paperOriginalLabeledRate hβ) * coulombFormEnergy N hβ u : ℝ) : EReal) :=
  paper_full_labeled_lsi_via_disk_reference hβ (thermalConstructedReference β hβ) N hN u

/-- A family of NEW actual physical references, independent of N and u. -/
def paperOriginalReferenceFamily {a b : ℝ} (ha : 0 < a)
    (β : Set.Icc a b) : EquilibriumConstructedReference β.1 :=
  thermalConstructedReference β.1 (ha.trans_le β.2.1)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The exact compact-temperature assembled rate, including the literal
supremum D_I over the new family. It is fixed before β, N and u. -/
def paperOriginalCompactLabeledRate {a b : ℝ} (ha : 0 < a) : ℝ :=
  paperCompactLabeledRateFromReferenceFamily ha (paperOriginalReferenceFamily (b := b) ha)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem paperOriginalCompactLabeledRate_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 < paperOriginalCompactLabeledRate (b := b) ha :=
  paperCompactLabeledRateFromReferenceFamily_pos ha hab (paperOriginalReferenceFamily ha)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- Original-input uniform labeled full-form LSI with a single positive
rate for the entire positive compact temperature interval, all N≥2, and
all original full-form observables. -/
theorem paper_uniform_labeled_lsi_original {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    0 < paperOriginalCompactLabeledRate (b := b) ha ∧
      ∀ (β : Set.Icc a b) (N : ℕ), 2 ≤ N →
        ∀ u : CoulombFormDomain N (ha.trans_le β.2.1),
          entropy (coulombMeasure N β.1)
            (fun z => (coulombFormValueL N (ha.trans_le β.2.1) u z)^2) ≤
            (((2 / paperOriginalCompactLabeledRate (b := b) ha) *
              coulombFormEnergy N (ha.trans_le β.2.1) u : ℝ) : EReal) :=
  paper_uniform_labeled_lsi_via_disk_reference_family ha hab (paperOriginalReferenceFamily ha)

end RepulsiveCoulomb.PaperRoute
