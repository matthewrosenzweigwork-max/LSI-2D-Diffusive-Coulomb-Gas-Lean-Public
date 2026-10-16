module

public import LeanResearch.RepulsiveCoulomb.CoulombCenterRelativeEmbedding
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.UpperLower.Basic

@[expose] public section

/-! Actual full-relative-domain optimal LSI rates, with an extended supremum
so that an unbounded admissible set is never silently assigned real sSup=0.
The original manuscript optimal rate is retained verbatim and bridged to the
extended supremum using its proved finite bound. -/
noncomputable section
open Set MeasureTheory
open PeriodicAttractiveLogGas
open scoped ENNReal
namespace RepulsiveCoulomb

variable {n : ℕ}

def coulombCenterRelativeAdmissibleRate (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) (ρ : ℝ) : Prop :=
  0 < ρ ∧ CoulombCenterRelativeFullLSI e he hβ (2 / ρ)

def coulombCenterRelativeRates (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) : Set ℝ :=
  insert 0 {ρ | coulombCenterRelativeAdmissibleRate e he hβ ρ}

def coulombCenterRelativeOptimalRate (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' coulombCenterRelativeRates e he hβ)

theorem coulombCenterRelativeRates_nonneg (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β ρ : ℝ} (hβ : 0 < β)
    (hρ : ρ ∈ coulombCenterRelativeRates e he hβ) : 0 ≤ ρ := by
  rcases hρ with rfl | ⟨hρ, hLSI⟩
  · exact le_rfl
  · exact hρ.le

theorem coulombCenterRelativeRates_downward (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β ρ σ : ℝ} (hβ : 0 < β)
    (hρ : ρ ∈ coulombCenterRelativeRates e he hβ) (hσ : 0 ≤ σ) (hσρ : σ ≤ ρ) :
    σ ∈ coulombCenterRelativeRates e he hβ := by
  by_cases hz : σ = 0
  · exact Or.inl hz
  · have hsp : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hz)
    rcases hρ with rfl | ⟨hρp, hρLSI⟩
    · exact (not_lt_of_ge hσρ hsp).elim
    · refine Or.inr ⟨hsp, ?_⟩
      intro u
      have hc : 2 / ρ ≤ 2 / σ := div_le_div_of_nonneg_left (by norm_num) hsp hσρ
      have hE : 0 ≤ coulombCenterRelativeFormEnergy e he hβ u := sq_nonneg _
      exact (hρLSI u).trans (by exact_mod_cast mul_le_mul_of_nonneg_right hc hE)

/-- The finite image of a nonnegative downward-closed real rate set is a lower
set in ENNReal. This remains true when its supremum is +∞. -/
theorem coulombCenter_ofReal_rates_lower {S : Set ℝ}
    (hn : ∀ r ∈ S, 0 ≤ r)
    (hd : ∀ r ∈ S, ∀ s, 0 ≤ s → s ≤ r → s ∈ S) :
    IsLowerSet (ENNReal.ofReal '' S) := by
  intro y x hxy hy
  rcases hy with ⟨r, hr, rfl⟩
  have hx : x ≠ ∞ := ne_of_lt (lt_of_le_of_lt hxy ENNReal.ofReal_lt_top)
  have hs : x.toReal ≤ r := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hxy
    simpa only [ENNReal.toReal_ofReal (hn r hr)] using h
  exact ⟨x.toReal, hd r hr x.toReal ENNReal.toReal_nonneg hs, ENNReal.ofReal_toReal hx⟩

/-- No attainment or finite-supremum assumption is needed for lower-set
intersection tensorization. -/
theorem coulombCenter_sSup_inter_lower {S T : Set ℝ≥0∞}
    (hS : IsLowerSet S) (hT : IsLowerSet T) :
    sSup (S ∩ T) = min (sSup S) (sSup T) := by
  apply le_antisymm sSup_inter_le
  change (sSup S ⊓ sSup T) ≤ sSup (S ∩ T)
  rw [sSup_inf_sSup]
  apply iSup_le
  intro p
  apply iSup_le
  intro hp
  exact le_sSup ⟨hS inf_le_left hp.1, hT inf_le_right hp.2⟩

theorem coulombCenter_ofReal_image_inter {S T : Set ℝ}
    (hS : ∀ r ∈ S, 0 ≤ r) (hT : ∀ r ∈ T, 0 ≤ r) :
    ENNReal.ofReal '' (S ∩ T) = (ENNReal.ofReal '' S) ∩ (ENNReal.ofReal '' T) := by
  ext x
  constructor
  · rintro ⟨r, ⟨hrS, hrT⟩, hr⟩
    exact ⟨⟨r, hrS, hr⟩, ⟨r, hrT, hr⟩⟩
  · rintro ⟨⟨r, hr, hxr⟩, ⟨s, hs, hxs⟩⟩
    have hrs : r = s := (ENNReal.ofReal_eq_ofReal_iff (hS r hr) (hT s hs)).mp (hxr.trans hxs.symm)
    subst s
    exact ⟨r, ⟨hr, hs⟩, hxr⟩

theorem coulombCenter_sSup_ofReal_Icc {β : ℝ} (hβ : 0 ≤ β) :
    sSup (ENNReal.ofReal '' Set.Icc 0 β) = ENNReal.ofReal β := by
  apply le_antisymm
  · apply sSup_le
    rintro x ⟨r, hr, rfl⟩
    exact ENNReal.ofReal_le_ofReal hr.2
  · exact le_sSup ⟨β, ⟨hβ, le_rfl⟩, rfl⟩

/-- The existing real optimal rate is exactly its extended admissible-set
supremum, using the source's boundedness proof rather than a default real sSup. -/
theorem coulombCenter_originalOptimalRate_extended (N : ℕ) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 < β) :
    ENNReal.ofReal (poleBranchOptimalLSIRate N hβ) =
      sSup (ENNReal.ofReal '' poleBranchLSIRates N hβ) := by
  apply le_antisymm
  · by_cases hp : 0 < poleBranchOptimalLSIRate N hβ
    · exact le_sSup ⟨poleBranchOptimalLSIRate N hβ,
        Or.inr (poleBranchOptimalLSIRate_admissible_of_pos hN hβ hp), rfl⟩
    · rw [ENNReal.ofReal_eq_zero.mpr (not_lt.mp hp)]
      exact bot_le
  · apply sSup_le
    rintro x ⟨r, hr, rfl⟩
    exact ENNReal.ofReal_le_ofReal
      (le_csSup (poleBranchLSIRates_bddAbove N hN hβ) hr)

end RepulsiveCoulomb
