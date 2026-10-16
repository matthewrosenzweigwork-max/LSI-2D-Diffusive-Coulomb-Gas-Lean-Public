module

public import LeanResearch.RepulsiveCoulomb.PointActualPreparationInnerRank

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Total finite preparation of any genuine current
positive-budget state. The only recursive move is the actually constructed
maximal translated strip; its rank drop was proved from actual contact and
coefficients. The output keeps every intermediate actual move, the final clean
ray, literal nested regions, unchanged allocation and exact signed invariants.
No assumed decreasing move, prepared state, or termination premise is used. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

namespace PointConstructedTranslatedMove
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j}
  {P : Set ℂ} {ν α : ℂ →₀ ℝ}

/-- Compose actual preparation after one literal translated residual. -/
def prependPreparation (M : PointConstructedTranslatedMove a y ha P ν α)
    (B : PointConstructedPreparation a y M.limit.cutRegion M.limit.cutCurvature α) :
    PointConstructedPreparation a y P ν α where
  Q := B.Q
  curvature := B.curvature
  state := B.state
  clean := B.clean
  subset_old := B.subset_old.trans M.residual.subset_old
  curvature_mass := B.curvature_mass.trans M.residual.curvature_mass
  negative_nonincrease := fun x ↦
    (B.negative_nonincrease x).trans (M.residual.negative_nonincrease x)
  interior_unchanged := fun x hx ↦
    (B.interior_unchanged x hx).trans
      (M.interior_unchanged x (interior_mono B.subset_old hx))
  rank_le := B.rank_le.trans M.outer_rank_le

end PointConstructedTranslatedMove

/-- A finite trace of actual translated cuts and an actually prepared last
state. In the producer, finish comes only from a present clean ray or the
original-input unmarked-boundary full-strip construction. -/
inductive PointFiniteActualPreparation {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (ha : ∀ j, 0 ≤ a j) :
    {P : Set ℂ} → {ν α : ℂ →₀ ℝ} → PointGeometricCutState a y P ν α → Type
  | finish {P ν α} (K : PointGeometricCutState a y P ν α)
      (B : PointConstructedPreparation a y P ν α) : PointFiniteActualPreparation a y ha K
  | translated {P ν α} (K : PointGeometricCutState a y P ν α)
      (M : PointConstructedTranslatedMove a y ha P ν α)
      (tail : PointFiniteActualPreparation a y ha M.next) : PointFiniteActualPreparation a y ha K

namespace PointFiniteActualPreparation
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j}

def preparation : {P : Set ℂ} → {ν α : ℂ →₀ ℝ} →
    {K : PointGeometricCutState a y P ν α} →
    PointFiniteActualPreparation a y ha K → PointConstructedPreparation a y P ν α
  | _, _, _, _, .finish _ B => B
  | _, _, _, _, .translated _ M tail => M.prependPreparation tail.preparation

def translatedCount : {P : Set ℂ} → {ν α : ℂ →₀ ℝ} →
    {K : PointGeometricCutState a y P ν α} →
    PointFiniteActualPreparation a y ha K → ℕ
  | _, _, _, _, .finish _ _ => 0
  | _, _, _, _, .translated _ _ tail => tail.translatedCount + 1

theorem translatedCount_le_rank {P : Set ℂ} {ν α : ℂ →₀ ℝ}
    {K : PointGeometricCutState a y P ν α} (T : PointFiniteActualPreparation a y ha K) :
    T.translatedCount ≤ pointPreparationInnerRank P ν α := by
  induction T with
  | finish K B => exact Nat.zero_le _
  | translated K M tail ih =>
      have hd := M.inner_rank_lt
      change tail.translatedCount + 1 ≤ _
      omega

theorem translatedCount_le_twice_marked {P : Set ℂ} {ν α : ℂ →₀ ℝ}
    {K : PointGeometricCutState a y P ν α} (T : PointFiniteActualPreparation a y ha K) :
    T.translatedCount ≤ 2 * (pointSignedMarked ν α).card :=
  T.translatedCount_le_rank.trans (pointPreparationInnerRank_le_twice_marked P ν α)

end PointFiniteActualPreparation

/-- The full finite inner construction. The Nat measure is the common marked
support plus its actual interior part, never an input transition certificate. -/
theorem PointGeometricCutState.construct_finite_preparation
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (K : PointGeometricCutState a y P ν α) :
    Nonempty (PointFiniteActualPreparation a y ha K) := by
  classical
  have build : ∀ n : ℕ, ∀ (P : Set ℂ) (ν α : ℂ →₀ ℝ)
      (K : PointGeometricCutState a y P ν α), pointPreparationInnerRank P ν α = n →
        Nonempty (PointFiniteActualPreparation a y ha K) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P ν α K hn
      by_cases hclean : Nonempty K.CleanRay
      · obtain ⟨R⟩ := hclean
        exact ⟨.finish K (K.prepare_identity R)⟩
      by_cases hmarked : ∃ x, x ∈ pointSignedMarked ν α ∧ x ∈ frontier P
      · obtain ⟨M⟩ := K.construct_maximal_translated_move ha y hmarked hclean
        have hd : pointPreparationInnerRank M.limit.cutRegion M.limit.cutCurvature α < n :=
          hn ▸ M.inner_rank_lt
        obtain ⟨tail⟩ := ih _ hd _ _ _ M.next rfl
        exact ⟨.translated K M tail⟩
      · have hfront : Disjoint (↑(pointSignedMarked ν α) : Set ℂ) (frontier P) :=
          Set.disjoint_left.mpr (fun x hx hf ↦ hmarked ⟨x, hx, hf⟩)
        obtain ⟨B⟩ := K.prepare_unmarked ha y hfront
        exact ⟨.finish K B⟩
  exact build _ P ν α K rfl

/-- The exact existing outer-induction preparation interface is now produced
from the original genuine state, including an actual clean positive-budget ray. -/
theorem PointGeometricCutState.prepare_total
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (K : PointGeometricCutState a y P ν α) :
    Nonempty (PointConstructedPreparation a y P ν α) := by
  obtain ⟨T⟩ := K.construct_finite_preparation ha y
  exact ⟨T.preparation⟩

theorem PointConstructedPreparation.interior_marks_subset
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {ν α : ℂ →₀ ℝ}
    (B : PointConstructedPreparation a y P ν α) :
    pointCutInteriorMarks B.Q B.curvature α ⊆ pointCutInteriorMarks P ν α :=
  pointCutInteriorMarks_subset B.subset_old B.interior_unchanged (fun _ _ ↦ rfl)

theorem PointConstructedPreparation.interior_mark_card_le
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {ν α : ℂ →₀ ℝ}
    (B : PointConstructedPreparation a y P ν α) :
    (pointCutInteriorMarks B.Q B.curvature α).card ≤ (pointCutInteriorMarks P ν α).card :=
  Finset.card_le_card B.interior_marks_subset

end RepulsiveCoulomb
