import LeanResearch.RepulsiveCoulomb.PaperRoute.ReferenceSpatialPartition
import LeanResearch.RepulsiveCoulomb.PaperRoute.LabeledLSIFromReferenceMoments

/-! Supplied-reference entropy assembly through the literal spatial partition.
The signed-product normalization/collision-free/a.e. correspondence is now
load-bearing when applying the partition estimates to the entropy consumer.
Only the physical reference still awaits the new original thermal producer. -/
noncomputable section
open MeasureTheory
open PeriodicAttractiveLogGas
namespace RepulsiveCoulomb.PaperRoute

theorem paper_reference_partition_pair_via_spatial {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : EquilibriumConstructedReference β, ∀ N : ℕ, 2 ≤ N →
      equilibriumReferencePartition N β R ≤ C ∧
      equilibriumReferencePartition N (6 * β) R ≤ C := by
  obtain ⟨C, hC, hb⟩ := paper_spatial_partition_uniform (show 0 < 6 * β by positivity)
  refine ⟨C, hC, ?_⟩
  intro R N hN
  have h1 := hb β hβ R N hN β hβ.le (by linarith)
  have h6 := hb β hβ R N hN (6 * β) (by positivity) le_rfl
  rw [paper_reference_spatial_partition_eq hβ R (by omega) β] at h1
  rw [paper_reference_spatial_partition_eq hβ R (by omega) (6 * β)] at h6
  exact ⟨h1, h6⟩

/-- Compact-temperature constants are chosen at fixed T=6*b before beta,
R and N. The spatial correspondence is applied on that same physical law. -/
theorem paper_reference_partition_pair_compact_via_spatial {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, a ≤ β → β ≤ b →
      ∀ R : EquilibriumConstructedReference β, ∀ N : ℕ, 2 ≤ N →
        equilibriumReferencePartition N β R ≤ C ∧
        equilibriumReferencePartition N (6 * β) R ≤ C := by
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨C, hC, hbound⟩ := paper_spatial_partition_uniform (show 0 < 6 * b by positivity)
  refine ⟨C, hC, ?_⟩
  intro β hlo hhi R N hN
  have hβ : 0 < β := ha.trans_le hlo
  have h1 := hbound β hβ R N hN β hβ.le (by linarith)
  have h6 := hbound β hβ R N hN (6 * β) (by positivity) (by linarith)
  rw [paper_reference_spatial_partition_eq hβ R (by omega) β] at h1
  rw [paper_reference_spatial_partition_eq hβ R (by omega) (6 * β)] at h6
  exact ⟨h1, h6⟩

theorem paperLabeledRateFromReference_pos_via_spatial {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) : 0 < paperLabeledRateFromReference hβ R := by
  obtain ⟨C, hC, hb⟩ := paper_reference_partition_pair_via_spatial hβ
  obtain ⟨M, hM, hm⟩ := paper_gibbs_moment_bound_of_partition_six hβ R hC
    (fun N hN => (hb R N hN).2)
  exact paperLabeledRateFromReference_pos hβ R (fun N hN => (hb R N hN).1) hm

/-- Full original-form LSI with the genuine spatial signed-interaction
partition correspondence and compact-resolvent PI both load-bearing. -/
theorem paper_full_labeled_lsi_via_spatial_reference {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) (N : ℕ) (hN : 2 ≤ N)
    (u : CoulombFormDomain N hβ) :
    entropy (coulombMeasure N β) (fun z => (coulombFormValueL N hβ u z) ^ 2) ≤
      (((2 / paperLabeledRateFromReference hβ R) * coulombFormEnergy N hβ u : ℝ) : EReal) := by
  obtain ⟨C, hC, hb⟩ := paper_reference_partition_pair_via_spatial hβ
  exact paper_full_labeled_lsi_of_partition_bounds hβ R hC
    (fun N hN => (hb R N hN).1) (fun N hN => (hb R N hN).2) N hN u

end RepulsiveCoulomb.PaperRoute
