import LeanResearch.RepulsiveCoulomb.PointUnchangedConeSectorChart
import LeanResearch.RepulsiveCoulomb.PointFlatEmbeddingClosure
import LeanResearch.RepulsiveCoulomb.EuclideanClosedSectorSource
import Mathlib.Topology.Homeomorph.Lemmas

/-! SOURCE-ONLY, UNCOMPILED. Invert the actual unchanged cone-sector chart
on its exact physical range. This supplies a continuous forward branch and
the unchanged constant-one metric bounds for finite surgery gluing. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointUnchangedConeSectorMap_isClosedEmbedding
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (lo : ℝ) {β R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hRC : R ≤ C.radius) :
    Topology.IsClosedEmbedding (pointUnchangedConeSectorMap (β := β) (R := R) C lo) := by
  apply pointFlatEmbedding_isClosedEmbedding ha y
    ((closedEuclideanSector_isClosed hβ hβπ).inter
      (isClosed_le continuous_norm continuous_const))
  exact pointUnchangedConeSectorMap_metric C lo hβπ hRC

def pointUnchangedConeSectorRangeHomeomorph
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (lo : ℝ) {β R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hRC : R ≤ C.radius) :
    flatLinkSectorDisk β R ≃ₜ range (pointUnchangedConeSectorMap (β := β) (R := R) C lo) :=
  (pointUnchangedConeSectorMap_isClosedEmbedding ha y C lo hβ hβπ hRC).isEmbedding.toHomeomorph

theorem pointUnchangedConeSectorRangeHomeomorph_inverse_metric
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (lo : ℝ) {β R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hRC : R ≤ C.radius)
    (x z : range (pointUnchangedConeSectorMap (β := β) (R := R) C lo)) :
    dist ((pointUnchangedConeSectorRangeHomeomorph ha y C lo hβ hβπ hRC).symm x)
      ((pointUnchangedConeSectorRangeHomeomorph ha y C lo hβ hβπ hRC).symm z) =
      (pointSmoothConformalEDist a y x.1 z.1).toReal := by
  let H := pointUnchangedConeSectorRangeHomeomorph ha y C lo hβ hβπ hRC
  have hx : pointUnchangedConeSectorMap C lo (H.symm x) = x.1 :=
    congrArg Subtype.val (H.apply_symm_apply x)
  have hz : pointUnchangedConeSectorMap C lo (H.symm z) = z.1 :=
    congrArg Subtype.val (H.apply_symm_apply z)
  rw [← hx, ← hz, pointUnchangedConeSectorMap_metric C lo hβπ hRC]

end RepulsiveCoulomb
