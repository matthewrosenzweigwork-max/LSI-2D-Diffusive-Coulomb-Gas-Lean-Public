module

public import LeanResearch.RepulsiveCoulomb.LocalIsometryGlobalization
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Connected.Clopen

@[expose] public section

/-! Surjectivity requires genuine additional hypotheses: a complete nonempty
source and an actually open map. Completeness closes the isometric image;
openness opens it; connectedness of ℂ makes it all of ℂ. This file does not
construct a flat metric, atlas, global developing map, or Bonk--Lang bound. -/
noncomputable section
open Set
namespace RepulsiveCoulomb
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]

/-- A complete nonempty source has no proper open isometric image in ℂ. -/
theorem surjective_of_isometry_isOpenMap {F : X → ℂ}
    (hF : Isometry F) (hopen : IsOpenMap F) : Function.Surjective F := by
  have hclopen : IsClopen (range F) :=
    ⟨hF.isClosedEmbedding.isClosed_range, hopen.isOpen_range⟩
  exact Set.range_eq_univ.mp (hclopen.eq_univ (Set.range_nonempty F))

/-- Globalize the locally distance-preserving open map, then use complete plus
open image to prove actual surjectivity. -/
theorem surjective_of_locallyDistancePreserving_isOpenMap {F : X → ℂ}
    (hsegment : ∀ x z : X, ∃ γ : Icc (0 : ℝ) 1 → X,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z)
    (hF : LocallyDistancePreserving F) (hopen : IsOpenMap F) :
    Function.Surjective F :=
  surjective_of_isometry_isOpenMap (isometry_of_locallyDistancePreserving hsegment hF) hopen

/-- The resulting isometry equivalence has exactly the given map as its forward
function. Its inverse is constructed from the proved bijectivity. -/
def isometryEquivOfLocallyDistancePreservingOpen {F : X → ℂ}
    (hsegment : ∀ x z : X, ∃ γ : Icc (0 : ℝ) 1 → X,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z)
    (hF : LocallyDistancePreserving F) (hopen : IsOpenMap F) : X ≃ᵢ ℂ :=
  { Equiv.ofBijective F
      ⟨(isometry_of_locallyDistancePreserving hsegment hF).injective,
        surjective_of_locallyDistancePreserving_isOpenMap hsegment hF hopen⟩ with
    isometry_toFun := isometry_of_locallyDistancePreserving hsegment hF }

@[simp] theorem isometryEquivOfLocallyDistancePreservingOpen_apply {F : X → ℂ}
    (hsegment : ∀ x z : X, ∃ γ : Icc (0 : ℝ) 1 → X,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z)
    (hF : LocallyDistancePreserving F) (hopen : IsOpenMap F) (x : X) :
    isometryEquivOfLocallyDistancePreservingOpen hsegment hF hopen x = F x := rfl

/-- Exact midpoints are a constructive source of the minimizing segments, while
completeness, nonemptiness, and openness remain explicit at the equivalence step. -/
def isometryEquivOfLocallyDistancePreservingOpenMidpoints {F : X → ℂ}
    (hmid : ∀ x z : X, ∃ p, dist x p = dist x z / 2 ∧ dist p z = dist x z / 2)
    (hF : LocallyDistancePreserving F) (hopen : IsOpenMap F) : X ≃ᵢ ℂ :=
  isometryEquivOfLocallyDistancePreservingOpen (exists_geodesic_of_exact_midpoints hmid) hF hopen

end RepulsiveCoulomb
