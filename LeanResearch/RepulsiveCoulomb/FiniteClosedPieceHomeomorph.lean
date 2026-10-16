import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Homeomorph.Defs

/-! SOURCE-ONLY, UNCOMPILED. Finite closed-piece gluing with a constructed
inverse. This works on the literal topological neighborhoods (or their
subtypes), with no abstract quotient or assumed global bijection. Apply to
local surgery wedges only after constructing their source and target covers.
Both overlap identities are necessary: agreement of forward values alone does
not rule out accidental identifications of disjoint pieces. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- An actual function, chosen from the pieces that contain its argument. -/
def finiteCoverGlue {ι X Y : Type*} (S : ι → Set X)
    (hcover : ∀ x, ∃ i, x ∈ S i) (f : ι → X → Y) : X → Y :=
  fun x ↦ f (Classical.choose (hcover x)) x

theorem finiteCoverGlue_eq {ι X Y : Type*} (S : ι → Set X)
    (hcover : ∀ x, ∃ i, x ∈ S i) (f : ι → X → Y)
    (hagrees : ∀ i j x, x ∈ S i → x ∈ S j → f i x = f j x)
    {i : ι} {x : X} (hx : x ∈ S i) : finiteCoverGlue S hcover f x = f i x :=
  hagrees _ i x (Classical.choose_spec (hcover x)) hx

theorem finiteCoverGlue_continuous {ι X Y : Type*} [Finite ι]
    [TopologicalSpace X] [TopologicalSpace Y]
    (S : ι → Set X) (hclosed : ∀ i, IsClosed (S i))
    (hcover : ∀ x, ∃ i, x ∈ S i) (f : ι → X → Y)
    (hc : ∀ i, ContinuousOn (f i) (S i))
    (hagrees : ∀ i j x, x ∈ S i → x ∈ S j → f i x = f j x) :
    Continuous (finiteCoverGlue S hcover f) := by
  have hcov : ⋃ i, S i = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    exact hcover x
  apply (locallyFinite_of_finite S).continuous hcov hclosed
  intro i
  exact (hc i).congr (fun x hx ↦ finiteCoverGlue_eq S hcover f hagrees hx)

/-- All inverse, continuity and seam claims for the global pasting are proved
from individual pieces. In a local surgery application X is the actual
neighborhood and Y is the target disk; neither is an abstract glued quotient. -/
def homeomorphOfFiniteClosedPieces {ι X Y : Type*} [Finite ι]
    [TopologicalSpace X] [TopologicalSpace Y]
    (S : ι → Set X) (T : ι → Set Y)
    (hSclosed : ∀ i, IsClosed (S i)) (hTclosed : ∀ i, IsClosed (T i))
    (hScover : ∀ x, ∃ i, x ∈ S i) (hTcover : ∀ y, ∃ i, y ∈ T i)
    (f : ι → X → Y) (g : ι → Y → X)
    (hf : ∀ i, ContinuousOn (f i) (S i))
    (hg : ∀ i, ContinuousOn (g i) (T i))
    (hfmem : ∀ i, MapsTo (f i) (S i) (T i))
    (hgmem : ∀ i, MapsTo (g i) (T i) (S i))
    (hleft : ∀ i x, x ∈ S i → g i (f i x) = x)
    (hright : ∀ i y, y ∈ T i → f i (g i y) = y)
    (hfseam : ∀ i j x, x ∈ S i → x ∈ S j → f i x = f j x)
    (hgseam : ∀ i j y, y ∈ T i → y ∈ T j → g i y = g j y) : X ≃ₜ Y where
  toFun := finiteCoverGlue S hScover f
  invFun := finiteCoverGlue T hTcover g
  left_inv := by
    intro x
    obtain ⟨i, hi⟩ := hScover x
    rw [finiteCoverGlue_eq S hScover f hfseam hi,
      finiteCoverGlue_eq T hTcover g hgseam (hfmem i hi)]
    exact hleft i x hi
  right_inv := by
    intro y
    obtain ⟨i, hi⟩ := hTcover y
    rw [finiteCoverGlue_eq T hTcover g hgseam hi,
      finiteCoverGlue_eq S hScover f hfseam (hgmem i hi)]
    exact hright i y hi
  continuous_toFun := finiteCoverGlue_continuous S hSclosed hScover f hf hfseam
  continuous_invFun := finiteCoverGlue_continuous T hTclosed hTcover g hg hgseam

end RepulsiveCoulomb
