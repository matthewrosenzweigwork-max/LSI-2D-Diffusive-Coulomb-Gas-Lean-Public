import LeanResearch.RepulsiveCoulomb.FiniteClosedPieceHomeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.ContinuousOn

/-! SOURCE-ONLY, UNCOMPILED. The old comparison neighborhood is genuinely
open before gluing. A smaller open target is used only after the continuous
forward paste is constructed. Its source is the preimage of that target
inside the old neighborhood, hence open. Actual inverse-aware piece data
prove the local homeomorphism, without assuming openness of trimmed pieces
or invoking invariance of domain. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def finiteCoverGlueWithin {ι X Y : Type*} (U : Set X) (S : ι → Set X)
    (hcover : ∀ x ∈ U, ∃ i, x ∈ S i) (f : ι → X → Y) (fallback : Y) : X → Y := by
  classical
  exact fun x ↦ if hx : x ∈ U then f (Classical.choose (hcover x hx)) x else fallback

theorem finiteCoverGlueWithin_eq {ι X Y : Type*} (U : Set X) (S : ι → Set X)
    (hcover : ∀ x ∈ U, ∃ i, x ∈ S i) (f : ι → X → Y) (fallback : Y)
    (hagrees : ∀ i j x, x ∈ U → x ∈ S i → x ∈ S j → f i x = f j x)
    {i : ι} {x : X} (hx : x ∈ U) (hxi : x ∈ S i) :
    finiteCoverGlueWithin U S hcover f fallback x = f i x := by
  rw [finiteCoverGlueWithin, dif_pos hx]
  exact hagrees _ i x hx (Classical.choose_spec (hcover x hx)) hxi

theorem finiteCoverGlueWithin_continuousOn
    {ι X Y : Type*} [Finite ι] [TopologicalSpace X] [TopologicalSpace Y]
    (U : Set X) (S : ι → Set X)
    (hclosed : ∀ i, IsClosed {x : U | x.1 ∈ S i})
    (hcover : ∀ x ∈ U, ∃ i, x ∈ S i) (f : ι → X → Y) (fallback : Y)
    (hc : ∀ i, ContinuousOn (f i) (U ∩ S i))
    (hagrees : ∀ i j x, x ∈ U → x ∈ S i → x ∈ S j → f i x = f j x) :
    ContinuousOn (finiteCoverGlueWithin U S hcover f fallback) U := by
  let P : ι → Set U := fun i ↦ {x | x.1 ∈ S i}
  have hPcover : ∀ x : U, ∃ i, x ∈ P i := fun x ↦ hcover x.1 x.2
  let f' : ι → U → Y := fun i x ↦ f i x.1
  have hf' : ∀ i, ContinuousOn (f' i) (P i) := by
    intro i
    exact (hc i).comp continuous_subtype_val.continuousOn (fun x hx ↦ ⟨x.2, hx⟩)
  have hagree' : ∀ i j x, x ∈ P i → x ∈ P j → f' i x = f' j x :=
    fun i j x hi hj ↦ hagrees i j x.1 x.2 hi hj
  have hcont := finiteCoverGlue_continuous P hclosed hPcover f' hf' hagree'
  apply continuousOn_iff_continuous_restrict.mpr
  have heq : (fun x : U ↦ finiteCoverGlueWithin U S hcover f fallback x.1) =
      finiteCoverGlue P hPcover f' := by
    funext x
    obtain ⟨i, hi⟩ := hPcover x
    rw [finiteCoverGlueWithin_eq U S hcover f fallback hagrees x.2 hi,
      finiteCoverGlue_eq P hPcover f' hagree' hi]
  change Continuous (fun x : U ↦ finiteCoverGlueWithin U S hcover f fallback x.1)
  rw [heq]
  exact hcont

/-- The small target inverse is required to lie in the original open U.
For surgery this is supplied by the actual c-times-radius bound. The source
of the resulting chart is then constructed; it is not an input piece union. -/
def openPartialHomeomorphOfFiniteClosedPiecesWithin
    {ι X Y : Type*} [Finite ι] [TopologicalSpace X] [TopologicalSpace Y]
    (U : Set X) (V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (S : ι → Set X) (T : ι → Set Y)
    (hSclosed : ∀ i, IsClosed {x : U | x.1 ∈ S i})
    (hTclosed : ∀ i, IsClosed {y : V | y.1 ∈ T i})
    (hScover : ∀ x ∈ U, ∃ i, x ∈ S i) (hTcover : ∀ y ∈ V, ∃ i, y ∈ T i)
    (f : ι → X → Y) (g : ι → Y → X) (x₀ : X) (y₀ : Y)
    (hf : ∀ i, ContinuousOn (f i) (U ∩ S i))
    (hg : ∀ i, ContinuousOn (g i) (V ∩ T i))
    (hfmem : ∀ i x, x ∈ U → x ∈ S i → f i x ∈ V → f i x ∈ T i)
    (hgmem : ∀ i y, y ∈ V → y ∈ T i → g i y ∈ U ∩ S i)
    (hleft : ∀ i x, x ∈ U → x ∈ S i → f i x ∈ V → g i (f i x) = x)
    (hright : ∀ i y, y ∈ V → y ∈ T i → f i (g i y) = y)
    (hfseam : ∀ i j x, x ∈ U → x ∈ S i → x ∈ S j → f i x = f j x)
    (hgseam : ∀ i j y, y ∈ V → y ∈ T i → y ∈ T j → g i y = g j y) :
    OpenPartialHomeomorph X Y := by
  let F := finiteCoverGlueWithin U S hScover f y₀
  let G := finiteCoverGlueWithin V T hTcover g x₀
  have hF : ContinuousOn F U :=
    finiteCoverGlueWithin_continuousOn U S hSclosed hScover f y₀ hf hfseam
  have hG : ContinuousOn G V :=
    finiteCoverGlueWithin_continuousOn V T hTclosed hTcover g x₀ hg hgseam
  have hFG : ∀ y ∈ V, G y ∈ U ∧ F (G y) = y := by
    intro y hy
    obtain ⟨i, hi⟩ := hTcover y hy
    have hgi : G y = g i y := finiteCoverGlueWithin_eq V T hTcover g x₀ hgseam hy hi
    have hmem := hgmem i y hy hi
    refine ⟨hgi.symm ▸ hmem.1, ?_⟩
    rw [hgi]
    change finiteCoverGlueWithin U S hScover f y₀ (g i y) = y
    rw [finiteCoverGlueWithin_eq U S hScover f y₀ hfseam hmem.1 hmem.2]
    exact hright i y hy hi
  have hGF : ∀ x ∈ U ∩ F ⁻¹' V, G (F x) = x := by
    intro x hx
    obtain ⟨i, hi⟩ := hScover x hx.1
    have hfi : F x = f i x := finiteCoverGlueWithin_eq U S hScover f y₀ hfseam hx.1 hi
    have hfiV : f i x ∈ V := hfi ▸ hx.2
    rw [hfi]
    change finiteCoverGlueWithin V T hTcover g x₀ (f i x) = x
    rw [finiteCoverGlueWithin_eq V T hTcover g x₀ hgseam hfiV
      (hfmem i x hx.1 hi hfiV)]
    exact hleft i x hx.1 hi hfiV
  exact {
    toFun := F
    invFun := G
    source := U ∩ F ⁻¹' V
    target := V
    map_source' := fun x hx ↦ hx.2
    map_target' := fun y hy ↦ ⟨(hFG y hy).1, by
      change F (G y) ∈ V
      rw [(hFG y hy).2]
      exact hy⟩
    left_inv' := fun x hx ↦ hGF x hx
    right_inv' := fun y hy ↦ (hFG y hy).2
    continuousOn_toFun := hF.mono inter_subset_left
    continuousOn_invFun := hG
    open_source := hF.isOpen_inter_preimage hU hV
    open_target := hV
  }

end RepulsiveCoulomb
