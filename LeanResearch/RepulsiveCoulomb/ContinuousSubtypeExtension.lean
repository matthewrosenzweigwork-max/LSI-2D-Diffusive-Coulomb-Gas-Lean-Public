import Mathlib.Topology.ContinuousOn

/-! SOURCE-ONLY, UNCOMPILED. Extend an actual continuous map on a literal
subtype by an arbitrary fixed outside value. Continuity is asserted only on
the original domain or a proved subset; no ambient extension is assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def continuousSubtypeExtension {X Y : Type*} (s : Set X) (f : s → Y) (fallback : Y) : X → Y := by
  classical
  exact fun x ↦ if hx : x ∈ s then f ⟨x, hx⟩ else fallback

theorem continuousSubtypeExtension_eq {X Y : Type*} (s : Set X) (f : s → Y) (fallback : Y)
    {x : X} (hx : x ∈ s) : continuousSubtypeExtension s f fallback x = f ⟨x, hx⟩ := by
  classical
  exact dif_pos hx

theorem continuousSubtypeExtension_continuousOn
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (s : Set X) (f : s → Y) (fallback : Y) (hf : Continuous f) :
    ContinuousOn (continuousSubtypeExtension s f fallback) s := by
  apply continuousOn_iff_continuous_restrict.mpr
  have heq : (fun x : s ↦ continuousSubtypeExtension s f fallback x.1) = f := by
    funext x
    exact continuousSubtypeExtension_eq s f fallback x.2
  change Continuous (fun x : s ↦ continuousSubtypeExtension s f fallback x.1)
  rw [heq]
  exact hf

end RepulsiveCoulomb
