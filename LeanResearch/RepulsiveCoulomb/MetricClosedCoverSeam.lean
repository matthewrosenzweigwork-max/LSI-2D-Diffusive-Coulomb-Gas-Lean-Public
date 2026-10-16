import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.UnitInterval

/-! SOURCE-ONLY, UNCOMPILED. A continuous path in a closed two-set cover must
meet the intersection if its endpoints belong to the respective sets. The
crossing is constructed from connectedness, never supplied as a certificate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

 theorem continuousPath_meets_closed_cover_intersection
    {Y : Type*} [TopologicalSpace Y] {S Q : Set Y}
    (hS : IsClosed S) (hQ : IsClosed Q)
    (γ : unitInterval → Y) (hc : Continuous γ)
    (hcover : ∀ t,γ t∈S∪Q) (h0 : γ 0∈S) (h1 : γ 1∈Q) :
    ∃ t : unitInterval,γ t∈S∩Q := by
  have hconn : IsPreconnected (range γ) := (isConnected_range hc).isPreconnected
  obtain ⟨p,⟨t,ht⟩,hp⟩ := isPreconnected_closed_iff.mp hconn S Q hS hQ
    (by rintro p ⟨t,rfl⟩; exact hcover t)
    ⟨γ 0,mem_range_self 0,h0⟩ ⟨γ 1,mem_range_self 1,h1⟩
  exact ⟨t,ht.symm ▸ hp⟩

/-- A purely set-theoretic gluing operation. It asks only for equality on the
actual overlap and jointly surjective source inclusions; metric preservation is
not among the hypotheses or conclusions. -/
theorem exists_map_of_jointly_surjective_injections
    {X A B Y : Type*} (i : A→X) (j : B→X)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hcover : ∀ q,(∃ x,i x=q)∨(∃ z,j z=q)) (f : A→Y) (g : B→Y)
    (hagree : ∀ x z,i x=j z→f x=g z) :
    ∃ H : X→Y,(∀ x,H (i x)=f x) ∧ (∀ z,H (j z)=g z) := by
  classical
  have hex : ∀ q,∃ y,(∀ x,i x=q→f x=y) ∧ (∀ z,j z=q→g z=y) := by
    intro q
    rcases hcover q with ⟨x,rfl⟩ | ⟨z,rfl⟩
    · refine ⟨f x,?_,?_⟩
      · intro x' he
        exact congrArg f (hi he)
      · intro z he
        exact (hagree x z he.symm).symm
    · refine ⟨g z,?_,?_⟩
      · intro x he
        exact hagree x z he
      · intro z' he
        exact congrArg g (hj he)
  let H : X→Y := fun q↦Classical.choose (hex q)
  exact ⟨H,fun x↦((Classical.choose_spec (hex (i x))).1 x rfl).symm,
    fun z↦((Classical.choose_spec (hex (j z))).2 z rfl).symm⟩

end RepulsiveCoulomb
