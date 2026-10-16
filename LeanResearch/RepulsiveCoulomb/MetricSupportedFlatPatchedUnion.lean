module

public import LeanResearch.RepulsiveCoulomb.MetricSupportedFlatPatchCompatibility
public import Mathlib.Data.Set.UnionLift

@[expose] public section

/-! NEW implementation after source loss. Construct the supported union map
from actual patch equivalences and old-map agreement. New-new compatibility
is proved by the recovered geometric compatibility theorem. All distance
conclusions for arbitrary targets are local. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- Old interior together with supported patches centered on the old source. -/
def supportedFlatPatchedSet {ι : Type*} {K : Set ℂ} (H : Set ℂ)
    (q : ι → K) (R : ι → ℝ) : Set ℂ :=
  interior K ∪ ⋃ i, supportedFlatPatch H (q i).1 (R i)

/-- Construct a map on the entire supported union. The supporting set need
not be open: the balls give relatively open patch neighborhoods on the union. -/
theorem exists_supported_flat_patched_union {Y ι : Type*} [MetricSpace Y]
    {K H : Set ℂ} (hK : Convex ℝ K) (hne : (interior K).Nonempty)
    (hH : Convex ℝ H) (hKH : K ⊆ H) (f : K → Y) (hf : Isometry f)
    (q : ι → K) (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (e : ∀ i, supportedFlatPatch H (q i).1 (R i) ≃ᵢ ball (f (q i)) (R i))
    (hold : ∀ i (x : K) (hx : x.1 ∈ supportedFlatPatch H (q i).1 (R i)),
      (e i ⟨x.1, hx⟩).1 = f x) :
    ∃ G : supportedFlatPatchedSet H q R → Y,
      (∀ x : K, ∀ hx : x.1 ∈ supportedFlatPatchedSet H q R,
        G ⟨x.1, hx⟩ = f x) ∧
      ∀ p, ∃ V : Set (supportedFlatPatchedSet H q R), IsOpen V ∧ p ∈ V ∧
        ∀ x ∈ V, ∀ z ∈ V, dist (G x) (G z) = dist x z := by
  classical
  have hecompat := supported_flat_patches_compatible hK hne hH hKH f q R hR e hold
  let W := supportedFlatPatchedSet H q R
  have hWH : W ⊆ H := by
    intro x hx
    rcases hx with hx | hx
    · exact hKH (interior_subset hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact hi.2
  let D : Option ι → Set ℂ := fun o ↦ match o with
    | none => interior K
    | some i => supportedFlatPatch H (q i).1 (R i)
  let g : ∀ o, D o → Y := fun o ↦ match o with
    | none => fun x ↦ f ⟨x.1, interior_subset x.2⟩
    | some i => fun x ↦ (e i x).1
  have hcompat : ∀ i j x (hi : x ∈ D i) (hj : x ∈ D j),
      g i ⟨x, hi⟩ = g j ⟨x, hj⟩ := by
    intro i j x hi hj
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some j => exact (hold j ⟨x, interior_subset hi⟩ hj).symm
    | some i =>
        cases j with
        | none => exact hold i ⟨x, interior_subset hj⟩ hi
        | some j => exact hecompat i j x hi hj
  have hgi (o : Option ι) : Isometry (g o) := by
    apply Isometry.of_dist_eq
    intro x z
    cases o with
    | none => exact hf.dist_eq ⟨x.1, interior_subset x.2⟩ ⟨z.1, interior_subset z.2⟩
    | some i => exact (e i).dist_eq x z
  have hDopen (o : Option ι) : IsOpen ((Subtype.val : W → ℂ) ⁻¹' D o) := by
    cases o with
    | none => exact isOpen_interior.preimage continuous_subtype_val
    | some i =>
        have heq : (Subtype.val : W → ℂ) ⁻¹' D (some i) =
            Subtype.val ⁻¹' ball (q i).1 (R i) := by
          ext x
          exact ⟨fun hx ↦ hx.1, fun hx ↦ ⟨hx, hWH x.2⟩⟩
        rw [heq]
        exact isOpen_ball.preimage continuous_subtype_val
  have hsub : W ⊆ ⋃ o, D o := by
    intro x hx
    rcases hx with hx | hx
    · exact mem_iUnion.mpr ⟨none, hx⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨some i, hi⟩
  let G : W → Y := iUnionLift D g hcompat W hsub
  refine ⟨G, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · exact iUnionLift_of_mem (S := D) (f := g) (hf := hcompat) (hT := hsub)
        (⟨x.1, Or.inl hx⟩ : W) (i := none) hx
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have he := iUnionLift_of_mem (S := D) (f := g) (hf := hcompat) (hT := hsub)
        (⟨x.1, Or.inr (mem_iUnion.mpr ⟨i, hi⟩)⟩ : W) (i := some i) hi
      exact he.trans (hold i x hi)
  · intro p
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hsub p.2)
    let V : Set W := Subtype.val ⁻¹' D i
    refine ⟨V, hDopen i, hi, ?_⟩
    intro x hx z hz
    have hxG : G x = g i ⟨x.1, hx⟩ :=
      iUnionLift_of_mem (S := D) (f := g) (hf := hcompat) (hT := hsub) x hx
    have hzG : G z = g i ⟨z.1, hz⟩ :=
      iUnionLift_of_mem (S := D) (f := g) (hf := hcompat) (hT := hsub) z hz
    rw [hxG, hzG]
    exact (hgi i).dist_eq _ _

end RepulsiveCoulomb
