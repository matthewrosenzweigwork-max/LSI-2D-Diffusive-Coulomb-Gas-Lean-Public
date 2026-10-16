module

public import LeanResearch.RepulsiveCoulomb.FlatAtlasDevelopment
public import Mathlib.Analysis.Normed.Affine.MazurUlam
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Construct the discrete transition cocycle from
actual locally rigid chart overlaps. Neither a cocycle nor path independence
nor a global developing map is a premise. The transition may vary between
components of the same overlap. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

@[ext] theorem DiscreteEuclideanMotion.ext {e f : DiscreteEuclideanMotion}
    (h : e.val = f.val) : e = f := by
  cases e
  cases f
  cases h
  rfl

/-- Global Euclidean isometries agreeing as germs are equal. Mazur--Ulam is
used only to make them affine; an open neighborhood spans the affine plane. -/
theorem euclideanIsometryEquiv_eq_of_eventuallyEq {e f : ℂ ≃ᵢ ℂ} {z : ℂ}
    (h : (e : ℂ → ℂ) =ᶠ[𝓝 z] f) : e = f := by
  obtain ⟨U, hUeq, hUopen, hzU⟩ := mem_nhds_iff.mp h
  have heq : e.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap =
      f.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap :=
    AffineMap.ext_on (hUopen.affineSpan_eq_top ⟨z, hzU⟩) hUeq
  ext w
  exact congrArg (fun k : ℂ →ᵃ[ℝ] ℂ ↦ k w) heq

/-- Germ equality can be tested after any actual open chart containing x. -/
theorem euclideanIsometryEquiv_eq_of_chart_germ
    {X : Type*} [TopologicalSpace X] (C : OpenPartialHomeomorph X ℂ)
    {x : X} (hx : x ∈ C.source) {e f : ℂ ≃ᵢ ℂ}
    (h : (fun y ↦ e (C y)) =ᶠ[𝓝 x] (fun y ↦ f (C y))) : e = f := by
  apply euclideanIsometryEquiv_eq_of_eventuallyEq (z := C x)
  rw [← C.map_nhds_eq hx]
  exact h

/-- A genuine flat coordinate atlas: ordinary disk charts and actual locally
rigid overlap equations are sufficient. The discrete cocycle is constructed. -/
def euclideanMotionAtlasOfLocalRigidOverlaps
    {X : Type*} [TopologicalSpace X]
    (C : X → OpenPartialHomeomorph X ℂ)
    (hC : ∀ x, x ∈ (C x).source)
    (hrigid : ∀ i j x, x ∈ (C i).source ∩ (C j).source →
      ∃ e : ℂ ≃ᵢ ℂ, (C i : X → ℂ) =ᶠ[𝓝 x] (fun y ↦ e (C j y))) :
    EuclideanMotionAtlas X := by
  classical
  let T : X → X → X → DiscreteEuclideanMotion := fun i j x ↦
    if hx : x ∈ (C i).source ∩ (C j).source then
      ⟨Classical.choose (hrigid i j x hx)⟩ else ⟨1⟩
  have hT (i j x : X) (hx : x ∈ (C i).source ∩ (C j).source) :
      (C i : X → ℂ) =ᶠ[𝓝 x] (fun y ↦ (T i j x).val (C j y)) := by
    simpa only [T, dif_pos hx] using Classical.choose_spec (hrigid i j x hx)
  refine {
    chart := C
    mem_source := hC
    transition := T
    transition_continuous := ?_
    transition_self := ?_
    transition_comp := ?_
    transition_apply := ?_
  }
  · intro i j x hx
    have hconstant : T i j =ᶠ[𝓝 x] (fun _ ↦ T i j x) := by
      filter_upwards [eventually_eventuallyEq_nhds.mpr (hT i j x hx),
        ((C i).open_source.inter (C j).open_source).mem_nhds hx]
        with y hy hys
      apply DiscreteEuclideanMotion.ext
      exact euclideanIsometryEquiv_eq_of_chart_germ (C j) hys.2
        ((hT i j y hys).symm.trans hy)
    exact (continuousAt_const.congr_of_eventuallyEq hconstant).continuousWithinAt
  · intro i x hx
    apply euclideanIsometryEquiv_eq_of_chart_germ (C i) hx
    simpa only [IsometryEquiv.coe_one, id_eq] using (hT i i x ⟨hx, hx⟩).symm
  · intro i j k x hx
    apply euclideanIsometryEquiv_eq_of_chart_germ (C k) hx.2
    filter_upwards [hT i j x hx.1, hT j k x ⟨hx.1.2, hx.2⟩,
      hT i k x ⟨hx.1.1, hx.2⟩] with y hij hjk hik
    change (T i j x).val ((T j k x).val (C k y)) = (T i k x).val (C k y)
    rw [← hjk, ← hij, hik]
  · intro i j x hx
    exact (hT i j x hx).self_of_nhds.symm

/-- The nonsmuggled atlas-to-development endpoint. The only input maps are
local chart partial homeomorphisms, with locally rigid coordinate overlaps. -/
theorem exists_development_of_localRigidOverlaps
    {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X]
    (C : X → OpenPartialHomeomorph X ℂ) (hC : ∀ x, x ∈ (C x).source)
    (hrigid : ∀ i j x, x ∈ (C i).source ∩ (C j).source →
      ∃ e : ℂ ≃ᵢ ℂ, (C i : X → ℂ) =ᶠ[𝓝 x] (fun y ↦ e (C j y)))
    (x₀ : X) :
    ∃ D : X → ℂ, Continuous D ∧ IsOpenMap D ∧
      ∀ x, ∃ e : ℂ ≃ᵢ ℂ, D =ᶠ[𝓝 x] (fun y ↦ e (C x y)) := by
  let A := euclideanMotionAtlasOfLocalRigidOverlaps C hC hrigid
  obtain ⟨D, hD⟩ := A.exists_developingMap x₀
  exact ⟨D, (A.continuous_isOpenMap_of_local_formula hD).1,
    (A.continuous_isOpenMap_of_local_formula hD).2, hD⟩

end RepulsiveCoulomb
