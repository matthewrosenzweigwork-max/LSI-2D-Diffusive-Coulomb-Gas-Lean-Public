import LeanResearch.RepulsiveCoulomb.MetricCompactFrontFlatExtension
import LeanResearch.RepulsiveCoulomb.PointConvexFlatClosedEmbedding

/-! ISOLATED SOURCE-ONLY DRAFT, 2026-10-03.

Construct the radius-growth step for a bounded convex sector from actual full
flat charts on its outer circular arc. The sector apex may be singular and is
not required to have a full flat chart. Neither a new map nor a continuation
certificate is supplied. The source cone hypotheses are ordinary Euclidean
set geometry and must be instantiated for an interior angular window.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem flatRadialTruncation_closed {S : Set ℂ} (hS : IsClosed S) (R : ℝ) :
    IsClosed (flatRadialTruncation S R) := hS.inter isClosed_closedBall

theorem flatRadialTruncation_closure_interior {S : Set ℂ}
    (hS : Convex ℝ S) (hclosed : IsClosed S) (R : ℝ)
    (hne : (interior (flatRadialTruncation S R)).Nonempty) :
    closure (interior (flatRadialTruncation S R)) = flatRadialTruncation S R := by
  rw [(flatRadialTruncation_convex hS R).closure_interior_eq_closure_of_nonempty_interior hne,
    (flatRadialTruncation_closed hclosed R).closure_eq]

/-- Literal all-pairs distance-preserving radius extension, including both
new angular side segments and their circular endpoint corners. The old map
is retained at every point by density, including its apex and radial sides. -/
theorem point_exists_closed_radial_front_extension
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P S : Set ℂ} (hP : IsClosed P)
    (hS : Convex ℝ S) (hSclosed : IsClosed S)
    (hscale : ∀ z ∈ S, ∀ t : ℝ, 0 ≤ t → t • z ∈ S)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hne : (interior (flatRadialTruncation S R)).Nonempty)
    (f : flatRadialTruncation S R → P)
    (hf : @Isometry _ P (inferInstance : PseudoEMetricSpace (flatRadialTruncation S R))
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace f)
    (hfront : ∀ z : flatRadialFront S R,
      Nonempty (@MetricFlatDiskChart P (pointRegionMetricSpace ha y P)
        (f ⟨z.1, flatRadialFront_subset S R z.2⟩))) :
    ∃ h : ℝ, 0 < h ∧ h < δ ∧
      ∃ F : flatRadialTruncation S (R + h) → P,
        (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
        ∀ z : flatRadialTruncation S R,
          ∀ hz : z.1 ∈ flatRadialTruncation S (R + h), F ⟨z.1, hz⟩ = f z := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let K := flatRadialTruncation S R
  obtain ⟨ε, hε, W, hW, hKW, hAW, G, hGold, hGlocal⟩ :=
    exists_compact_front_flat_extension (flatRadialTruncation_convex hS R) hne
      (flatRadialFront_compact hSclosed R) (flatRadialFront_subset S R) f hf hfront
  let h := min (ε / 2) (δ / 2)
  have hh : 0 < h := lt_min (half_pos hε) (half_pos hδ)
  have hhε : h ≤ ε := (min_le_left _ _).trans (half_le_self hε.le)
  have hhδ : h < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  let K' := flatRadialTruncation S (R + h)
  let U := interior K'
  have hKK : K ⊆ K' := flatRadialTruncation_mono S (by linarith)
  have hUconv : Convex ℝ U := (flatRadialTruncation_convex hS (R + h)).interior
  have hUne : U.Nonempty := hne.mono (interior_mono hKK)
  have hUW : U ⊆ W := by
    intro z hz
    rcases flatRadialTruncation_interior_enlargement hscale hR hh.le hhε hz with hz | hz
    · exact hKW hz
    · exact hAW hz
  let inclU : U → W := fun z ↦ ⟨z.1, hUW z.2⟩
  have hinclU : Isometry inclU := fun _ _ ↦ rfl
  let G' : U → P := G ∘ inclU
  have hG'local : PointLocallyDistancePreserving a y (fun z ↦ (G' z).1) := by
    intro z
    obtain ⟨V, hV, hz, hd⟩ := hGlocal (inclU z)
    refine ⟨inclU ⁻¹' V, hV.preimage hinclU.continuous, hz, ?_⟩
    intro x hx w hw
    exact (hd (inclU x) hx (inclU w) hw).trans (hinclU.dist_eq x w)
  have hclosure : closure U = K' :=
    flatRadialTruncation_closure_interior hS hSclosed (R + h) hUne
  let incl : K' → closure U := fun z ↦ ⟨z.1, hclosure.symm ▸ z.2⟩
  have hinc : Isometry incl := fun _ _ ↦ rfl
  let F : K' → P := pointFlatClosureMap ha y G' ∘ incl
  have hF : @Isometry K' P (inferInstance : PseudoEMetricSpace K') M.toPseudoEMetricSpace F :=
    (pointFlatClosureMap_isometry ha y hUconv hG'local hP).comp hinc
  let oldincl : K → K' := fun z ↦ ⟨z.1, hKK z.2⟩
  have holdincl : Isometry oldincl := fun _ _ ↦ rfl
  let oldinterior : interior K → K := Set.inclusion interior_subset
  have hdense : DenseRange oldinterior := by
    apply (denseRange_inclusion_iff (interior_subset : interior K ⊆ K)).mpr
    rw [flatRadialTruncation_closure_interior hS hSclosed R hne]
  have hFcont : Continuous (F ∘ oldincl) := by
    have hc : @Continuous K P _ M.toUniformSpace.toTopologicalSpace (F ∘ oldincl) :=
      @Isometry.continuous K P (inferInstance : PseudoEMetricSpace K) M.toPseudoEMetricSpace
        (F ∘ oldincl) (hF.comp holdincl)
    change @Continuous K P _ (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace
      (F ∘ oldincl) at hc
    rwa [pointRegionMetricSpace_topology ha y P] at hc
  have hfcont : Continuous f := by
    have hc : @Continuous K P _ M.toUniformSpace.toTopologicalSpace f :=
      @Isometry.continuous K P (inferInstance : PseudoEMetricSpace K) M.toPseudoEMetricSpace f hf
    change @Continuous K P _ (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace f at hc
    rwa [pointRegionMetricSpace_topology ha y P] at hc
  have heq : F ∘ oldincl = f := hdense.equalizer hFcont hfcont (by
    funext x
    have hxU : x.1 ∈ U := interior_mono hKK x.2
    have hext := pointFlatClosureMap_apply ha y hUconv hG'local (⟨x.1, hxU⟩ : U)
    exact hext.trans (hGold ⟨x.1, interior_subset x.2⟩ (hUW hxU)))
  refine ⟨h, hh, hhδ, F, ?_, ?_⟩
  · intro x z
    exact @Isometry.dist_eq K' P _ M.toPseudoMetricSpace F hF x z
  · intro z hz
    exact congrFun heq z

end RepulsiveCoulomb
