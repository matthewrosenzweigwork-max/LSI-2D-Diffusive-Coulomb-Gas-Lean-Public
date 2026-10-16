module

public import LeanResearch.RepulsiveCoulomb.DevelopedPathMetricTopology
public import LeanResearch.RepulsiveCoulomb.CompleteLocalIsometryEquiv
public import LeanResearch.RepulsiveCoulomb.EuclideanChartTransition
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

@[expose] public section

/-!
SOURCE-ONLY, UNCOMPILED. A sufficiently small straight coordinate segment is
lifted through an actual chart, giving the missing local upper bound for the
new intrinsic distance. The opposite inequality follows from Euclidean
endpoint distance ≤ developed variation of EVERY competitor. Completeness and
NEW minimizing segments are then proved upstream, so the existing complete
local-isometry theorem can be invoked without circularity.
-/
noncomputable section
open Set Filter Metric
open scoped ENNReal NNReal Topology
namespace RepulsiveCoulomb
variable {X : Type*} [MetricSpace X]

/-- Local chart formula alone yields local equality of the actual path
infimum with Euclidean endpoint distance. No injectivity of D is assumed. -/
theorem developedPathEDist_locally_eq (D : X → ℂ)
    (C : X → OpenPartialHomeomorph X ℂ) (hC : ∀ x, x ∈ (C x).source)
    (hformula : ∀ x, ∃ e : ℂ ≃ᵢ ℂ,
      D =ᶠ[𝓝 x] (fun y ↦ e (C x y))) :
    ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ u ∈ V, ∀ v ∈ V, developedPathEDist D u v = edist (D u) (D v) := by
  intro x
  obtain ⟨e, he⟩ := hformula x
  obtain ⟨U, hUeq, hUopen, hxU⟩ := _root_.mem_nhds_iff.mp he
  let W := (C x).target ∩ (C x).symm ⁻¹' U
  have hW : IsOpen W := (C x).isOpen_inter_preimage_symm hUopen
  have hxW : C x x ∈ W := by
    exact ⟨(C x).map_source (hC x), by simpa only [Set.mem_preimage, (C x).left_inv (hC x)] using hxU⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW _ hxW
  let V := (C x).source ∩ (C x) ⁻¹' ball (C x x) r
  have hV : IsOpen V := (C x).isOpen_inter_preimage isOpen_ball
  have hxV : x ∈ V := ⟨hC x, by simpa only [Set.mem_preimage, mem_ball, dist_self] using hr⟩
  refine ⟨V, hV, hxV, fun u hu v hv ↦ le_antisymm ?_ (developed_edist_le_pathEDist D u v)⟩
  let L : ℝ → ℂ := AffineMap.lineMap (C x u) (C x v)
  have hL (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : L t ∈ W :=
    hball ((convex_ball (C x x) r).lineMap_mem hu.2 hv.2 ht)
  let f : ℝ → X := (C x).symm ∘ L
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) :=
    (C x).symm.continuousOn.comp
      (AffineMap.lineMap_continuous.continuousOn) (fun t ht ↦ (hL t ht).1)
  have hf0 : f 0 = u := by simp only [f, L, Function.comp_apply,
    AffineMap.lineMap_apply_zero, (C x).left_inv hu.1]
  have hf1 : f 1 = v := by simp only [f, L, Function.comp_apply,
    AffineMap.lineMap_apply_one, (C x).left_inv hv.1]
  let γ := MetricRegionLengthPath.ofContinuousOn f hfc hf0 hf1
    (fun _ _ ↦ mem_univ _)
  have hγ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ.toFun t = f t := by
    dsimp only [γ, MetricRegionLengthPath.ofContinuousOn]
    exact IccExtend_of_mem _ _ ht
  have hdeveloped : EqOn (D ∘ γ.toFun) (e ∘ L) (Icc (0 : ℝ) 1) := by
    intro t ht
    change D (γ.toFun t) = e (L t)
    rw [hγ t ht]
    change D ((C x).symm (L t)) = e (L t)
    rw [hUeq (hL t ht).2]
    exact congrArg e ((C x).right_inv (hL t ht).1)
  have hLip : LipschitzWith (nndist (C x u) (C x v)) (e ∘ L) := by
    simpa only [one_mul] using e.isometry.lipschitz.comp
      (lipschitzWith_lineMap (C x u) (C x v))
  have hvar := hLip.lipschitzOnWith.comp_eVariationOn_le
    (g := id) (s := Icc (0 : ℝ) 1) (fun t ht ↦ mem_univ t)
  have hbound : developedPathLength D γ ≤ edist (C x u) (C x v) := by
    unfold developedPathLength
    rw [eVariationOn.eq_of_eqOn hdeveloped]
    simpa only [Function.comp_id, eVariationOn_id_Icc, sub_zero,
      ENNReal.ofReal_one, mul_one, coe_nnreal_ennreal_nndist] using hvar
  have huU : u ∈ U := by
    have h := (hball hu.2).2
    simpa only [Set.mem_preimage, (C x).left_inv hu.1] using h
  have hvU : v ∈ U := by
    have h := (hball hv.2).2
    simpa only [Set.mem_preimage, (C x).left_inv hv.1] using h
  have heq : edist (C x u) (C x v) = edist (D u) (D v) := by
    rw [hUeq huU, hUeq hvU, e.edist_eq]
  exact (developedPathEDist_le_length D γ).trans (hbound.trans_eq heq)

/-- Constructed local Euclidean equality becomes a local-isometry statement
only AFTER the new metric's topology has been identified. -/
theorem developedPathMetricSpace_locallyDistancePreserving
    (D : X → ℂ) (hD : Continuous D) (c : ℝ≥0) (hc : 0 < c)
    (hsegment : HasMinimizingSegments X)
    (hlower : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ u ∈ U, ∀ v ∈ U, (c : ℝ≥0∞) * edist u v ≤ edist (D u) (D v))
    (hupper : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ u ∈ U, ∀ v ∈ U, dist (D u) (D v) ≤ dist u v)
    (C : X → OpenPartialHomeomorph X ℂ) (hC : ∀ x, x ∈ (C x).source)
    (hformula : ∀ x, ∃ e : ℂ ≃ᵢ ℂ, D =ᶠ[𝓝 x] (fun y ↦ e (C x y))) :
    @LocallyDistancePreserving X
      (developedPathMetricSpace D hD c hc hsegment hlower hupper) D := by
  intro x
  obtain ⟨V, hV, hxV, heq⟩ := developedPathEDist_locally_eq D C hC hformula x
  refine ⟨V, ?_, hxV, ?_⟩
  · change @IsOpen X
      (developedPathMetricSpace D hD c hc hsegment hlower hupper).toUniformSpace.toTopologicalSpace V
    rwa [developedPathMetricSpace_topology]
  · intro u hu v hv
    change dist (D u) (D v) = (developedPathEDist D u v).toReal
    rw [heq u hu v hv, ← dist_edist]

/-- Full conditional globalization from genuine local chart formulas and
local c/1 bounds. The global distance identity and bijectivity are OUTPUTS.
This theorem still awaits instantiation by the actual finite-sector atlas. -/
theorem developedPathMetricSpace_isometry_bijective [ProperSpace X] [Nonempty X]
    (D : X → ℂ) (hD : Continuous D) (hopen : IsOpenMap D)
    (c : ℝ≥0) (hc : 0 < c) (hsegment : HasMinimizingSegments X)
    (hlower : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ u ∈ U, ∀ v ∈ U, (c : ℝ≥0∞) * edist u v ≤ edist (D u) (D v))
    (hupper : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ u ∈ U, ∀ v ∈ U, dist (D u) (D v) ≤ dist u v)
    (C : X → OpenPartialHomeomorph X ℂ) (hC : ∀ x, x ∈ (C x).source)
    (hformula : ∀ x, ∃ e : ℂ ≃ᵢ ℂ, D =ᶠ[𝓝 x] (fun y ↦ e (C x y))) :
    Function.Bijective D ∧
      (∀ x z, developedPathEDist D x z = edist (D x) (D z)) ∧
      ∀ x z, (c : ℝ) * dist x z ≤ dist (D x) (D z) ∧
        dist (D x) (D z) ≤ dist x z := by
  let oldMetric : MetricSpace X := inferInstance
  let d := @developedPathMetricSpace X oldMetric D hD c hc hsegment hlower hupper
  letI : MetricSpace X := oldMetric
  have hcomplete := developedPathMetricSpace_complete D hD c hc hsegment hlower hupper
  have hgeod := developedPathMetricSpace_hasMinimizingSegments D hD c hc hsegment hlower hupper
  have hlocal := developedPathMetricSpace_locallyDistancePreserving
    D hD c hc hsegment hlower hupper C hC hformula
  have hopen' : @IsOpenMap X ℂ d.toUniformSpace.toTopologicalSpace inferInstance D := by
    change @IsOpenMap X ℂ
      (developedPathMetricSpace D hD c hc hsegment hlower hupper).toUniformSpace.toTopologicalSpace
      inferInstance D
    rwa [developedPathMetricSpace_topology]
  let E : @IsometryEquiv X ℂ d.toPseudoEMetricSpace inferInstance :=
    @isometryEquivOfLocallyDistancePreservingOpen X d hcomplete inferInstance
      D hgeod hlocal hopen'
  have heq (x z : X) : developedPathEDist D x z = edist (D x) (D z) := by
    have hE := @IsometryEquiv.edist_eq X ℂ d.toPseudoEMetricSpace inferInstance E x z
    change edist (D x) (D z) = developedPathEDist D x z at hE
    exact hE.symm
  refine ⟨@IsometryEquiv.bijective X ℂ d.toPseudoEMetricSpace inferInstance E, heq, ?_⟩
  intro x z
  have h := developedPathEDist_toReal_bounds D c hsegment hlower hupper x z
  rwa [heq x z, ← dist_edist] at h

end RepulsiveCoulomb
