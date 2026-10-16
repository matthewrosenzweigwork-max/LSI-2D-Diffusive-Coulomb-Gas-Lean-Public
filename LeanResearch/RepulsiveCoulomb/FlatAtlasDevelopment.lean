module

public import LeanResearch.RepulsiveCoulomb.CompleteLocalIsometryEquiv
public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

@[expose] public section

/-!
SOURCE-ONLY, UNCOMPILED.

Development is constructed, not supplied. A genuine locally Euclidean atlas
with locally constant Euclidean transition motions is the input. Overlap
components need not be connected and their motions may differ. Covering-space
lifting supplies a section of the discrete motion bundle. Evaluation of that
section constructs the global developing map and its local chart formula.

This reusable theorem does not construct the angular-surgery atlas from the
finite sector family. No original-input Bonk--Lang existence claim is made.
The full Euclidean group is used; positive signed Jacobian requires a separate
oriented-atlas specialization. Absolute-Jacobian distortion needs no such step.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- Rigid coordinates carry the discrete topology for monodromy, rather than
the compact-open topology on the group of Euclidean motions. -/
structure DiscreteEuclideanMotion where
  val : ℂ ≃ᵢ ℂ

instance : TopologicalSpace DiscreteEuclideanMotion := ⊥
instance : DiscreteTopology DiscreteEuclideanMotion := ⟨rfl⟩

/-- Actual chart and transition data. `transition i j x` maps chart-j
coordinates to chart-i coordinates near x. These are ordinary atlas cocycle
laws, not global map, global metric, or path-independence hypotheses. -/
structure EuclideanMotionAtlas (X : Type*) [TopologicalSpace X] where
  chart : X → OpenPartialHomeomorph X ℂ
  mem_source : ∀ x, x ∈ (chart x).source
  transition : X → X → X → DiscreteEuclideanMotion
  transition_continuous : ∀ i j,
    ContinuousOn (transition i j) ((chart i).source ∩ (chart j).source)
  transition_self : ∀ i x, x ∈ (chart i).source →
    (transition i i x).val = 1
  transition_comp : ∀ i j k x,
    x ∈ (chart i).source ∩ (chart j).source ∩ (chart k).source →
    (transition i j x).val * (transition j k x).val = (transition i k x).val
  transition_apply : ∀ i j x,
    x ∈ (chart i).source ∩ (chart j).source →
    (transition i j x).val (chart j x) = chart i x

namespace EuclideanMotionAtlas
section Topological
variable {X : Type*} [TopologicalSpace X]

/-- The explicit discrete motion bundle associated to the actual atlas. -/
def motionBundle (A : EuclideanMotionAtlas X) :
    FiberBundleCore X X DiscreteEuclideanMotion where
  baseSet i := (A.chart i).source
  isOpen_baseSet i := (A.chart i).open_source
  indexAt := id
  mem_baseSet_at := A.mem_source
  coordChange i j x v := ⟨v.val * (A.transition i j x).val⟩
  coordChange_self := by
    intro i x hx v
    cases v
    simp [A.transition_self i x hx]
  continuousOn_coordChange := by
    intro i j
    have hc : Continuous
        (fun p : DiscreteEuclideanMotion × DiscreteEuclideanMotion ↦
          (⟨p.2.val * p.1.val⟩ : DiscreteEuclideanMotion)) :=
      continuous_of_discreteTopology
    apply hc.comp_continuousOn (f := fun p : X × DiscreteEuclideanMotion ↦
      (A.transition i j p.1, p.2))
    exact ((A.transition_continuous i j).comp continuous_fst.continuousOn
      (fun p hp ↦ hp.1)).prodMk continuous_snd.continuousOn
  coordChange_comp := by
    intro i j k x hx v
    change DiscreteEuclideanMotion.mk
      ((v.val * (A.transition i j x).val) * (A.transition j k x).val) =
        DiscreteEuclideanMotion.mk (v.val * (A.transition i k x).val)
    rw [mul_assoc, A.transition_comp i j k x hx]

/-- No global development is assumed: covering lifting constructs a function
whose germ at every x is an actual Euclidean motion of the x-chart. -/
theorem exists_developingMap [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (A : EuclideanMotionAtlas X) (x₀ : X) :
    ∃ D : X → ℂ, ∀ x, ∃ e : ℂ ≃ᵢ ℂ,
      D =ᶠ[𝓝 x] (fun y ↦ e (A.chart x y)) := by
  classical
  let Z := A.motionBundle
  have hcov : IsCoveringMap Z.proj :=
    IsCoveringMap.mk Z.proj (fun _ ↦ DiscreteEuclideanMotion)
      (fun x ↦ Z.localTriv x) A.mem_source
  let e₀ : Z.TotalSpace := ⟨x₀, ⟨1⟩⟩
  obtain ⟨S, ⟨_, hS⟩, _⟩ := hcov.existsUnique_continuousMap_lifts
    (ContinuousMap.id X) x₀ e₀ rfl
  have hproj : ∀ x, (S x).proj = x := fun x ↦ congr_fun hS x
  let D : X → ℂ := fun x ↦ (S x).snd.val (A.chart (S x).proj (S x).proj)
  refine ⟨D, fun x ↦ ?_⟩
  let e : ℂ ≃ᵢ ℂ := ((Z.localTriv x) (S x)).2.val
  refine ⟨e, ?_⟩
  have hsource : S x ∈ (Z.localTriv x).source := by
    rw [Z.mem_localTriv_source, hproj x]
    exact A.mem_source x
  have hcoord : ContinuousAt
      (fun y ↦ ((Z.localTriv x) (S y)).2) x :=
    (((Z.localTriv x).toOpenPartialHomeomorph.continuousAt hsource).comp
      S.continuous.continuousAt).snd
  have hevent : ∀ᶠ y in 𝓝 x,
      ((Z.localTriv x) (S y)).2 = ((Z.localTriv x) (S x)).2 :=
    hcoord.eventually ((isOpen_discrete
      {v : DiscreteEuclideanMotion | v = ((Z.localTriv x) (S x)).2}).mem_nhds rfl)
  filter_upwards [hevent, (A.chart x).open_source.mem_nhds (A.mem_source x)]
    with y hy hys
  have hval := congrArg DiscreteEuclideanMotion.val hy
  change (S y).snd.val * (A.transition (S y).proj x (S y).proj).val = e at hval
  rw [hproj y] at hval
  change (S y).snd.val (A.chart (S y).proj (S y).proj) = e (A.chart x y)
  rw [hproj y, ← hval, IsometryEquiv.mul_apply,
    A.transition_apply y x y ⟨A.mem_source y, hys⟩]

/-- A locally developed chart formula proves ordinary continuity and openness;
neither is an input to the development theorem. -/
theorem continuous_isOpenMap_of_local_formula (A : EuclideanMotionAtlas X)
    {D : X → ℂ}
    (hD : ∀ x, ∃ e : ℂ ≃ᵢ ℂ,
      D =ᶠ[𝓝 x] (fun y ↦ e (A.chart x y))) :
    Continuous D ∧ IsOpenMap D := by
  have hmap (x : X) : Filter.map D (𝓝 x) = 𝓝 (D x) := by
    obtain ⟨e, he⟩ := hD x
    calc
      Filter.map D (𝓝 x) = Filter.map (fun y ↦ e (A.chart x y)) (𝓝 x) :=
        Filter.map_congr he
      _ = Filter.map e (Filter.map (A.chart x) (𝓝 x)) := by rw [Filter.map_map]; rfl
      _ = Filter.map e (𝓝 (A.chart x x)) := by
        rw [(A.chart x).map_nhds_eq (A.mem_source x)]
      _ = 𝓝 (e (A.chart x x)) := e.toHomeomorph.map_nhds_eq _
      _ = 𝓝 (D x) := by rw [he.self_of_nhds]
  constructor
  · rw [continuous_iff_continuousAt]
    intro x
    exact (hmap x).le
  · exact isOpenMap_iff_nhds_le.mpr fun x ↦ (hmap x).ge

end Topological

variable {X : Type*}

/-- Actual chart distances transfer to the constructed global map locally. -/
theorem locallyDistancePreserving_of_local_formula [MetricSpace X]
    (A : EuclideanMotionAtlas X)
    (hmetric : ∀ x, ∀ u ∈ (A.chart x).source, ∀ v ∈ (A.chart x).source,
      dist (A.chart x u) (A.chart x v) = dist u v)
    {D : X → ℂ}
    (hD : ∀ x, ∃ e : ℂ ≃ᵢ ℂ,
      D =ᶠ[𝓝 x] (fun y ↦ e (A.chart x y))) :
    LocallyDistancePreserving D := by
  intro x
  obtain ⟨e, he⟩ := hD x
  obtain ⟨U, hUeq, hUopen, hxU⟩ := mem_nhds_iff.mp he
  refine ⟨U ∩ (A.chart x).source, hUopen.inter (A.chart x).open_source,
    ⟨hxU, A.mem_source x⟩, ?_⟩
  intro u hu v hv
  rw [hUeq hu.1, hUeq hv.1, e.dist_eq]
  exact hmetric x u hu.2 v hv.2

/-- Complete simply connected geodesic Euclidean atlases now yield an actual
isometry equivalence. The global map, inverse, openness, injectivity and
surjectivity are outputs, not fields of the input atlas. -/
theorem exists_isometryEquiv [MetricSpace X] [CompleteSpace X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (A : EuclideanMotionAtlas X) (x₀ : X)
    (hmetric : ∀ x, ∀ u ∈ (A.chart x).source, ∀ v ∈ (A.chart x).source,
      dist (A.chart x u) (A.chart x v) = dist u v)
    (hsegment : ∀ x z : X, ∃ γ : Icc (0 : ℝ) 1 → X,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z) :
    Nonempty (X ≃ᵢ ℂ) := by
  letI : Nonempty X := ⟨x₀⟩
  obtain ⟨D, hD⟩ := A.exists_developingMap x₀
  exact ⟨isometryEquivOfLocallyDistancePreservingOpen hsegment
    (A.locallyDistancePreserving_of_local_formula hmetric hD)
    (A.continuous_isOpenMap_of_local_formula hD).2⟩

end EuclideanMotionAtlas
end RepulsiveCoulomb
