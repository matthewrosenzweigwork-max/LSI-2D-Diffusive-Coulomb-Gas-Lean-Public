import LeanResearch.RepulsiveCoulomb.PointRadialChartSideTransport
import LeanResearch.RepulsiveCoulomb.PointExteriorTwoRayArgument

/-! Actual exterior observation points approaching a two-ray boundary
vertex through its chart. Which sector is exterior is derived from the actual
Jordan partition and closure incidences, with both possibilities retained.
Selecting the positively oriented one still requires the local orientation
adapter; that fact is not silently assumed here. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem pointRadialChart_observer_tendsto {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) {p : X} (hp : p ∈ e.source) (hep : e p = 0)
    (φ : ℝ) : Tendsto (fun ε : ℝ => e.symm (pointRadialSectorPoint ε φ)) (𝓝 0) (𝓝 p) := by
  have h0t : (0 : ℂ) ∈ e.target := hep ▸ e.mapsTo hp
  have he0 : e.symm 0 = p := by rw [← hep, e.left_inv hp]
  have hpath : Continuous (fun ε : ℝ => pointRadialSectorPoint ε φ) := by
    unfold pointRadialSectorPoint
    fun_prop
  have hpathT : Tendsto (fun ε : ℝ => pointRadialSectorPoint ε φ) (𝓝 0) (𝓝 0) := by
    simpa only [pointRadialSectorPoint_zero] using hpath.tendsto 0
  have he := (e.symm.continuousOn.continuousAt (e.open_target.mem_nhds h0t)).tendsto.comp hpathT
  simpa only [he0, Function.comp_def] using he

/-- The observers are proved to lie in the actual exterior set V, rather
than merely in a formally labelled angular interval. Both side alternatives
are kept until global positive orientation has been related to the chart. -/
theorem exists_pointRadialChart_actual_exterior_observers {X : Type*} [TopologicalSpace X]
    {C U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hd : Disjoint U V)
    (hcover : U ∪ V = Cᶜ) {p : X} (hpU : p ∈ closure U) (hpV : p ∈ closure V)
    (e : OpenPartialHomeomorph X ℂ) (hp : p ∈ e.source) (hep : e p = 0)
    {R θ : ℝ} (hR : 0 < R) (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (hball : ball (0 : ℂ) R ⊆ e.target)
    (hboundary : ∀ z ∈ ball (0 : ℂ) R,
      e.symm z ∈ C ↔ z ∈ pointDiskRay R 0 ∪ pointDiskRay R θ) :
    (∃ φ : ℝ, θ < φ ∧ φ < 2 * Real.pi ∧
      (∀ ε ∈ Ioo (0 : ℝ) R, e.symm (pointRadialSectorPoint ε φ) ∈ V) ∧
      Tendsto (fun ε : ℝ => e.symm (pointRadialSectorPoint ε φ)) (𝓝[>] 0) (𝓝 p)) ∨
    (∃ φ : ℝ, 0 < φ ∧ φ < θ ∧
      (∀ ε ∈ Ioo (0 : ℝ) R, e.symm (pointRadialSectorPoint ε φ) ∈ V) ∧
      Tendsto (fun ε : ℝ => e.symm (pointRadialSectorPoint ε φ)) (𝓝[>] 0) (𝓝 p)) := by
  rcases pointRadialChart_region_side_choice hU hV hd hcover hpU hpV e hp hep
    hR hθ0 hθ2 hball hboundary with hside | hside
  · left
    let φ := (θ + 2 * Real.pi) / 2
    have hφl : θ < φ := by dsimp [φ]; linarith
    have hφr : φ < 2 * Real.pi := by dsimp [φ]; linarith
    refine ⟨φ, hφl, hφr, ?_,
      (pointRadialChart_observer_tendsto e hp hep φ).mono_left nhdsWithin_le_nhds⟩
    intro ε hε
    exact hside.2 ⟨(ε, φ), ⟨hε, ⟨hφl, hφr⟩⟩, rfl⟩
  · right
    let φ := θ / 2
    have hφl : 0 < φ := by dsimp [φ]; positivity
    have hφr : φ < θ := by dsimp [φ]; linarith
    refine ⟨φ, hφl, hφr, ?_,
      (pointRadialChart_observer_tendsto e hp hep φ).mono_left nhdsWithin_le_nhds⟩
    intro ε hε
    exact hside.1 ⟨(ε, φ), ⟨hε, ⟨hφl, hφr⟩⟩, rfl⟩

end RepulsiveCoulomb
