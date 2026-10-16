import LeanResearch.RepulsiveCoulomb.PointSurgeryComplementLocalMetric
import LeanResearch.RepulsiveCoulomb.ComplexCenteredMetricRigidity
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! SOURCE-ONLY, UNCOMPILED. Actual all-model rigid overlap away from the
selected closed sectors, including all artificial complement subdivision
seams. The charts are restricted to a geometrically proved open complement;
centered local old metric equalities then give genuine Euclidean rigidity. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}

/-- Open unchanged region determined by the actual selected closed images. -/
def pointSelectedRangeComplement (L : List (PointActualAllocatedSector a y)) : Set ℂ :=
  ⋂ i : Fin L.length, (range (L.get i).map)ᶜ

theorem mem_pointSelectedRangeComplement (L : List (PointActualAllocatedSector a y))
    (x : ℂ) : x ∈ pointSelectedRangeComplement L ↔
      ∀ i : Fin L.length, x ∉ range (L.get i).map := by
  simp only [pointSelectedRangeComplement, mem_iInter, mem_compl_iff]

theorem pointSelectedRangeComplement_isOpen (ha : ∀ j, 0 ≤ a j)
    (L : List (PointActualAllocatedSector a y)) : IsOpen (pointSelectedRangeComplement L) :=
  isOpen_iInter_of_finite (fun i ↦ ((L.get i).isClosedEmbedding ha).isClosed_range.isOpen_compl)

namespace PointFiniteSurgeryLocalModel
variable {p q : ℂ} {c : ℝ} {ha : ∀ j, 0 ≤ a j}
    {L : List (PointActualAllocatedSector a y)} {hc : 0 < c} {hc1 : c ≤ 1}

/-- This is the exact desired rigid-overlap germ for every unselected point,
proved from the actual finite branch provenance rather than a metric field. -/
theorem exists_rigid_overlap_of_no_selected_range
    (D : PointFiniteSurgeryLocalModel ha L p c hc hc1)
    (E : PointFiniteSurgeryLocalModel ha L q c hc hc1)
    (x : ℂ) (hxD : x ∈ D.chart.source) (hxE : x ∈ E.chart.source)
    (hclear : ∀ i : Fin L.length, x ∉ range (L.get i).map) :
    ∃ e : ℂ ≃ᵢ ℂ, (D.chart : ℂ → ℂ) =ᶠ[𝓝 x] (fun z ↦ e (E.chart z)) := by
  let U := pointSelectedRangeComplement L
  have hU : IsOpen U := pointSelectedRangeComplement_isOpen ha L
  have hxU : x ∈ U := (mem_pointSelectedRangeComplement L x).mpr hclear
  let D' := D.chart.restrOpen U hU
  let E' := E.chart.restrOpen U hU
  let T := E'.symm.trans D'
  have hlocal : ∀ v ∈ T.source, ∀ᶠ w in 𝓝 v, dist (T v) (T w) = dist v w := by
    intro v hv
    have hvE : v ∈ E.chart.target := hv.1.1
    have hvEU : E.chart.symm v ∈ U := hv.1.2
    have hvD : E.chart.symm v ∈ D.chart.source := hv.2.1
    have hvc : ∀ i : Fin L.length, E.chart.symm v ∉ range (L.get i).map :=
      (mem_pointSelectedRangeComplement L _).mp hvEU
    have hD := (E.chart.symm.continuousAt hvE).eventually
      (D.centered_metric_of_no_selected_range (E.chart.symm v) hvD hvc)
    have hE := (E.chart.symm.continuousAt hvE).eventually
      (E.centered_metric_of_no_selected_range (E.chart.symm v) (E.chart.map_target hvE) hvc)
    filter_upwards [hD, hE, E.chart.open_target.mem_nhds hvE] with w hwD hwE hwT
    change dist (D.chart (E.chart.symm v)) (D.chart (E.chart.symm w)) = dist v w
    rw [hwD, ← hwE, E.chart.right_inv hvE, E.chart.right_inv hwT]
  have hxE' : x ∈ E'.source := ⟨hxE, hxU⟩
  have hxT : E.chart x ∈ T.source := by
    change E.chart x ∈ E'.target ∧ E.chart.symm (E.chart x) ∈ D'.source
    refine ⟨E'.map_source hxE', ?_⟩
    rw [E.chart.left_inv hxE]
    exact ⟨hxD, hxU⟩
  obtain ⟨e, he⟩ := exists_complex_isometry_germ_of_centered_local_dist_eq T hlocal (E.chart x) hxT
  have hcomp := (E.chart.continuousAt hxE).eventually he
  refine ⟨e, ?_⟩
  filter_upwards [hcomp, E.chart.open_source.mem_nhds hxE] with z hz hzE
  change D.chart (E.chart.symm (E.chart z)) = e (E.chart z) at hz
  simpa only [E.chart.left_inv hzE] using hz

end PointFiniteSurgeryLocalModel
end RepulsiveCoulomb
