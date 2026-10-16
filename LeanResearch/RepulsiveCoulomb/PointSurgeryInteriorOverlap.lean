import LeanResearch.RepulsiveCoulomb.PointIncidentOccupiedMotion

/-! SOURCE-ONLY, UNCOMPILED. All actual constructed local model cases have
rigid overlap at points inside a selected open sector. The relevant global
contraction is the same actual allocated sector for both charts. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb
namespace PointFiniteSurgeryLocalModel

variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p q : ℂ} {c : ℝ}
    {ha : ∀ j, 0 ≤ a j} {L : List (PointActualAllocatedSector a y)}
    {hc : 0 < c} {hc1 : c ≤ 1}

/-- Actual listwise disjointness identifies the unique selected sector met
by an overlap point; no uniqueness annotation is part of the model data. -/
theorem sector_index_eq_of_common_openImage
    (hdis : L.Pairwise (fun S E ↦ Disjoint S.openImage E.openImage))
    {i j : Fin L.length} {z : ℂ}
    (hi : z ∈ (L.get i).openImage) (hj : z ∈ (L.get j).openImage) : i = j := by
  by_contra hne
  have hd : Disjoint (L.get i).openImage (L.get j).openImage := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact hdis.rel_get_of_lt h
    · exact (hdis.rel_get_of_lt h).symm
  exact Set.disjoint_left.mp hd hi hj

/-- Each of the three actually constructed chart cases agrees locally with
the same original sector's interior contraction chart, up to one motion. -/
theorem exists_eventuallyEq_sectorInteriorChart
    (D : PointFiniteSurgeryLocalModel ha L p c hc hc1)
    (hdis : L.Pairwise (fun S E ↦ Disjoint S.openImage E.openImage))
    (i : Fin L.length) (hopen : IsOpen (L.get i).openImage) (z : ℂ)
    (hz : z ∈ D.chart.source) (hzi : z ∈ (L.get i).openImage) :
    ∃ e : ℂ ≃ᵢ ℂ, (D.chart : ℂ → ℂ) =ᶠ[𝓝 z]
      (fun w ↦ e (pointActualSectorInteriorOpenChart ha (L.get i) hc hc1 hopen w)) := by
  cases D with
  | sectorInterior j hjo hp =>
      have hzj : z ∈ (L.get j).openImage := hz
      have hji : j = i := sector_index_eq_of_common_openImage hdis hzj hzi
      subst j
      refine ⟨IsometryEquiv.refl ℂ, Filter.Eventually.of_forall ?_⟩
      intro w
      rfl
  | unchanged D =>
      exact False.elim (D.clear i z hz ((L.get i).openImage_subset_range hzi))
  | incident D =>
      exact D.exists_chart_eventuallyEq_sectorInteriorChart i hopen z hz hzi

/-- The genuine atlas overlap germ is now proved for every selected
sector-interior point and every pair of actually constructed local models. -/
theorem exists_rigid_overlap_of_mem_openImage
    (D : PointFiniteSurgeryLocalModel ha L p c hc hc1)
    (E : PointFiniteSurgeryLocalModel ha L q c hc hc1)
    (hdis : L.Pairwise (fun S F ↦ Disjoint S.openImage F.openImage))
    (i : Fin L.length) (hopen : IsOpen (L.get i).openImage) (z : ℂ)
    (hzD : z ∈ D.chart.source) (hzE : z ∈ E.chart.source)
    (hzi : z ∈ (L.get i).openImage) :
    ∃ e : ℂ ≃ᵢ ℂ, (D.chart : ℂ → ℂ) =ᶠ[𝓝 z] (fun w ↦ e (E.chart w)) := by
  obtain ⟨d, hd⟩ := D.exists_eventuallyEq_sectorInteriorChart hdis i hopen z hzD hzi
  obtain ⟨e, he⟩ := E.exists_eventuallyEq_sectorInteriorChart hdis i hopen z hzE hzi
  refine ⟨e.symm.trans d, ?_⟩
  filter_upwards [hd, he] with w hdw hew
  rw [hdw, hew]
  exact (congrArg d (e.symm_apply_apply _)).symm

end PointFiniteSurgeryLocalModel
end RepulsiveCoulomb
