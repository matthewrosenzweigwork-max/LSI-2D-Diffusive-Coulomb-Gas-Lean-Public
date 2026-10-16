import LeanResearch.RepulsiveCoulomb.PointRetainedApexUnorientedChart
import LeanResearch.RepulsiveCoulomb.PointRetainedSectorPassingChart
import LeanResearch.RepulsiveCoulomb.PointRetainedApexBudgetTransport
import LeanResearch.RepulsiveCoulomb.PointTranslatedStripRetainedGerms

/-!
SOURCE-ONLY, NOT COMPILED. Explicit all-point geometric characterization of the
GENERAL Finsupp nu+beta*delta_p. The newly exposed charts and their coefficient
identities are constructed by the actual-sector modules, not assumed.

This is an assembly theorem AFTER global contact/topology: the literal cut
identity, frontier carrier, and old-interior status of nonapex free-ray points
are explicit remaining geometric inputs. It is NOT a proof of those inputs and
is not advertised as a complete supplied-sector removal theorem.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointRetainedApex_all_point_geometric_coefficients
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {P Q : Set ℂ} (hP : IsClosed P) (hS : IsClosed (range σ)) (hσP : ∀ x, σ x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hremain : β < C.flatPhysicalWidth)
    (hpfront : σ (flatLinkSectorApex hβ.le) ∈ frontier P)
    {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ < C.radius)
    (hfront : σ (flatLinkSectorDiskInclusion
      (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0)) ∈ frontier P)
    (ν : ℂ →₀ ℝ)
    (hνoff : ∀ x, x ∉ P → ν x = 0)
    (hνint : ∀ x ∈ interior P, ν x = -Real.pi*coalescedPointExponent a y x)
    (hνboundary : ∀ x ∈ frontier P, ∃ D : PointRetainedConeNeighborhood a y P x,
      ν x = Real.pi-D.flatPhysicalWidth ∧ D.Admissible)
    (hclean : ∀ x ∈ range σ \
      range (fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u)), ν x = 0)
    (hQ : Q = P \ (range σ \
      range (fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u))))
    (hQclosure : closure (P \ range σ) = Q)
    (hQfront : frontier Q =
      range (fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u)) ∪ (frontier P \ range σ))
    (hTopInterior : ∀ r : NNReal, 0 < (r:ℝ) →
      σ (retainedApexUpperSource hβ.le hβπ r) ∈ interior P) :
    let p := σ (flatLinkSectorApex hβ.le)
    let ν' := retainedApexCurvature ν p β
    (∀ x, x ∉ Q → ν' x = 0) ∧
    (∀ x ∈ interior Q, ν' x = -Real.pi*coalescedPointExponent a y x) ∧
    (∀ x ∈ frontier Q, ∃ E : PointRetainedConeNeighborhood a y Q x,
      ν' x = Real.pi-E.flatPhysicalWidth ∧ E.Admissible) := by
  let p := σ (flatLinkSectorApex hβ.le)
  have hpnot : p ∉ interior P := hpfront.2
  let T := range (fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u))
  have htopzero : σ (retainedApexUpperSource hβ.le hβπ 0) = p := by
    apply congrArg σ
    apply Subtype.ext
    exact sectorPolar_zero β
  have hpT : p ∈ T := ⟨0,htopzero⟩
  have hpP : p ∈ P := hσP _
  have hpS : p ∈ range σ := mem_range_self _
  have hpQ : p ∈ Q := by rw [hQ]; exact ⟨hpP,fun hw ↦ hw.2 hpT⟩
  have hQP : Q ⊆ P := by rw [hQ]; exact sdiff_subset
  obtain ⟨Ebase,_,_,hbasewidth,_,hbaseadm⟩ :=
    pointRetainedApex_construct_apex_chart_from_frontier ha y hβ hβπ hL σ hσ hσP C hC hremain
      hρ hρL hρC hfront hQ
  obtain ⟨Dbase,hνbase,_⟩ := hνboundary p hpfront
  have hbaseold : C.flatPhysicalWidth = Dbase.flatPhysicalWidth := by
    simpa only [PointRetainedConeNeighborhood.flatPhysicalWidth, p, add_comm]
      using C.physical_width_eq Dbase
  have hbasecoeff : retainedApexCurvature ν p β p = Real.pi-Ebase.flatPhysicalWidth := by
    rw [retainedApexCurvature_at,hbasewidth,hbaseold,hνbase]
    ring
  refine ⟨?_,?_,?_⟩
  · intro x hxQ
    have hxp : x ≠ p := fun he ↦ hxQ (he.symm ▸ hpQ)
    rw [retainedApexCurvature_off ν β hxp]
    by_cases hxP : x ∈ P
    · apply hclean
      have hxW : x ∈ range σ \ T := by
        by_contra hxW
        exact hxQ (hQ.symm ▸ And.intro hxP hxW)
      exact hxW
    · exact hνoff x hxP
  · intro x hxI
    have hxP := interior_mono hQP hxI
    have hxp : x ≠ p := fun he ↦ hpnot (he ▸ hxP)
    rw [retainedApexCurvature_off ν β hxp]
    exact hνint x hxP
  · intro x hxF
    rw [hQfront] at hxF
    rcases hxF with hxT | hxOld
    · obtain ⟨r,hrx⟩ := hxT
      change σ (retainedApexUpperSource hβ.le hβπ r) = x at hrx
      by_cases hr0 : r = 0
      · have hxp : x = p := by rw [hr0,htopzero] at hrx; exact hrx.symm
        rw [hxp]
        exact ⟨Ebase,hbasecoeff,hbaseadm⟩
      · have hrpos : 0 < (r:ℝ) := lt_of_le_of_ne r.2
          (fun he ↦ hr0 (Subtype.ext he.symm))
        have hxI : x ∈ interior P := hrx ▸ hTopInterior r hrpos
        have hxp : x ≠ p := fun he ↦ hpnot (he ▸ hxI)
        obtain ⟨E,_,hEcoeff,hEadm⟩ := pointRetainedSector_construct_passing_chart
          ha y hβ hβπ σ hσ hQ r hrpos (hTopInterior r hrpos)
        subst x
        refine ⟨E,?_,hEadm⟩
        rw [retainedApexCurvature_off ν β hxp,hνint _ hxI]
        exact hEcoeff.symm
    · obtain ⟨D,hνD,hDadm⟩ := hνboundary x hxOld.1
      obtain ⟨E,_,hElo,hEhi,hEwidth⟩ :=
        pointTranslatedStrip_retained_chart_away_from_image ha y hP hS hxOld.2 D
      rw [← hQclosure]
      have hxp : x ≠ p := fun he ↦ hxOld.2 (he.symm ▸ hpS)
      refine ⟨E,?_,?_⟩
      · rw [retainedApexCurvature_off ν β hxp,hνD,hEwidth]
      · unfold PointRetainedConeNeighborhood.Admissible
        rw [hElo,hEhi]
        exact hDadm

end RepulsiveCoulomb
