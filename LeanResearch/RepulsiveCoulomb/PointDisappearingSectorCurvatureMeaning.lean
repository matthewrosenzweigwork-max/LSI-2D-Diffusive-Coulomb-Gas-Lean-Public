module

public import LeanResearch.RepulsiveCoulomb.PointDisappearingSectorPassingChart
public import LeanResearch.RepulsiveCoulomb.PointDisappearingApexBudget

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. All-point geometric interpretation of the
ambient finite update after the literal disappearing cut is constructed. New
charts are constructed from the actual source; no new coefficient/angle/chart
certificate is supplied. Global contact/topology is a prior theorem layer. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointDisappearingSector_all_point_curvature
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P Q : Set ℂ} (hP : IsClosed P) (hσP : ∀ x,σ x∈P)
    (r : NNReal) (hr : 0<(r:ℝ))
    (hprefix : ∀ t : NNReal,t≤r → σ (retainedApexUpperSource hβ.le hβπ t)∈frontier P)
    (hopenTop : ∀ t : NNReal,r<t → σ (retainedApexUpperSource hβ.le hβπ t)∈interior P)
    (hpfront : σ (flatLinkSectorApex hβ.le)∈frontier P)
    (hzneq : σ (retainedApexUpperSource hβ.le hβπ r)≠σ (flatLinkSectorApex hβ.le))
    (ν : ℂ →₀ ℝ)
    (hνI : ∀ x∈interior P,ν x= -Real.pi*coalescedPointExponent a y x)
    (hνB : ∀ x∈frontier P,∃ C : PointRetainedConeNeighborhood a y P x,
      ν x=Real.pi-C.flatPhysicalWidth ∧ C.Admissible)
    (hνO : ∀ x,x∉P → ν x=0)
    (hzneg : ν (σ (retainedApexUpperSource hβ.le hβπ r))<0)
    (hclean : ∀ x∈range σ\range (fun t : NNReal ↦ σ (disappearingSectorTail hβ.le hβπ r t)),
      x≠σ (flatLinkSectorApex hβ.le) → ν x=0)
    (hQcl : Q=closure (P\range σ))
    (hQ : Q=P\(range σ\range (fun t : NNReal ↦ σ (disappearingSectorTail hβ.le hβπ r t))))
    (hQfront : frontier Q=range (fun t : NNReal ↦ σ (disappearingSectorTail hβ.le hβπ r t)) ∪
      (frontier P\range σ)) :
    let p:=σ (flatLinkSectorApex hβ.le)
    let z:=σ (retainedApexUpperSource hβ.le hβπ r)
    let μ:=disappearingApexCurvature ν p z
    (∀ x,x∉Q → μ x=0) ∧
    (∀ x∈interior Q,μ x= -Real.pi*coalescedPointExponent a y x) ∧
    (∀ x∈frontier Q,∃ E : PointRetainedConeNeighborhood a y Q x,
      μ x=Real.pi-E.flatPhysicalWidth ∧ E.Admissible) := by
  let p:=σ (flatLinkSectorApex hβ.le)
  let z:=σ (retainedApexUpperSource hβ.le hβπ r)
  let τ : NNReal → ℂ:=fun t ↦ σ (disappearingSectorTail hβ.le hβπ r t)
  let μ:=disappearingApexCurvature ν p z
  change p ∈ frontier P at hpfront
  have hτ0 : τ 0=z:=by simp only [τ,disappearingSectorTail,add_zero,z]
  have hzfront : z∈frontier P:=hprefix r le_rfl
  have hzT : z∈range τ:=⟨0,hτ0⟩
  have hzQ : z∈Q:=by rw [hQ]; exact ⟨hσP _,fun hw ↦ hw.2 hzT⟩
  have hQP : Q⊆P:=by rw [hQ]; exact sdiff_subset
  have hSclosed : IsClosed (range σ):=(pointRetainedSector_closed_proper ha y hβ hβπ σ hσ).1.isClosed_range
  obtain ⟨Cz,hνz,hCz⟩:=hνB z hzfront
  obtain ⟨Ez,hzwidth,hzturn,hEz⟩:=pointDisappearingApex_construct_departure_chart ha y hβ hβπ σ hσ hσP
    r hr hprefix Cz hCz hνz hzneg hQ
  have hzcoeff : μ z=Real.pi-Ez.flatPhysicalWidth:=by
    rw [disappearingApexCurvature_at_departure ν hzneq]
    exact hzturn.symm
  refine ⟨?_,?_,?_⟩
  · intro x hxQ
    by_cases hxp : x=p
    · subst x
      exact disappearingApexCurvature_at_apex ν hzneq
    have hxz : x≠z:=fun he ↦ hxQ (he.symm ▸ hzQ)
    rw [disappearingApexCurvature_off ν hxp hxz]
    by_cases hxP : x∈P
    · apply hclean x _ hxp
      by_contra hxW
      exact hxQ (hQ.symm ▸ And.intro hxP hxW)
    · exact hνO x hxP
  · intro x hxI
    have hxPI:=interior_mono hQP hxI
    have hxp : x≠p:=fun he ↦ hpfront.2 (he ▸ hxPI)
    have hxz : x≠z:=fun he ↦ hzfront.2 (he ▸ hxPI)
    rw [disappearingApexCurvature_off ν hxp hxz]
    exact hνI x hxPI
  · intro x hxF
    rw [hQfront] at hxF
    rcases hxF with hxT | hxOld
    · obtain ⟨t,htx⟩:=hxT
      change τ t = x at htx
      by_cases ht0 : t=0
      · have he : x=z:=by rw [ht0,hτ0] at htx; exact htx.symm
        rw [he]
        exact ⟨Ez,hzcoeff,hEz⟩
      · have ht : 0<(t:ℝ):=lt_of_le_of_ne t.2 (fun he ↦ ht0 (Subtype.ext he.symm))
        have hxPI : τ t∈interior P:=hopenTop (r+t) (lt_add_of_pos_right _ ht)
        obtain ⟨E,_,hEturn,hE⟩:=pointDisappearingSector_construct_passing_chart ha y hβ hβπ σ hσ r hQ t ht hxPI
        have hxp : τ t≠p:=fun he ↦ hpfront.2 (he ▸ hxPI)
        have hxz : τ t≠z:=fun he ↦ hzfront.2 (he ▸ hxPI)
        have hcoeff : μ (τ t)=Real.pi-E.flatPhysicalWidth:=by
          rw [disappearingApexCurvature_off ν hxp hxz,hνI _ hxPI]
          exact hEturn.symm
        have hfinal : ∃ E : PointRetainedConeNeighborhood a y Q (τ t),
            μ (τ t)=Real.pi-E.flatPhysicalWidth ∧ E.Admissible := ⟨E,hcoeff,hE⟩
        exact Eq.mp (congrArg (fun v : ℂ =>
          ∃ E : PointRetainedConeNeighborhood a y Q v,
            μ v=Real.pi-E.flatPhysicalWidth ∧ E.Admissible) htx) hfinal
    · obtain ⟨C,hνC,hC⟩:=hνB x hxOld.1
      obtain ⟨E,_,hlo,hhi,hwidth⟩:=pointTranslatedStrip_retained_chart_away_from_image ha y hP hSclosed hxOld.2 C
      have hxp : x≠p:=fun he ↦ hxOld.2 (he.symm ▸ mem_range_self (flatLinkSectorApex hβ.le))
      have hxz : x≠z:=fun he ↦ hxOld.2 (he.symm ▸ mem_range_self (retainedApexUpperSource hβ.le hβπ r))
      have hfinal : ∃ E : PointRetainedConeNeighborhood a y (closure (P\range σ)) x,
          μ x=Real.pi-E.flatPhysicalWidth ∧ E.Admissible := by
        refine ⟨E,?_,?_⟩
        · rw [disappearingApexCurvature_off ν hxp hxz,hνC,hwidth]
        · unfold PointRetainedConeNeighborhood.Admissible
          rw [hlo,hhi]
          exact hC
      exact Eq.mp (congrArg (fun Q' : Set ℂ =>
        ∃ E : PointRetainedConeNeighborhood a y Q' x,
          μ x=Real.pi-E.flatPhysicalWidth ∧ E.Admissible) hQcl.symm) hfinal

end RepulsiveCoulomb
