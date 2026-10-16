module

public import LeanResearch.RepulsiveCoulomb.PointDisappearingSectorNoLaterContact

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Exact sector contact from the independently
constructed finite departure. Later contact is disproved by the actual cap
construction; the equality below is an output, never a cut certificate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointDisappearingSector_exact_contact_of_departure
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P : Set ℂ} (H : ℂ≃ₜℂ) (hHP : P=H ⁻¹' planarClosedUpperHalfplane)
    (hσP : ∀ x,σ x∈P)
    (hbottom : ∀ t : NNReal,σ (retainedApexBottomSource hβ.le hβπ t)∈frontier P)
    (pieces : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P=⋃ i,range (pieces i).curve)
    (r : NNReal) (hr : 0<(r:ℝ))
    (hprefix : ∀ t : NNReal,t≤r → σ (retainedApexUpperSource hβ.le hβπ t)∈frontier P)
    (hterminal : ∀ t : ℝ,(r:ℝ)<t → ¬ Icc (r:ℝ) t ⊆
      (fun u : ℝ ↦ σ (retainedApexUpperSource hβ.le hβπ u.toNNReal)) ⁻¹' frontier P)
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    (hboundary : ν (σ (flatLinkSectorApex hβ.le))=Real.pi-β)
    (hβα : β≤α (σ (flatLinkSectorApex hβ.le)))
    (hzneg : ν (σ (retainedApexUpperSource hβ.le hβπ r))<0)
    (hνB : ∀ x∈frontier P,∃ C : PointRetainedConeNeighborhood a y P x,
      ν x=Real.pi-C.flatPhysicalWidth ∧ C.Admissible)
    (hinterior : ∀ x : closedEuclideanSector β,0<‖x.1‖ → 0<Complex.arg x.1 → Complex.arg x.1<β →
      σ x∈interior P) :
    range σ∩frontier P=
      range (fun t : NNReal ↦ σ (retainedApexBottomSource hβ.le hβπ t)) ∪
      (fun t : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ t)) '' Icc 0 r ∧
    (∀ t : NNReal,r<t → σ (retainedApexUpperSource hβ.le hβπ t)∈interior P) := by
  have hno:=pointDisappearingSector_no_later_old_contact ha y hβ hβπ σ hσ H hHP hσP hbottom
    pieces hpieces r hr hprefix hterminal hbudget hboundary hβα hzneg hνB
  constructor
  · ext z
    constructor
    · rintro ⟨⟨x,rfl⟩,hxF⟩
      by_cases hx0 : x.1=0
      · left
        refine ⟨0,congrArg σ (Subtype.ext ?_)⟩
        change sectorPolar 0 0=x.1
        rw [sectorPolar_zero,hx0]
      by_cases harg0 : Complex.arg x.1=0
      · left
        refine ⟨⟨‖x.1‖,norm_nonneg _⟩,congrArg σ (Subtype.ext ?_)⟩
        change sectorPolar ‖x.1‖ 0=x.1
        rw [← harg0,sectorPolar_norm_arg]
      by_cases hargβ : Complex.arg x.1=β
      · let t : NNReal:=⟨‖x.1‖,norm_nonneg _⟩
        have he : retainedApexUpperSource hβ.le hβπ t=x:=by
          apply Subtype.ext
          change sectorPolar ‖x.1‖ β=x.1
          exact (congrArg (sectorPolar ‖x.1‖) hargβ).symm.trans (sectorPolar_norm_arg x.1)
        have htr : t≤r:=by
          by_contra hn
          exact hno t (lt_of_not_ge hn) (he.symm ▸ hxF)
        exact Or.inr ⟨t,⟨(show (0 : NNReal) ≤ t from zero_le),htr⟩,congrArg σ he⟩
      · exact False.elim (hxF.2 (hinterior x (norm_pos_iff.mpr hx0)
          (lt_of_le_of_ne x.2.1 (Ne.symm harg0)) (lt_of_le_of_ne x.2.2 hargβ)))
    · rintro (⟨t,rfl⟩ | ⟨t,ht,rfl⟩)
      · exact ⟨mem_range_self _,hbottom t⟩
      · exact ⟨mem_range_self _,hprefix t ht.2⟩
  · intro t ht
    by_contra hi
    exact hno t ht ⟨subset_closure (hσP _),hi⟩

end RepulsiveCoulomb
