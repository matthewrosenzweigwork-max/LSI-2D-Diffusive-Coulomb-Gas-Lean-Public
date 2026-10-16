module

public import LeanResearch.RepulsiveCoulomb.PointDisappearingApexActualDeparture

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. All original curvature and budget coefficients
on the literal removed piece vanish except at the fully spent original apex.
The statement is derived by exact source classification and the constructed
clean upper prefix, with no original-atom support shortcut. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem disappearingSector_removed_coefficients_zero
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ) (ν α : ℂ →₀ ℝ) (r : NNReal)
    (hbottom : ∀ t : NNReal,0<(t:ℝ) →
      ν (σ (retainedApexBottomSource hβ.le hβπ t))=0 ∧ α (σ (retainedApexBottomSource hβ.le hβπ t))=0)
    (hopen : ∀ x : closedEuclideanSector β,0<‖x.1‖ → 0<Complex.arg x.1 → Complex.arg x.1<β →
      ν (σ x)=0 ∧ α (σ x)=0)
    (hprefix : ∀ t : NNReal,0<(t:ℝ) → t<r →
      ν (σ (retainedApexUpperSource hβ.le hβπ t))=0 ∧ α (σ (retainedApexUpperSource hβ.le hβπ t))=0) :
    ∀ z∈range σ\range (fun t : NNReal ↦ σ (disappearingSectorTail hβ.le hβπ r t)),
      z≠σ (flatLinkSectorApex hβ.le) → ν z=0 ∧ α z=0 := by
  rintro z ⟨⟨x,rfl⟩,hxT⟩ hxp
  have hx0 : x.1≠0:=by
    intro hx0
    apply hxp
    exact congrArg σ (Subtype.ext hx0)
  have hxpos : 0<‖x.1‖:=norm_pos_iff.mpr hx0
  by_cases harg0 : Complex.arg x.1=0
  · have he : retainedApexBottomSource hβ.le hβπ ⟨‖x.1‖,norm_nonneg _⟩=x:=by
      apply Subtype.ext
      change sectorPolar ‖x.1‖ 0=x.1
      rw [← harg0,sectorPolar_norm_arg]
    simpa only [he] using hbottom ⟨‖x.1‖,norm_nonneg _⟩ hxpos
  by_cases hargβ : Complex.arg x.1=β
  · let u : NNReal:=⟨‖x.1‖,norm_nonneg _⟩
    have he : retainedApexUpperSource hβ.le hβπ u=x:=by
      apply Subtype.ext
      change sectorPolar ‖x.1‖ β=x.1
      exact (congrArg (sectorPolar ‖x.1‖) hargβ.symm).trans (sectorPolar_norm_arg x.1)
    have hur : u<r:=by
      by_contra hn
      have hru : r≤u:=le_of_not_gt hn
      apply hxT
      let t : NNReal:=⟨(u:ℝ)-(r:ℝ),sub_nonneg.mpr hru⟩
      have hsum : r+t=u:=Subtype.ext (by change (r:ℝ)+((u:ℝ)-(r:ℝ))=u; ring)
      refine ⟨t,?_⟩
      change σ (retainedApexUpperSource hβ.le hβπ (r+t))=σ x
      rw [hsum,he]
    simpa only [he] using hprefix u hxpos hur
  · exact hopen x hxpos (lt_of_le_of_ne x.2.1 (Ne.symm harg0))
      (lt_of_le_of_ne x.2.2 hargβ)

end RepulsiveCoulomb
