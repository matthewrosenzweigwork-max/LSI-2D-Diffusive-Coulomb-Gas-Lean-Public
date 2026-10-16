module

public import LeanResearch.RepulsiveCoulomb.PointRetainedSectorPassingChart
public import LeanResearch.RepulsiveCoulomb.PointDisappearingApexDepartureChart
public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripRetainedGerms

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Transfer the actual passing halfdisk complement
chart to the TAIL-based residual. The whole-upper-ray cut is used only as a
local comparison set; it is not mistaken for the actual disappearing cut. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointDisappearingSector_construct_passing_chart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P Q : Set ℂ} (r : NNReal)
    (hQ : Q=P\(range σ\range (fun t : NNReal ↦ σ (disappearingSectorTail hβ.le hβπ r t))))
    (t : NNReal) (ht : 0<(t:ℝ))
    (hp : σ (disappearingSectorTail hβ.le hβπ r t)∈interior P) :
    ∃ E : PointRetainedConeNeighborhood a y Q (σ (disappearingSectorTail hβ.le hβπ r t)),
      E.flatPhysicalWidth=(coalescedPointExponent a y (σ (disappearingSectorTail hβ.le hβπ r t))/2+1)*
        (2*Real.pi)-Real.pi ∧
      Real.pi-E.flatPhysicalWidth= -Real.pi*coalescedPointExponent a y (σ (disappearingSectorTail hβ.le hβπ r t)) ∧
      E.Admissible := by
  let top : NNReal → ℂ:=fun u ↦ σ (retainedApexUpperSource hβ.le hβπ u)
  let tail : NNReal → ℂ:=fun u ↦ top (r+u)
  let Q0:=P\(range σ\range top)
  have hrt : 0<((r+t:NNReal):ℝ):=add_pos_of_nonneg_of_pos r.2 ht
  obtain ⟨D,hwidth,hturn,hD⟩:=pointRetainedSector_construct_passing_chart ha y hβ hβπ σ hσ
    (Q:=Q0) rfl (r+t) hrt hp
  have hgerm : ∀ z,(pointSmoothConformalEDist a y z (tail t)).toReal≤(t:ℝ)/2 →
      (z∈range top ↔ z∈range tail):=by
    intro z hz
    constructor
    · rintro ⟨v,hv⟩
      have hd:=hz
      rw [← hv,hσ,(retainedApexUpperSource_isometry hβ.le hβπ).dist_eq,NNReal.dist_eq] at hd
      rw [NNReal.coe_add] at hd
      have hvr : (r:ℝ)≤v:=by
        have hl : -((t:ℝ)/2) ≤ (v:ℝ)-((r:ℝ)+(t:ℝ)) := (abs_le.mp hd).1
        linarith
      let u : NNReal:=⟨(v:ℝ)-(r:ℝ),sub_nonneg.mpr hvr⟩
      refine ⟨u,?_⟩
      have he : r+u=v:=Subtype.ext (by change (r:ℝ)+((v:ℝ)-(r:ℝ))=v; ring)
      change top (r+u)=z
      rwa [he]
    · rintro ⟨u,rfl⟩
      exact ⟨r+u,rfl⟩
  have hregions : ∀ z,(pointSmoothConformalEDist a y z (tail t)).toReal≤(t:ℝ)/2 →
      (z∈Q0 ↔ z∈Q):=by
    intro z hz
    rw [hQ]
    change (z∈P ∧ ¬(z∈range σ ∧ z∉range top)) ↔
      (z∈P ∧ ¬(z∈range σ ∧ z∉range tail))
    rw [hgerm z hz]
  let E:=D.translatedGerm (half_pos ht) hregions
  exact ⟨E,hwidth,hturn,hD⟩

end RepulsiveCoulomb
