import LeanResearch.RepulsiveCoulomb.PointTranslatedMarkedLimitContact
import LeanResearch.RepulsiveCoulomb.PointActualTranslatedStripIteration
import LeanResearch.RepulsiveCoulomb.PointTranslatedResidualFiniteBoundary

/-! SOURCE-ONLY, UNCOMPILED. The attained maximal strip produces the literal
residual closure(P \\ range F), all-point transferred signed state, genuine
ambient halfplane topology and exact retained corner charts once its strict
remaining angle is proved. Exact old contact and below-top cleanliness are
constructed here from the actual finite limit, not supplied as certificates.
The general original no-clean strict-angle discharge remains separate. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb.PointTranslatedRegularData.FiniteWidthLimit
variable {m : ℕ} {a : Fin m→ℝ} {y : Fin m→ℂ} {ha : ∀ j,0≤a j}
  {P : Set ℂ} {ν α : ℂ→₀ℝ} {D : PointTranslatedRegularData a y ha P ν α}
  (K : D.FiniteWidthLimit)

theorem below_top_coefficients_zero
    {x : ℂ}
    (hx : x∈range (fun q ↦ (K.map q).1)\
      range (fun r ↦ (K.map (translatedStripTop K.positive.le r)).1))
    (hxp : x≠(D.ray 0).1) : ν x=0 ∧ α x=0 := by
  obtain ⟨q,rfl⟩ := hx.1
  obtain ⟨r,hr,u,hu,hq⟩ := q.2
  have hub : u<sSup D.regularWidths := by
    apply lt_of_le_of_ne hu.2
    intro he
    exact hx.2 ((translatedStrip_image_mem_top_iff D.direction_im_ne_zero K.positive.le
      K.closed.injective q hr hq).mpr he)
  have he : q=⟨flatShearedPoint (conePhase D.angle) r u,r,hr,u,hu,rfl⟩ := Subtype.ext hq
  apply pointSigned_eq_zero_off_marked
  intro hm
  exact K.below_unmarked ⟨r,hr⟩ ⟨u,hu⟩ hub (he ▸ And.intro hm hxp)

/-- Same exact reusable geometric output as the genuine supplied-strip cut,
now with the strip, old contact, marked avoidance and original width all
coming from the constructed supremum. -/
theorem construct_actual_residual_of_positive_angle
    (Cz : PointRetainedConeNeighborhood a y P
      (K.map (translatedStripTop K.positive.le 0)).1) (hCz : Cz.Admissible)
    (hremain : Real.pi-D.angle<Cz.flatPhysicalWidth) :
    let S := range (fun q ↦ (K.map q).1)
    let τ : NNReal→ℂ := fun r ↦ (K.map (translatedStripTop K.positive.le r)).1
    let Q := closure (P\S)
    let p := (K.map (translatedStripBottom K.positive.le 0)).1
    let μ := BoundaryPreparation.transfer ν p (τ 0)
    Nonempty (PointTranslatedStripIterationOutput a y P S Q τ p ν μ α (Real.pi-D.angle) Cz) ∧
      (∀ r,(K.map (translatedStripBottom K.positive.le r)).1∉Q) ∧
      (∀ u : Icc (0:ℝ) (sSup D.regularWidths),u.1<sSup D.regularWidths→
        (K.map (translatedStripEdge u)).1∉Q) := by
  have hp : (K.map (translatedStripBottom K.positive.le 0)).1=(D.ray 0).1 :=
    congrArg Subtype.val (K.bottom 0)
  have hclean : ∀ x∈range (fun q ↦ (K.map q).1)\
      range (fun r ↦ (K.map (translatedStripTop K.positive.le r)).1),
      x≠(K.map (translatedStripBottom K.positive.le 0)).1→ν x=0 ∧ α x=0 := by
    intro x hx hxp
    exact K.below_top_coefficients_zero hx (fun he ↦ hxp (he.trans hp.symm))
  apply pointTranslatedStrip_actual_iteration_output ha y D.ambient D.region_eq
    D.angle_pos D.angle_lt_pi K.positive K.map
    (fun x z ↦ @Isometry.dist_eq _ P _ (pointRegionMetricSpace ha y P).toPseudoMetricSpace
      K.map K.metric x z)
    (K.exact_old_contact_of_positive_residual Cz hCz hremain) ν α
    D.interior_coeff D.boundary_coeff D.exterior_coeff Cz hCz
    (K.contact_origin_coefficient Cz) hremain D.allocation_support
    (by rw [hp];exact D.apex_budget_zero) hclean

end RepulsiveCoulomb.PointTranslatedRegularData.FiniteWidthLimit
