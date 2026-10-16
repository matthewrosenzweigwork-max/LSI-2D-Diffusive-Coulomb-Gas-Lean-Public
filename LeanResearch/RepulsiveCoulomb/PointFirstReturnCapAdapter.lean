module

public import LeanResearch.RepulsiveCoulomb.PointFiniteBoundaryRayContacts
public import LeanResearch.RepulsiveCoulomb.PlanarFirstReturnJordanCaps
public import LeanResearch.RepulsiveCoulomb.PointFirstReturnRadialGerms

@[expose] public section

/-! Source-only draft. End-to-end bounded topology adapter for an actual ray
entering an actual halfplane and subsequently returning. This endpoint chooses
the boundary gap containing a specified interior time; the finite-piece
endpoint separately identifies the very first later component after a supplied
terminal initial contact. Neither theorem constructs a flat strip or sector. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- The actual metric identity gives injectivity on all nonnegative ray times. -/
theorem pointMetricRay_nonnegative_injOn {m : ℕ} {a : Fin m → ℝ}
    (y : Fin m → ℂ) (r : ℝ → ℂ)
    (hd : ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (r s) (r t)).toReal = dist s t) :
    InjOn r (Ici (0 : ℝ)) := by
  intro s hs t ht he
  have h := hd s hs t ht
  rw [he, pointSmoothConformalEDist_self, ENNReal.toReal_zero] at h
  exact dist_eq_zero.mp h.symm

/-- The simple loop can be recovered in ordinary complex coordinates, with
image exactly the stopped-ray/old-arc carrier already proved Jordan. The loop
is an output of actual two-arc gluing, not a simple-loop hypothesis. -/
theorem exists_complex_loop_of_actual_jordan {C : Set ℂ}
    (hJ : Schoenflies.IsJordanCurve (Complex.orthonormalBasisOneI.repr '' C)) :
    ∃ f : ℝ → ℂ, ContinuousOn f (Icc (0 : ℝ) 1) ∧ f 0 = f 1 ∧
      InjOn f (Ico (0 : ℝ) 1) ∧ f '' Icc (0 : ℝ) 1 = C := by
  let e : ℂ ≃ₜ Schoenflies.Plane := Complex.orthonormalBasisOneI.repr.toHomeomorph
  obtain ⟨g, hg, him⟩ := hJ
  let f : ℝ → ℂ := e.symm ∘ g
  refine ⟨f, e.symm.continuous.comp_continuousOn hg.continuousOn,
    congrArg e.symm hg.closes, ?_, ?_⟩
  · intro s hs t ht he
    exact hg.injOn hs ht (e.symm.injective he)
  · rw [image_comp, him]
    change e.symm '' (e '' C) = C
    exact e.toEquiv.symm_image_image C

/-- From one actual interior time, a preceding boundary point and a later
boundary contact, construct the two bounding contacts of that excursion,
the original boundary arc, a complex simple loop and its compact filled cap
contained in the literal `P`. No finite-boundary-contact assumption is needed
for this compact trimming endpoint. -/
theorem exists_pointMetricRay_trimmed_firstReturn_cap
    {m : ℕ} {a : Fin m → ℝ} (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    (b r : ℝ → ℂ) (hb : Continuous b) (hbi : Function.Injective b)
    (hboundary : range b = frontier P) (hr : Continuous r)
    (hd : ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (r s) (r t)).toReal = dist s t)
    (hrP : MapsTo r (Ici (0 : ℝ)) P)
    {a₀ e b₀ : ℝ} (ha₀ : 0 ≤ a₀) (hae : a₀ < e) (heb : e < b₀)
    (hstart : r a₀ ∈ frontier P) (hentry : r e ∈ interior P)
    (hlater : r b₀ ∈ frontier P) :
    ∃ z w s t : ℝ, a₀ ≤ z ∧ z < e ∧ e < w ∧ w ≤ b₀ ∧
      r z ∈ frontier P ∧ r w ∈ frontier P ∧
      (∀ u ∈ Ioo z w, r u ∉ frontier P) ∧ b s = r z ∧ b t = r w ∧ s ≠ t ∧
      let C := range (lineCapSegment r z w) ∪ range (lineCapSegment b s t)
      (∃ f : ℝ → ℂ, ContinuousOn f (Icc (0 : ℝ) 1) ∧ f 0 = f 1 ∧
        InjOn f (Ico (0 : ℝ) 1) ∧ f '' Icc (0 : ℝ) 1 = C) ∧
      ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
        Disjoint U V ∧ U ∪ V = Cᶜ ∧ frontier U = C ∧ frontier V = C ∧
        IsCompact (closure U) ∧ closure U ⊆ P := by
  have hC : IsClosed (r ⁻¹' frontier P) := isClosed_frontier.preimage hr
  have he : r e ∉ frontier P := fun h => h.2 hentry
  obtain ⟨z, w, haz, hze, hew, hwb, hz, hw, hgap⟩ :=
    exists_contact_gap_around_noncontact hC hae heb hstart he hlater
  have hzw : z < w := hze.trans hew
  have hz0 : 0 ≤ z := ha₀.trans haz
  have hinter : Icc z w ⊆ Ici (0 : ℝ) := fun u hu => hz0.trans hu.1
  have hri := (pointMetricRay_nonnegative_injOn y r hd).mono hinter
  obtain ⟨s, t, hs, ht, hst, hJ, U, V, hU, hV, hUc, hVc,
      hUV, hcover, hfu, hfv, hK, hcontain⟩ :=
    exists_firstReturn_actual_cap H hP b r hb hbi hboundary hr hzw hri hz hw
      (fun u hu => hrP (hinter hu)) hgap
  exact ⟨z, w, s, t, haz, hze, hew, hwb, hz, hw, hgap, hs, ht, hst,
    exists_complex_loop_of_actual_jordan hJ, U, V, hU, hV, hUc, hVc,
    hUV, hcover, hfu, hfv, hK, hcontain⟩


/-- The finite-old-piece endpoint starts at the specified terminal initial
contact and produces its first later contact and actual bounded cap. The gap
and Jordan/containment conclusions are constructed, rather than supplied. -/
theorem exists_pointMetricRay_initial_component_return_cap
    {m n : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    (E : Fin n → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (E i).curve)
    (b r : ℝ → ℂ) (hb : Continuous b) (hbi : Function.Injective b)
    (hboundary : range b = frontier P) (hr : Continuous r)
    (hd : ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (r s) (r t)).toReal = dist s t)
    (hrP : MapsTo r (Ici (0 : ℝ)) P)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : r z ∈ frontier P)
    (hterminal : ∀ t, z < t → ¬ Icc z t ⊆ r ⁻¹' frontier P)
    (hlater : ∃ t, z < t ∧ r t ∈ frontier P) :
    ∃ w s t : ℝ, z < w ∧ r w ∈ frontier P ∧
      (∀ u, z < u → r u ∈ frontier P → w ≤ u) ∧
      (∀ u ∈ Ioo z w, r u ∉ frontier P) ∧ b s = r z ∧ b t = r w ∧ s ≠ t ∧
      let C := range (lineCapSegment r z w) ∪ range (lineCapSegment b s t)
      Schoenflies.IsJordanCurve (Complex.orthonormalBasisOneI.repr '' C) ∧
      ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
        Disjoint U V ∧ U ∪ V = Cᶜ ∧ frontier U = C ∧ frontier V = C ∧
        IsCompact (closure U) ∧ closure U ⊆ P := by
  obtain ⟨w, hzw, hw, hleast, hgap⟩ :=
    exists_pointMetricRay_first_later_boundary_contact ha y E hpieces r hr hd hz0 hterminal hlater
  have hinter : Icc z w ⊆ Ici (0 : ℝ) := fun u hu => hz0.trans hu.1
  have hri := (pointMetricRay_nonnegative_injOn y r hd).mono hinter
  obtain ⟨s, t, hs, ht, hst, hJ, U, V, hU, hV, hUc, hVc,
      hUV, hcover, hfu, hfv, hK, hcontain⟩ :=
    exists_firstReturn_actual_cap H hP b r hb hbi hboundary hr hzw hri hz hw
      (fun u hu => hrP (hinter hu)) hgap
  exact ⟨w, s, t, hzw, hw, hleast, hgap, hs, ht, hst, hJ,
    U, V, hU, hV, hUc, hVc, hUV, hcover, hfu, hfv, hK, hcontain⟩

end RepulsiveCoulomb
