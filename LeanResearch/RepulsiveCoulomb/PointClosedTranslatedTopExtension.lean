import LeanResearch.RepulsiveCoulomb.MetricTranslatedTopExtension
import LeanResearch.RepulsiveCoulomb.PointConvexFlatClosedEmbedding

/-! ISOLATED SOURCE-ONLY DRAFT. Actual closed-map continuation from the mixed
relative-halfdisk/full-disk top construction. Ambient local-to-global geometry
and completeness produce all pair distances and preserve the entire old map.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem point_exists_closed_translated_top_extension
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hP : IsClosed P) {stripAngle R s delta ell : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi)
    (hR : 0 < R) (hs : 0 < s) (hsdelta : s < delta) (hsell : s < ell)
    (f : flatShearedRectangle (conePhase stripAngle) R s → P)
    (hf : @Isometry _ P (inferInstance : PseudoEMetricSpace
      (flatShearedRectangle (conePhase stripAngle) R s))
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace f)
    (edge : Icc (0 : ℝ) ell → P)
    (hedge : @Isometry (Icc (0 : ℝ) ell) P inferInstance
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace edge)
    (hold : ∀ u : Icc (0 : ℝ) s,
      f (shearedCompactEdgePoint hR.le u) = edge ⟨u.1, u.2.1, u.2.2.trans hsell.le⟩)
    (C : @MetricFlatHalfDiskChart P (pointRegionMetricSpace ha y P)
      (f (shearedCompactEdgePoint hR.le ⟨s, hs.le, le_rfl⟩)))
    (hregular : ∀ r : Icc (0 : ℝ) R, 0 < r.1 →
      Nonempty (@MetricFlatDiskChart P (pointRegionMetricSpace ha y P)
        (f (shearedTopPoint (conePhase stripAngle) R s hs.le r)))) :
    ∃ h : ℝ, 0 < h ∧ s + h < delta ∧
      ∃ F : flatShearedRectangle (conePhase stripAngle) R (s + h) → P,
        (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
        ∀ x : flatShearedRectangle (conePhase stripAngle) R s,
          ∀ hx : x.1 ∈ flatShearedRectangle (conePhase stripAngle) R (s + h), F ⟨x.1, hx⟩ = f x := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  obtain ⟨h, hh, hhδ, G, hGold, hGlocal⟩ :=
    exists_translated_top_local_extension stripAngle_pos stripAngle_lt_pi hR hs hsdelta hsell
      f hf edge hedge hold C hregular
  let K := flatShearedRectangle (conePhase stripAngle) R s
  let K' := flatShearedRectangle (conePhase stripAngle) R (s + h)
  let U := interior K'
  have hvi : (conePhase stripAngle).im ≠ 0 := by
    rw [conePhase_im]
    exact (Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi).ne'
  have hnewpos : 0 < s + h := add_pos hs hh
  have hU : Convex ℝ U := (flatShearedRectangle_convex (conePhase stripAngle) R (s + h)).interior
  have hlocal : PointLocallyDistancePreserving a y (fun x ↦ (G x).1) := hGlocal
  have hclosure : closure U = K' := flatShearedRectangle_closure_interior hvi hR hnewpos
  let incl : K' → closure U := fun z ↦ ⟨z.1, hclosure.symm ▸ z.2⟩
  have hincl : Isometry incl := fun _ _ ↦ rfl
  let F : K' → P := pointFlatClosureMap ha y G ∘ incl
  have hF : @Isometry K' P (inferInstance : PseudoEMetricSpace K') M.toPseudoEMetricSpace F :=
    (pointFlatClosureMap_isometry ha y hU hlocal hP).comp hincl
  have hKK : K ⊆ K' := flatShearedRectangle_mono le_rfl (by linarith)
  let oldincl : K → K' := fun z ↦ ⟨z.1, hKK z.2⟩
  have holdincl : Isometry oldincl := fun _ _ ↦ rfl
  let oldinterior : interior K → K := Set.inclusion interior_subset
  have hdense : DenseRange oldinterior := by
    apply (denseRange_inclusion_iff (interior_subset : interior K ⊆ K)).mpr
    rw [flatShearedRectangle_closure_interior hvi hR hs]
  have hFcont : Continuous (F ∘ oldincl) := by
    have hc : @Continuous K P _ M.toUniformSpace.toTopologicalSpace (F ∘ oldincl) :=
      @Isometry.continuous K P (inferInstance : PseudoEMetricSpace K) M.toPseudoEMetricSpace
        (F ∘ oldincl) (hF.comp holdincl)
    change @Continuous K P _ (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace
      (F ∘ oldincl) at hc
    rwa [pointRegionMetricSpace_topology ha y P] at hc
  have hfcont : Continuous f := by
    have hc : @Continuous K P _ M.toUniformSpace.toTopologicalSpace f :=
      @Isometry.continuous K P (inferInstance : PseudoEMetricSpace K) M.toPseudoEMetricSpace f hf
    change @Continuous K P _ (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace f at hc
    rwa [pointRegionMetricSpace_topology ha y P] at hc
  have heq : F ∘ oldincl = f := hdense.equalizer hFcont hfcont (by
    funext x
    have hxU : x.1 ∈ U := interior_mono hKK x.2
    have hext := pointFlatClosureMap_apply ha y hU hlocal (⟨x.1, hxU⟩ : U)
    exact hext.trans (hGold x hxU))
  refine ⟨h, hh, hhδ, F, ?_, ?_⟩
  · intro x z
    exact @Isometry.dist_eq K' P _ M.toPseudoMetricSpace F hF x z
  · intro x hx
    exact congrFun heq x


end RepulsiveCoulomb
