import LeanResearch.RepulsiveCoulomb.MetricShearedTopExtension
import LeanResearch.RepulsiveCoulomb.MetricInteriorSupportedPatchExtension
import LeanResearch.RepulsiveCoulomb.PointConvexFlatClosedEmbedding

/-! NEW header reconstruction. The retained proof suffix is unchanged. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem exists_normal_top_extension_of_full_top {Y : Type*} [MetricSpace Y]
    {R s delta : ℝ} (hR : 0 < R) (hs : 0 < s) (hsdelta : s < delta)
    (f : flatShearedRectangle Complex.I R s → Y)
    (hf : Isometry f)
    (hregular : ∀ r : Icc (0 : ℝ) R,
      Nonempty (MetricFlatDiskChart Y
        (f (shearedTopPoint Complex.I R s hs.le r)))) :
    ∃ h : ℝ, 0 < h ∧ s + h < delta ∧
      ∃ G : interior (flatShearedRectangle Complex.I R (s + h)) → Y,
        (∀ x : interior (flatShearedRectangle Complex.I R s),
          ∀ hx : x.1 ∈ interior (flatShearedRectangle Complex.I R (s + h)),
            G ⟨x.1, hx⟩ = f ⟨x.1, interior_subset x.2⟩) ∧
        ∀ p, ∃ V : Set (interior (flatShearedRectangle Complex.I R (s + h))), IsOpen V ∧ p ∈ V ∧
          ∀ x ∈ V, ∀ z ∈ V, dist (G x) (G z) = dist x z := by
  let K := flatShearedRectangle Complex.I R s
  let q := shearedTopPoint Complex.I R s hs.le
  have hpatch (r : Icc (0 : ℝ) R) : ∃ B : ℝ, 0 < B ∧
      ∃ e : supportedFlatPatch univ (q r).1 B ≃ᵢ ball (f (q r)) B,
        ∀ x : K, ∀ hx : x.1 ∈ supportedFlatPatch univ (q r).1 B, (e ⟨x.1, hx⟩).1 = f x := by
    obtain ⟨D⟩ := hregular r
    exact exists_interior_supported_patch_extension (flatShearedRectangle_convex _ _ _)
      (flatShearedRectangle_interior_nonempty (by simp) hR hs) f hf (q r) (by simp) D
  choose B hB e hold using hpatch
  exact exists_sheared_top_local_extension (by simp : ‖Complex.I‖ = 1) (by simp)
    hR hs hsdelta convex_univ (fun _ _ ↦ mem_univ _) f hf B hB e hold

theorem point_exists_closed_normal_full_top_extension
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hP : IsClosed P) {R s delta : ℝ}
    (hR : 0 < R) (hs : 0 < s) (hsdelta : s < delta)
    (f : flatShearedRectangle Complex.I R s → P)
    (hf : @Isometry _ P (inferInstance : PseudoEMetricSpace
      (flatShearedRectangle Complex.I R s))
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace f)
    (hregular : ∀ r : Icc (0 : ℝ) R,
      Nonempty (@MetricFlatDiskChart P (pointRegionMetricSpace ha y P)
        (f (shearedTopPoint Complex.I R s hs.le r)))) :
    ∃ h : ℝ, 0 < h ∧ s + h < delta ∧
      ∃ F : flatShearedRectangle Complex.I R (s + h) → P,
        (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
        ∀ x : flatShearedRectangle Complex.I R s,
          ∀ hx : x.1 ∈ flatShearedRectangle Complex.I R (s + h), F ⟨x.1, hx⟩ = f x := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  obtain ⟨h, hh, hhδ, G, hGold, hGlocal⟩ :=
    exists_normal_top_extension_of_full_top hR hs hsdelta f hf hregular
  let K := flatShearedRectangle Complex.I R s
  let K' := flatShearedRectangle Complex.I R (s + h)
  let U := interior K'
  have hvi : Complex.I.im ≠ 0 := by simp
  have hnewpos : 0 < s + h := add_pos hs hh
  have hU : Convex ℝ U := (flatShearedRectangle_convex Complex.I R (s + h)).interior
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
