import LeanResearch.RepulsiveCoulomb.ComplexSubsetIsometryExtension

/-! NEW implementation after workspace loss. An actual whole-ball Euclidean
chart and the old map determine the new patch by accepted plane rigidity.
No patch existence, agreement, or surjectivity certificate is an input. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

structure MetricFlatDiskChart (Y : Type*) [MetricSpace Y] (p : Y) where
  radius : ℝ
  radius_pos : 0 < radius
  toEuclidean : ball p radius ≃ᵢ ball (0 : ℂ) radius
  center : (toEuclidean ⟨p, mem_ball_self radius_pos⟩).1 = 0

theorem exists_flat_disk_patch_extension {Y : Type*} [MetricSpace Y]
    {K : Set ℂ} (f : K → Y) (hf : Isometry f) (q : K)
    (C : MetricFlatDiskChart Y (f q))
    (hne : (interior (K ∩ ball q.1 C.radius)).Nonempty) :
    ∃ F : ball q.1 C.radius → Y,
      Isometry F ∧
      (∀ x : K, ∀ hx : x.1 ∈ ball q.1 C.radius, F ⟨x.1, hx⟩ = f x) ∧
      range F = ball (f q) C.radius := by
  let U : Set ℂ := K ∩ ball q.1 C.radius
  have htarget (z : U) : f ⟨z.1, z.2.1⟩ ∈ ball (f q) C.radius := by
    change dist (f ⟨z.1, z.2.1⟩) (f q) < C.radius
    rw [hf.dist_eq]
    exact z.2.2
  let τ : U → ℂ := fun z ↦ (C.toEuclidean ⟨f ⟨z.1, z.2.1⟩, htarget z⟩).1
  have hτ : Isometry τ := by
    apply Isometry.of_dist_eq
    intro z w
    change dist (C.toEuclidean ⟨f ⟨z.1, z.2.1⟩, htarget z⟩)
      (C.toEuclidean ⟨f ⟨w.1, w.2.1⟩, htarget w⟩) = dist z w
    rw [C.toEuclidean.dist_eq]
    exact hf.dist_eq ⟨z.1, z.2.1⟩ ⟨w.1, w.2.1⟩
  obtain ⟨e, he⟩ := exists_complex_isometry_extension_of_open_overlap τ hτ hne
  have hqU : q.1 ∈ U := ⟨q.2, mem_ball_self C.radius_pos⟩
  have heq0 : e q.1 = 0 := by
    have h := he ⟨q.1, hqU⟩
    change e q.1 = (C.toEuclidean ⟨f q, mem_ball_self C.radius_pos⟩).1 at h
    exact h.trans C.center
  have hcoord (z : ball q.1 C.radius) : e z.1 ∈ ball (0 : ℂ) C.radius := by
    change dist (e z.1) 0 < C.radius
    rw [← heq0, e.dist_eq]
    exact z.2
  let F : ball q.1 C.radius → Y := fun z ↦ (C.toEuclidean.symm ⟨e z.1, hcoord z⟩).1
  have hF : Isometry F := by
    apply Isometry.of_dist_eq
    intro z w
    change dist (C.toEuclidean.symm ⟨e z.1, hcoord z⟩)
      (C.toEuclidean.symm ⟨e w.1, hcoord w⟩) = dist z w
    rw [C.toEuclidean.symm.dist_eq]
    change dist (e z.1) (e w.1) = dist z.1 w.1
    exact e.dist_eq _ _
  refine ⟨F, hF, ?_, ?_⟩
  · intro x hx
    have hxU : x.1 ∈ U := ⟨x.2, hx⟩
    have hfx : f x ∈ ball (f q) C.radius := htarget ⟨x.1, hxU⟩
    have harg : (⟨e x.1, hcoord ⟨x.1, hx⟩⟩ : ball (0 : ℂ) C.radius) =
        C.toEuclidean ⟨f x, hfx⟩ := by
      apply Subtype.ext
      exact he ⟨x.1, hxU⟩
    change (C.toEuclidean.symm ⟨e x.1, hcoord ⟨x.1, hx⟩⟩).1 = f x
    rw [harg, C.toEuclidean.symm_apply_apply]
  · apply Subset.antisymm
    · rintro y ⟨z, rfl⟩
      exact (C.toEuclidean.symm ⟨e z.1, hcoord z⟩).2
    · intro y hy
      let yB : ball (f q) C.radius := ⟨y, hy⟩
      let w : ℂ := e.symm (C.toEuclidean yB).1
      have hew : e w = (C.toEuclidean yB).1 := e.apply_symm_apply _
      have hw : w ∈ ball q.1 C.radius := by
        change dist w q.1 < C.radius
        rw [← e.dist_eq, hew, heq0]
        exact (C.toEuclidean yB).2
      refine ⟨⟨w, hw⟩, ?_⟩
      have harg : (⟨e w, hcoord ⟨w, hw⟩⟩ : ball (0 : ℂ) C.radius) =
          C.toEuclidean yB := Subtype.ext hew
      change (C.toEuclidean.symm ⟨e w, hcoord ⟨w, hw⟩⟩).1 = y
      rw [harg, C.toEuclidean.symm_apply_apply]

end RepulsiveCoulomb
