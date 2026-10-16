import LeanResearch.RepulsiveCoulomb.MetricSupportedFlatPatchCompatibility

/-! NEW implementation after workspace loss. A full metric disk chart and an
actual old isometry give an actual whole-ball patch at a source point interior
to the supporting set. Only the H = univ use survives historically; the general
source hypothesis `q.1 ∈ interior H` is a newly specified, root-reviewed API.
No historical proof identity or pass is claimed. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- Construct an interior-supported patch by restricting a genuine full-disk
extension to a smaller ball contained in H. The whole smaller target ball is
covered, and agreement at every old source point is proved from the original
extension. No extension or new-patch compatibility is an input. -/
theorem exists_interior_supported_patch_extension {Y : Type*} [MetricSpace Y]
    {K H : Set ℂ} (hK : Convex ℝ K) (hne : (interior K).Nonempty)
    (f : K → Y) (hf : Isometry f) (q : K)
    (hqH : q.1 ∈ interior H) (C : MetricFlatDiskChart Y (f q)) :
    ∃ B : ℝ, 0 < B ∧
      ∃ e : supportedFlatPatch H q.1 B ≃ᵢ ball (f q) B,
        ∀ x : K, ∀ hx : x.1 ∈ supportedFlatPatch H q.1 B,
          (e ⟨x.1, hx⟩).1 = f x := by
  classical
  have hneball : (interior (K ∩ ball q.1 C.radius)).Nonempty := by
    rw [interior_inter, isOpen_ball.interior_eq]
    exact convex_interior_inter_ball_nonempty hK hne q.2 C.radius_pos
  obtain ⟨F, hF, hFold, hFrange⟩ :=
    exists_flat_disk_patch_extension f hf q C hneball
  obtain ⟨r, hr, hrH⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hqH)
  let B : ℝ := min C.radius r
  have hB : 0 < B := lt_min C.radius_pos hr
  have hBC : B ≤ C.radius := min_le_left _ _
  have hBr : B ≤ r := min_le_right _ _
  have hBH : ball q.1 B ⊆ H := by
    intro z hz
    exact hrH (lt_of_lt_of_le hz hBr)
  let A : Set ℂ := supportedFlatPatch H q.1 B
  let incl : A → ball q.1 C.radius := fun z ↦
    ⟨z.1, lt_of_lt_of_le z.2.1 hBC⟩
  have hq : q.1 ∈ ball q.1 C.radius := mem_ball_self C.radius_pos
  have hFq : F ⟨q.1, hq⟩ = f q := hFold q hq
  have htarget (z : A) : F (incl z) ∈ ball (f q) B := by
    change dist (F (incl z)) (f q) < B
    rw [← hFq, hF.dist_eq]
    exact z.2.1
  let G : A → ball (f q) B := fun z ↦ ⟨F (incl z), htarget z⟩
  have hG : Isometry G := by
    apply Isometry.of_dist_eq
    intro x z
    change dist (F (incl x)) (F (incl z)) = dist x.1 z.1
    exact hF.dist_eq _ _
  have hGsurj : Function.Surjective G := by
    intro y
    have hy : y.1 ∈ ball (f q) C.radius := lt_of_lt_of_le y.2 hBC
    rw [← hFrange] at hy
    obtain ⟨z, hz⟩ := hy
    have hzB : z.1 ∈ ball q.1 B := by
      change dist z (⟨q.1, hq⟩ : ball q.1 C.radius) < B
      rw [← hF.dist_eq, hFq, hz]
      exact y.2
    have hzA : z.1 ∈ A := ⟨hzB, hBH hzB⟩
    refine ⟨⟨z.1, hzA⟩, ?_⟩
    apply Subtype.ext
    change F (incl ⟨z.1, hzA⟩) = y.1
    have hincl : incl ⟨z.1, hzA⟩ = z := Subtype.ext rfl
    rw [hincl]
    exact hz
  let e : A ≃ᵢ ball (f q) B :=
    { toEquiv := Equiv.ofBijective G ⟨hG.injective, hGsurj⟩
      isometry_toFun := hG }
  refine ⟨B, hB, e, ?_⟩
  intro x hx
  change F (incl ⟨x.1, hx⟩) = f x
  exact hFold x (incl ⟨x.1, hx⟩).2

end RepulsiveCoulomb
