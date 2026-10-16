import LeanResearch.RepulsiveCoulomb.ConnectedEuclideanMotionGerms
import LeanResearch.RepulsiveCoulomb.FiniteClosedPieceMetricBounds
import LeanResearch.RepulsiveCoulomb.ComplexSubsetIsometryExtension

/-! SOURCE-ONLY, UNCOMPILED. A genuine local homeomorphism pieced from full
Euclidean motions is locally rigid. Forward and inverse finite closed-cover
bounds supply the no-fold argument. Motions on adjacent pieces are never
identified merely from their common one-dimensional seam. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_euclideanMotion_germ_of_finite_piecewise_motions
    {ι : Type*} [Finite ι] (e : OpenPartialHomeomorph ℂ ℂ)
    {x : ℂ} {R : ℝ} (hR : 0 < R) (hsource : ball x R ⊆ e.source)
    (S : ι → Set ℂ)
    (hclosed : ∀ i, IsClosed {z : ball x R | z.1 ∈ S i})
    (hcover : ∀ z ∈ ball x R, ∃ i, z ∈ S i)
    (motion : ι → (ℂ ≃ᵢ ℂ))
    (hformula : ∀ i z, z ∈ ball x R → z ∈ S i → e z = motion i z) :
    ∃ A : ℂ ≃ᵢ ℂ, (e : ℂ → ℂ) =ᶠ[𝓝 x] (A : ℂ → ℂ) := by
  let U := ball x R
  have hxU : x ∈ U := mem_ball_self hR
  have hxe : x ∈ e.source := hsource hxU
  have hF : LipschitzOnWith 1 e U := by
    apply lipschitzOnWith_of_finite_closed_cover_of_convex U (convex_ball _ _)
      S hclosed hcover
    intro i
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    rw [hformula i z hz.1 hz.2, hformula i w hw.1 hw.2, (motion i).dist_eq]
    simp only [NNReal.coe_one, one_mul, le_refl]
  have hnear : {y | y ∈ e.target ∧ e.symm y ∈ U} ∈ 𝓝 (e x) := by
    have hpre : ∀ᶠ y in 𝓝 (e x), e.symm y ∈ U := by
      have hxinv : e.symm (e x) ∈ U := by rw [e.left_inv hxe]; exact hxU
      exact (e.symm.continuousAt (e.map_source hxe)).tendsto.eventually
        (isOpen_ball.mem_nhds hxinv)
    exact Filter.Eventually.and (e.open_target.mem_nhds (e.map_source hxe)) hpre
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  let V := ball (e x) δ
  let T : ι → Set ℂ := fun i ↦ {z | e.symm z ∈ S i}
  let G : V → U := fun z ↦ ⟨e.symm z.1, (hδsub z.2).2⟩
  have hGcontinuous : Continuous G := by
    apply Continuous.subtype_mk
    exact (e.symm.continuousOn.mono (fun z hz ↦ (hδsub hz).1)).restrict
  have hTclosed : ∀ i, IsClosed {z : V | z.1 ∈ T i} := fun i ↦ (hclosed i).preimage hGcontinuous
  have hTcover : ∀ z ∈ V, ∃ i, z ∈ T i := fun z hz ↦ hcover (e.symm z) (hδsub hz).2
  have hG : LipschitzOnWith 1 e.symm V := by
    apply lipschitzOnWith_of_finite_closed_cover_of_convex V (convex_ball _ _)
      T hTclosed hTcover
    intro i
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    have hz' : e.target z := (hδsub hz.1).1
    have hw' : e.target w := (hδsub hw.1).1
    have hez := hformula i (e.symm z) (hδsub hz.1).2 hz.2
    have hew := hformula i (e.symm w) (hδsub hw.1).2 hw.2
    rw [e.right_inv hz'] at hez
    rw [e.right_inv hw'] at hew
    rw [← (motion i).dist_eq, ← hez, ← hew]
    simp only [NNReal.coe_one, one_mul, le_refl]
  let W := U ∩ e ⁻¹' V
  have hWopen : IsOpen W :=
    (e.continuousOn.mono hsource).isOpen_inter_preimage isOpen_ball isOpen_ball
  have hxW : x ∈ W := ⟨hxU, mem_ball_self hδ⟩
  have hiso : Isometry (fun z : W ↦ e z.1) := by
    apply Isometry.of_dist_eq
    intro z w
    change dist (e z.1) (e w.1) = dist z.1 w.1
    apply le_antisymm
    · simpa only [NNReal.coe_one, one_mul] using hF.dist_le_mul z.1 z.2.1 w.1 w.2.1
    · have h := hG.dist_le_mul (e z.1) z.2.2 (e w.1) w.2.2
      simpa only [e.left_inv (hsource z.2.1), e.left_inv (hsource w.2.1),
        NNReal.coe_one, one_mul] using h
  obtain ⟨A, hA⟩ := exists_complex_isometry_extension_of_open_overlap
    (fun z : W ↦ e z.1) hiso (by rw [hWopen.interior_eq]; exact ⟨x, hxW⟩)
  refine ⟨A, ?_⟩
  filter_upwards [hWopen.mem_nhds hxW] with z hz
  exact (hA ⟨z, hz⟩).symm

end RepulsiveCoulomb
