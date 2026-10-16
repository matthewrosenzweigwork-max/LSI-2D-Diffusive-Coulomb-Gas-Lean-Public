module

public import LeanResearch.RepulsiveCoulomb.MetricHalfDiskAnchoredStageUniqueness
public import LeanResearch.RepulsiveCoulomb.MetricHalfDiskBoundaryAlignment

@[expose] public section

/-! NEW post-loss stage compatibility. Actual arclength alignment of one
center halfdisk supplies the common two anchors. Local agreement and its
propagation are derived from genuine charts, never assumed for the stages. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem metricFullLine_stages_agree {Y : Type*} [MetricSpace Y]
    (line : ℝ → Y) (hline : Isometry line) (offset center : ℝ)
    (C : MetricFlatHalfDiskChart Y (line (offset + center)))
    {K L : Set ℂ} (hK : Convex ℝ K) (hclosed : IsClosed K)
    (hne : (interior K).Nonempty) (hKL : K ⊆ L)
    {w : ℝ} (hw : 0 < w)
    (hwindow : ∀ q ∈ Icc (center - w) (center + w), (q : ℂ) ∈ K)
    (f : K → Y) (g : L → Y) (hf : Isometry f) (hg : Isometry g)
    (hfb : ∀ q : ℝ, ∀ hq : (q : ℂ) ∈ K, f ⟨(q : ℂ), hq⟩ = line (offset + q))
    (hgb : ∀ q : ℝ, ∀ hq : (q : ℂ) ∈ L, g ⟨(q : ℂ), hq⟩ = line (offset + q))
    (hregular : ∀ z : K, z.1 ∈ interior K → Nonempty (MetricFlatDiskChart Y (f z))) :
    ∀ z : K, f z = g ⟨z.1, hKL z.2⟩ := by
  let B : ℝ := min w (C.radius / 2)
  have hB : 0 < B := lt_min hw (half_pos C.radius_pos)
  have hBw : B ≤ w := min_le_left _ _
  have hBC : B < C.radius := (min_le_right _ _).trans_lt (half_lt_self C.radius_pos)
  let rho : Icc (-B) B → Y := fun t ↦ line (offset + (center + t.1))
  have hrho : Isometry rho := by
    apply Isometry.of_dist_eq
    intro r t
    change dist (line (offset + (center + r.1))) (line (offset + (center + t.1))) = dist r t
    rw [hline.dist_eq]
    change |(offset + (center + r.1)) - (offset + (center + t.1))| = |r.1 - t.1|
    congr 1
    ring
  have hrho0 : rho (complexSymmetricIntervalZero hB) = line (offset + center) := by
    simp only [rho, complexSymmetricIntervalZero, add_zero]
  obtain ⟨e, he0, heline⟩ := C.exists_aligned_to_short_interval hB hBC rho hrho hrho0
  let A : MetricFlatHalfDiskChart Y (line (offset + center)) :=
    ⟨C.radius, C.radius_pos, e, he0⟩
  have hcK : (center : ℂ) ∈ K := hwindow center ⟨by linarith, by linarith⟩
  have hcbK : ((center + B : ℝ) : ℂ) ∈ K :=
    hwindow (center + B) ⟨by linarith, by linarith⟩
  have hright (hmem : (B : ℂ) ∈ flatUpperDisk C.radius) :
      (e ⟨(B : ℂ), hmem⟩).1 = line (offset + (center + B)) := by
    let t : Icc (-B) B := ⟨B, by constructor <;> linarith⟩
    have h := heline t
    change (e ⟨(B : ℂ), hmem⟩).1 = line (offset + (center + B)) at h
    exact h
  exact metricHalfDisk_anchored_stage_unique A hB hBC hK hclosed hne hKL f g hf hg hcK hcbK
    (hfb center hcK) (hgb center (hKL hcK))
    ((hfb (center + B) hcbK).trans (hright _).symm)
    ((hgb (center + B) (hKL hcbK)).trans (hright _).symm) hregular

end RepulsiveCoulomb
