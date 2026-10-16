import LeanResearch.RepulsiveCoulomb.MetricHalfDiskAnchoredStageUniqueness
import LeanResearch.RepulsiveCoulomb.MetricHalfDiskBoundaryAlignment

/-! Genuine uniqueness of two flat maps with the same positive boundary-ray
interval. This is the ray version of the accepted complete-line comparison;
no complete boundary line is postulated or manufactured from a halfline. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem metricRay_stages_agree {Y : Type*} [MetricSpace Y]
    (ρ : NNReal → Y) (hρ : Isometry ρ)
    {c w : ℝ} (hw : 0 < w) (hwc : w < c)
    (C : MetricFlatHalfDiskChart Y (ρ ⟨c, hw.le.trans hwc.le⟩))
    {K L : Set ℂ} (hK : Convex ℝ K) (hclosed : IsClosed K)
    (hne : (interior K).Nonempty) (hKL : K ⊆ L)
    (hwindow : ∀ q ∈ Icc (c - w) (c + w), (q : ℂ) ∈ K)
    (f : K → Y) (g : L → Y) (hf : Isometry f) (hg : Isometry g)
    (hfb : ∀ t : NNReal, ∀ ht : (t : ℂ) ∈ K, f ⟨(t : ℂ), ht⟩ = ρ t)
    (hgb : ∀ t : NNReal, ∀ ht : (t : ℂ) ∈ L, g ⟨(t : ℂ), ht⟩ = ρ t)
    (hregular : ∀ z : K, z.1 ∈ interior K → Nonempty (MetricFlatDiskChart Y (f z))) :
    ∀ z : K, f z = g ⟨z.1, hKL z.2⟩ := by
  let B : ℝ := min w (C.radius / 2)
  have hB : 0 < B := lt_min hw (half_pos C.radius_pos)
  have hBw : B ≤ w := min_le_left _ _
  have hBC : B < C.radius := (min_le_right _ _).trans_lt (half_lt_self C.radius_pos)
  let τ : Icc (-B) B → NNReal := fun t ↦ ⟨c + t.1, by linarith [t.2.1]⟩
  have hτ : Isometry τ := by
    apply Isometry.of_dist_eq
    intro t u
    change |(c + t.1) - (c + u.1)| = |t.1 - u.1|
    congr 1
    ring
  have hτ0 : τ (complexSymmetricIntervalZero hB) = ⟨c, hw.le.trans hwc.le⟩ := by
    apply Subtype.ext
    simp [τ, complexSymmetricIntervalZero]
  obtain ⟨e, he0, heline⟩ := C.exists_aligned_to_short_interval hB hBC
    (ρ ∘ τ) (hρ.comp hτ) (congrArg ρ hτ0)
  let A : MetricFlatHalfDiskChart Y (ρ ⟨c, hw.le.trans hwc.le⟩) :=
    ⟨C.radius, C.radius_pos, e, he0⟩
  have hcK : (c : ℂ) ∈ K := hwindow c ⟨by linarith, by linarith⟩
  have hcbK : ((c + B : ℝ) : ℂ) ∈ K := hwindow (c + B) ⟨by linarith, by linarith⟩
  let cb : NNReal := ⟨c + B, by linarith⟩
  have hright (hmem : (B : ℂ) ∈ flatUpperDisk C.radius) :
      (e ⟨(B : ℂ), hmem⟩).1 = ρ cb := by
    let t : Icc (-B) B := ⟨B, by constructor <;> linarith⟩
    exact heline t
  exact metricHalfDisk_anchored_stage_unique A hB hBC hK hclosed hne hKL f g hf hg hcK hcbK
    (hfb ⟨c, hw.le.trans hwc.le⟩ hcK) (hgb ⟨c, hw.le.trans hwc.le⟩ (hKL hcK))
    ((hfb cb hcbK).trans (hright _).symm)
    ((hgb cb (hKL hcbK)).trans (hright _).symm) hregular

end RepulsiveCoulomb
