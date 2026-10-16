module

public import LeanResearch.RepulsiveCoulomb.MetricRelativeHalfDiskPatchExtension

@[expose] public section

/-! ISOLATED SOURCE-ONLY DRAFT. A closed flat extension cannot choose a
different continuation of an old boundary edge inside a genuine retained
halfdisk. The actual arclength interval and two old anchors force the new
boundary values. No zero ambient exponent or complete boundary line is used. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem metricHalfDisk_boundary_continuation_unique {Y : Type*} [MetricSpace Y]
    {K : Set ℂ} (F : K → Y) (hF : Isometry F) (q q₁ : K)
    (E : ℂ ≃ᵢ ℂ) (hq : E q.1 = 0)
    (C : MetricFlatHalfDiskChart Y (F q))
    {L : ℝ} (hL : 0 < L) (hLC : L < C.radius)
    (ρ : Icc (-L) L → Y) (hρ : Isometry ρ)
    (hρzero : ρ (complexSymmetricIntervalZero hL) = F q)
    (b : Icc (-L) L) (hb : b.1 ≠ 0)
    (hq₁ : E q₁.1 = (b.1 : ℂ)) (hρb : ρ b = F q₁)
    (x : K) (t : Icc (-L) L) (hxt : E x.1 = (t.1 : ℂ)) : F x = ρ t := by
  obtain ⟨D, hD0, hDline⟩ := C.exists_aligned_to_short_interval hL hLC ρ hρ hρzero
  have htmem : (t.1 : ℂ) ∈ flatUpperDisk C.radius := (halfDiskIntervalReal hLC t).2
  have hbmem : (b.1 : ℂ) ∈ flatUpperDisk C.radius := (halfDiskIntervalReal hLC b).2
  have h0mem : (0 : ℂ) ∈ flatUpperDisk C.radius := (flatUpperDiskZero C.radius_pos).2
  have hxball : F x ∈ ball (F q) C.radius := by
    change dist (F x) (F q) < C.radius
    rw [hF.dist_eq]
    change dist x.1 q.1 < C.radius
    rw [← E.dist_eq, hxt, hq, dist_zero_right]
    exact htmem.1
  have htball : ρ t ∈ ball (F q) C.radius := by
    rw [← hDline t]
    exact (D (halfDiskIntervalReal hLC t)).2
  have hzero : dist (⟨F x, hxball⟩ : ball (F q) C.radius) (D ⟨0, h0mem⟩) =
      dist (⟨ρ t, htball⟩ : ball (F q) C.radius) (D ⟨0, h0mem⟩) := by
    change dist (F x) (D ⟨0, h0mem⟩).1 = dist (ρ t) (D ⟨0, h0mem⟩).1
    have hD0' : (D ⟨0, h0mem⟩).1 = F q := hD0
    rw [hD0', hF.dist_eq, ← hρzero, hρ.dist_eq]
    change dist x.1 q.1 = dist t.1 (0 : ℝ)
    rw [← E.dist_eq, hxt, hq]
    change dist (t.1 : ℂ) (0 : ℂ) = dist t.1 (0 : ℝ)
    simp
  have hsecond : dist (⟨F x, hxball⟩ : ball (F q) C.radius) (D ⟨(b.1 : ℂ), hbmem⟩) =
      dist (⟨ρ t, htball⟩ : ball (F q) C.radius) (D ⟨(b.1 : ℂ), hbmem⟩) := by
    have hDb : (D ⟨(b.1 : ℂ), hbmem⟩).1 = ρ b := hDline b
    change dist (F x) (D ⟨(b.1 : ℂ), hbmem⟩).1 = dist (ρ t) (D ⟨(b.1 : ℂ), hbmem⟩).1
    rw [hDb, hρ.dist_eq, hρb, hF.dist_eq]
    change dist x.1 q₁.1 = dist t.1 b.1
    rw [← E.dist_eq, hxt, hq₁]
    simp only [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, Real.dist_eq]
  exact congrArg Subtype.val (metricHalfDisk_two_anchor_unique D (Ne.symm hb)
    h0mem hbmem hzero hsecond)

end RepulsiveCoulomb
