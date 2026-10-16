module

public import LeanResearch.RepulsiveCoulomb.PointRetainedCappedSectorSeed
public import LeanResearch.RepulsiveCoulomb.PointSectorReturnActualCleanGerm

@[expose] public section

/-! ISOLATED SOURCE-ONLY DRAFT. Construct the actual reflected retained cone
chart and use the genuine clean-ray endpoint theorem to orient the seed at the
lower endpoint. No principal-angle truncation or assumed bottom orientation. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem complex_abs_arg_conj (z : ℂ) : |Complex.arg (star z)| = |Complex.arg z| := by
  change |Complex.arg ((starRingEnd ℂ) z)| = _
  rw [Complex.arg_conj]
  split_ifs <;> simp_all only [abs_neg]

theorem classicalCone_conj_dist {α : ℝ} (hα : 0 ≤ α) (x z : ℂ) :
    @dist ℂ (classicalConeMetricSpace α hα).toDist (star x) (star z) =
      @dist ℂ (classicalConeMetricSpace α hα).toDist x z := by
  rcases hα.eq_or_lt with he | hp
  · subst α
    rw [classicalCone_zero_dist, classicalCone_zero_dist, ← star_sub, norm_star]
  · rw [classicalCone_distance_formula hp, classicalCone_distance_formula hp,
      norm_star, norm_star, ← star_div₀, complex_abs_arg_conj]

theorem pointClassicalConeDist_conj {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (p x z : ℂ) :
    pointClassicalConeDist a y p (star x) (star z) = pointClassicalConeDist a y p x z :=
  classicalCone_conj_dist
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)) x z

theorem pointRadialSectorPoint_conj (r θ : ℝ) :
    star (pointRadialSectorPoint r θ) = pointRadialSectorPoint r (-θ) := by
  rw [← sectorPolar_eq_pointRadialSectorPoint r θ,
    ← sectorPolar_eq_pointRadialSectorPoint r (-θ)]
  apply Complex.ext <;>
    simp [Complex.star_def, sectorPolar_re, sectorPolar_im]

theorem pointClosedRadialInterval_conj_iff (R lo hi : ℝ) (w : ℂ) :
    star w ∈ pointClosedRadialInterval R (-hi) (-lo) ↔
      w ∈ pointClosedRadialInterval R lo hi := by
  constructor
  · rintro ⟨r, hr, θ, hθ, he⟩
    refine ⟨r, hr, -θ, ⟨by linarith [hθ.2], by linarith [hθ.1]⟩, ?_⟩
    simpa only [star_star, pointRadialSectorPoint_conj] using congrArg star he
  · rintro ⟨r, hr, θ, hθ, rfl⟩
    exact ⟨r, hr, -θ, ⟨by linarith [hθ.2], by linarith [hθ.1]⟩,
      pointRadialSectorPoint_conj r θ⟩

theorem PointRetainedConeNeighborhood.exists_reflect
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) :
    ∃ D : PointRetainedConeNeighborhood a y P p,
      D.radius = C.radius ∧ D.chart.source = C.chart.source ∧
      (∀ z, D.chart z = star (C.chart z)) ∧ D.lo = -C.hi ∧ D.hi = -C.lo ∧
      D.flatPhysicalWidth = C.flatPhysicalWidth ∧ (D.Admissible ↔ C.Admissible) := by
  let F := C.chart.trans Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph
  have hF (z : ℂ) : F z = star (C.chart z) := rfl
  have hsrc : F.source = C.chart.source := by simp [F]
  have hconj : BijOn (star : ℂ → ℂ)
      {z : ℂ | ‖z‖ ≤ C.radius} {z : ℂ | ‖z‖ ≤ C.radius} := by
    refine ⟨?_, fun _ _ _ _ he ↦ star_injective he, ?_⟩
    · intro z hz
      simpa only [mem_setOf_eq, norm_star] using hz
    · intro z hz
      exact ⟨star z, by simpa only [mem_setOf_eq, norm_star] using hz, star_star z⟩
  let D : PointRetainedConeNeighborhood a y P p :=
    { chart := F
      radius := C.radius
      radius_pos := C.radius_pos
      center := by rw [hF, C.center, star_zero]
      source := by rw [hsrc]; exact C.source
      onto := hconj.comp C.onto
      metric := by
        intro z hz w hw
        rw [hF, hF, pointClassicalConeDist_conj]
        exact C.metric z hz w hw
      lo := -C.hi
      hi := -C.lo
      width_pos := by linarith [C.width_pos]
      width_le_full := by linarith [C.width_le_full]
      retained := by
        intro z hz
        rw [hF]
        exact (C.retained z hz).trans
          (pointClosedRadialInterval_conj_iff C.radius C.lo C.hi (C.chart z)).symm }
  refine ⟨D, rfl, hsrc, hF, rfl, rfl, ?_, ?_⟩
  · unfold PointRetainedConeNeighborhood.flatPhysicalWidth
    change _ * (-C.lo - -C.hi) = _ * (C.hi - C.lo)
    ring
  · unfold PointRetainedConeNeighborhood.Admissible
    change (Real.pi ≤ _ * (2 * Real.pi - (-C.lo - -C.hi))) ↔
      (Real.pi ≤ _ * (2 * Real.pi - (C.hi - C.lo)))
    rw [show -C.lo - -C.hi = C.hi - C.lo by ring]

/-- Choose the actual lower-endpoint orientation from the actual clean
metric ray. Reflection is constructed precisely when the ray occupied the
upper endpoint in the old chart. -/
theorem exists_actual_clean_lower_retained_chart
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hC : C.Admissible) (hP : IsClosed P)
    (ρ : ℝ → ℂ) (hρ0 : ρ 0 = p)
    (hρd : ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (hρfront : ∀ t ∈ Ici (0 : ℝ), ρ t ∈ frontier P) :
    ∃ D : PointRetainedConeNeighborhood a y P p,
      D.Admissible ∧ D.flatPhysicalWidth = C.flatPhysicalWidth ∧
      ∃ T : ℝ, 0 < T ∧ T < D.radius ∧
        ∀ t ∈ Icc (0 : ℝ) T, D.chart (ρ t) = pointRadialSectorPoint t D.lo := by
  obtain ⟨T, ξ, hT, hTR, hξ, hξend, hgerm⟩ :=
    exists_clean_metric_ray_retained_endpoint_germ C hP ρ hρ0 hρd hρfront
  rcases hξend with hlo | hhi
  · refine ⟨C, hC, rfl, T, hT, hTR, ?_⟩
    intro t ht
    simpa only [hlo] using (hgerm t ht).2.1
  · obtain ⟨D, hDR, _, hDchart, hDlo, _, hDwidth, hDadm⟩ := C.exists_reflect
    refine ⟨D, hDadm.mpr hC, hDwidth, T, hT, hDR.symm ▸ hTR, ?_⟩
    intro t ht
    rw [hDchart, (hgerm t ht).2.1, pointRadialSectorPoint_conj, hhi, hDlo]

end RepulsiveCoulomb
