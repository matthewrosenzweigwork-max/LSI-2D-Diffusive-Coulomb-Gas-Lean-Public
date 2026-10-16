module

public import LeanResearch.RepulsiveCoulomb.PointFiniteBoundaryRayContacts
public import LeanResearch.RepulsiveCoulomb.PointGeodesicRadialGerms
public import LeanResearch.RepulsiveCoulomb.PointGeodesicStrictSectors

@[expose] public section

/-! Source-only draft. At the far contact, the reversed stopped ray and the
chosen incident old-boundary piece have distinct radial germs in one actual
cone chart. Both complementary physical intervals are positive, so either
actual Jordan-side choice has turn strictly below pi. This file never supplies
an unproved identification of the Jordan side or retained interval as a field. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- Boundary avoidance separates synchronized equal-radius inward germs.
The cone chart, radiality and both strict physical sector bounds are outputs.
The old germ is only one incident finite boundary piece, not the whole arc. -/
theorem exists_boundary_disjoint_geodesic_germ_sectors {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ} {p : ℂ}
    (γ η : ℝ → ℂ) {L : ℝ} (hL : 0 < L)
    (hγ0 : γ 0 = p) (hη0 : η 0 = p)
    (hγd : ∀ s ∈ Icc (0 : ℝ) L, ∀ t ∈ Icc (0 : ℝ) L,
      (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = dist s t)
    (hηd : ∀ s ∈ Icc (0 : ℝ) L, ∀ t ∈ Icc (0 : ℝ) L,
      (pointSmoothConformalEDist a y (η s) (η t)).toReal = dist s t)
    (hγavoid : ∀ t ∈ Ioo (0 : ℝ) L, γ t ∉ frontier P)
    (hηboundary : ∀ t ∈ Icc (0 : ℝ) L, η t ∈ frontier P) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ R τ : ℝ,
      0 < R ∧ 0 < τ ∧ τ < L ∧ τ ≤ R ∧ e p = 0 ∧
      {u : ℂ | (pointSmoothConformalEDist a y u p).toReal ≤ R} ⊆ e.source ∧
      (∀ u, (pointSmoothConformalEDist a y u p).toReal ≤ R →
        ∀ v, (pointSmoothConformalEDist a y v p).toReal ≤ R →
          (pointSmoothConformalEDist a y u v).toReal = pointClassicalConeDist a y p (e u) (e v)) ∧
      e (γ τ) ≠ e (η τ) ∧
      (∀ u : unitInterval,
        e (γ (u.1 * τ)) = u.1 • e (γ τ) ∧
        e (η (u.1 * τ)) = u.1 • e (η τ)) ∧
      0 < coneShortSectorAngle (coalescedPointExponent a y p / 2) (e (γ τ)) (e (η τ)) ∧
      0 < coneLongSectorAngle (coalescedPointExponent a y p / 2) (e (γ τ)) (e (η τ)) ∧
      Real.pi - coneShortSectorAngle (coalescedPointExponent a y p / 2)
        (e (γ τ)) (e (η τ)) < Real.pi ∧
      Real.pi - coneLongSectorAngle (coalescedPointExponent a y p / 2)
        (e (γ τ)) (e (η τ)) < Real.pi := by
  obtain ⟨e, R, hR, hep, hsource, hmetric, hradial⟩ :=
    exists_pointConformal_radial_metric_disk ha y p
  let τ : ℝ := min L R / 2
  have hτ : 0 < τ := div_pos (lt_min hL hR) (by norm_num)
  have hτL : τ < L := by dsimp [τ]; linarith [min_le_left L R]
  have hτR : τ ≤ R := by dsimp [τ]; linarith [min_le_right L R]
  have hmem : τ ∈ Icc (0 : ℝ) L := ⟨hτ.le, hτL.le⟩
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) L := ⟨le_rfl, hL.le⟩
  have hrγ : (pointSmoothConformalEDist a y (γ τ) p).toReal = τ := by
    simpa only [hγ0, Real.dist_eq, sub_zero, abs_of_pos hτ] using hγd τ hmem 0 hzero
  have hrη : (pointSmoothConformalEDist a y (η τ) p).toReal = τ := by
    simpa only [hη0, Real.dist_eq, sub_zero, abs_of_pos hτ] using hηd τ hmem 0 hzero
  have hγR : (pointSmoothConformalEDist a y (γ τ) p).toReal ≤ R := hrγ.trans_le hτR
  have hηR : (pointSmoothConformalEDist a y (η τ) p).toReal ≤ R := hrη.trans_le hτR
  have hne : γ τ ≠ η τ := by
    intro he
    exact hγavoid τ ⟨hτ, hτL⟩ (he.symm ▸ hηboundary τ hmem)
  have hene : e (γ τ) ≠ e (η τ) :=
    fun he => hne (e.injOn (hsource hγR) (hsource hηR) he)
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ R := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact hR.le
  have hnorm : ‖e (γ τ)‖ = ‖e (η τ)‖ := by
    have h := hrγ.trans hrη.symm
    rw [hmetric _ hγR p hpp, hmetric _ hηR p hpp, hep,
      pointClassicalConeDist_apex, pointClassicalConeDist_apex] at h
    exact h
  have hsectors := cone_equal_radius_sector_turns_lt_pi
    (α := coalescedPointExponent a y p / 2)
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)) hnorm hene
  have hsmall : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) L := Icc_subset_Icc le_rfl hτL.le
  have hγgeo := lineCapSegment_metricOn y γ hτ.le
    (fun s hs t ht => hγd s (hsmall hs) t (hsmall ht))
  have hηgeo := lineCapSegment_metricOn y η hτ.le
    (fun s hs t ht => hηd s (hsmall hs) t (hsmall ht))
  rw [hγ0] at hγgeo
  rw [hη0] at hηgeo
  have hγrad := hradial (γ τ) hγR (lineCapSegment γ 0 τ)
    ((lineCapSegment_zero γ 0 τ).trans hγ0) (lineCapSegment_one γ 0 τ) hγgeo
  have hηrad := hradial (η τ) hηR (lineCapSegment η 0 τ)
    ((lineCapSegment_zero η 0 τ).trans hη0) (lineCapSegment_one η 0 τ) hηgeo
  refine ⟨e, R, τ, hR, hτ, hτL, hτR, hep, hsource, hmetric, hene, ?_, hsectors⟩
  intro u
  simpa only [lineCapSegment, sub_zero, zero_add] using And.intro (hγrad u) (hηrad u)

/-- A first-return gap supplies the required far-contact avoidance after
reversing the actual ray. The old boundary germ is supplied by an incident
old piece, with its actual arclength metric law on a positive interval. -/
theorem firstReturn_reversed_germ_data {m : ℕ} {a : Fin m → ℝ}
    (y : Fin m → ℂ) {P : Set ℂ} (r : ℝ → ℂ) {z w L : ℝ}
    (hL : 0 < L) (hLgap : L ≤ w - z)
    (hd : ∀ s ∈ Icc z w, ∀ t ∈ Icc z w,
      (pointSmoothConformalEDist a y (r s) (r t)).toReal = dist s t)
    (hgap : ∀ t ∈ Ioo z w, r t ∉ frontier P) :
    (∀ s ∈ Icc (0 : ℝ) L, ∀ t ∈ Icc (0 : ℝ) L,
      (pointSmoothConformalEDist a y (r (w - s)) (r (w - t))).toReal = dist s t) ∧
      ∀ t ∈ Ioo (0 : ℝ) L, r (w - t) ∉ frontier P := by
  constructor
  · intro s hs t ht
    rw [hd (w - s) (by constructor <;> linarith [hs.1, hs.2])
      (w - t) (by constructor <;> linarith [ht.1, ht.2]), Real.dist_eq, Real.dist_eq]
    rw [show w - s - (w - t) = t - s by ring, abs_sub_comm]
  · intro t ht
    exact hgap (w - t) (by constructor <;> linarith [ht.1, ht.2])

end RepulsiveCoulomb
