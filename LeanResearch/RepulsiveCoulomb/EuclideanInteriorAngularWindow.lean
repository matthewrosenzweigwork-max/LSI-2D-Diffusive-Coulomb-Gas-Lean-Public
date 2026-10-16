module

public import LeanResearch.RepulsiveCoulomb.EuclideanClosedSectorSource

@[expose] public section

/-! ISOLATED SOURCE-ONLY DRAFT. Closed angular windows strictly inside the
requested positive sector. Their radial endpoint rays are interior directions,
so all points of their outer circular fronts can have full metric disk charts.
-/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- The lower supporting inequality removes directions below a without
choosing a principal argument at the apex. -/
def flatInteriorAngularWindow (a b : ℝ) : Set ℂ :=
  closedEuclideanSector b ∩ {z | 0 ≤ Real.cos a * z.im - Real.sin a * z.re}

theorem complex_support_side (z : ℂ) (θ : ℝ) :
    Real.cos θ * z.im - Real.sin θ * z.re = ‖z‖ * Real.sin (Complex.arg z - θ) := by
  rw [Real.sin_sub]
  calc
    _ = (‖z‖ * Real.sin (Complex.arg z)) * Real.cos θ -
        (‖z‖ * Real.cos (Complex.arg z)) * Real.sin θ := by
          rw [Complex.norm_mul_sin_arg, Complex.norm_mul_cos_arg]
          ring
    _ = _ := by ring

theorem sectorPolar_support_side (r φ θ : ℝ) :
    Real.cos θ * (sectorPolar r φ).im - Real.sin θ * (sectorPolar r φ).re =
      r * Real.sin (φ - θ) := by
  rw [sectorPolar_im, sectorPolar_re, Real.sin_sub]
  ring

/-- The angular window is exactly its full literal argument interval off the
apex. Both angular endpoint rays are included. -/
theorem flatInteriorAngularWindow_arg {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hbπ : b ≤ Real.pi) {z : ℂ} (hz : z ∈ flatInteriorAngularWindow a b) (hz0 : z ≠ 0) :
    Complex.arg z ∈ Icc a b := by
  refine ⟨?_, hz.1.2⟩
  by_contra hn
  have hlt : Complex.arg z < a := lt_of_not_ge hn
  have hs : 0 < Real.sin (a - Complex.arg z) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hlt) (by linarith [hz.1.1])
  have hs' : Real.sin (Complex.arg z - a) < 0 := by
    rw [show Complex.arg z - a = -(a - Complex.arg z) by ring, Real.sin_neg]
    exact neg_neg_of_pos hs
  have hneg := mul_neg_of_pos_of_neg (norm_pos_iff.mpr hz0) hs'
  have hside := hz.2
  change 0 ≤ Real.cos a * z.im - Real.sin a * z.re at hside
  rw [complex_support_side] at hside
  exact (not_lt_of_ge hside) hneg

theorem flatInteriorAngularWindow_convex {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hbπ : b ≤ Real.pi) :
    Convex ℝ (flatInteriorAngularWindow a b) := by
  apply (closedEuclideanSector_convex (ha.trans hab) hbπ).inter
  intro x hx z hz c d hc hd hcd
  change 0 ≤ Real.cos a * (c • x + d • z).im - Real.sin a * (c • x + d • z).re
  simp only [Complex.add_im, Complex.smul_im, Complex.add_re, Complex.smul_re, smul_eq_mul]
  have h := add_nonneg (mul_nonneg hc hx) (mul_nonneg hd hz)
  nlinarith

theorem flatInteriorAngularWindow_isClosed {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hbπ : b ≤ Real.pi) :
    IsClosed (flatInteriorAngularWindow a b) :=
  (closedEuclideanSector_isClosed (ha.trans hab) hbπ).inter
    (isClosed_le continuous_const (by fun_prop))

theorem flatInteriorAngularWindow_nonneg_smul {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hbπ : b ≤ Real.pi)
    {z : ℂ} (hz : z ∈ flatInteriorAngularWindow a b) {t : ℝ} (ht : 0 ≤ t) :
    t • z ∈ flatInteriorAngularWindow a b := by
  refine ⟨closedEuclideanSector_nonneg_smul (ha.trans hab) hbπ hz.1 ht, ?_⟩
  change 0 ≤ Real.cos a * (t • z).im - Real.sin a * (t • z).re
  simp only [Complex.smul_im, Complex.smul_re, smul_eq_mul]
  have h := mul_nonneg ht hz.2
  nlinarith

@[simp] theorem zero_mem_flatInteriorAngularWindow {a b : ℝ} (hb : 0 ≤ b) :
    (0 : ℂ) ∈ flatInteriorAngularWindow a b := by
  simp [flatInteriorAngularWindow, closedEuclideanSector, hb]

/-- A positive-radius angular window is genuinely two-dimensional. -/
theorem flatInteriorAngularWindow_truncation_interior_nonempty {a b R : ℝ}
    (ha : 0 < a) (hab : a < b) (hbπ : b ≤ Real.pi) (hR : 0 < R) :
    (interior (flatRadialTruncation (flatInteriorAngularWindow a b) R)).Nonempty := by
  let c := (a + b) / 2
  have hac : a < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  have hc : 0 < c := ha.trans hac
  have hcπ : c < Real.pi := hcb.trans_le hbπ
  let V : Set ℂ := {z | 0 < z.im ∧
    Real.cos b * z.im - Real.sin b * z.re < 0 ∧
    0 < Real.cos a * z.im - Real.sin a * z.re ∧ ‖z‖ < R}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      ((isOpen_lt (show Continuous (fun z : ℂ ↦ Real.cos b * z.im - Real.sin b * z.re) from by fun_prop) continuous_const).inter
        ((isOpen_lt continuous_const (show Continuous (fun z : ℂ ↦ Real.cos a * z.im - Real.sin a * z.re) from by fun_prop)).inter
          (isOpen_lt continuous_norm continuous_const)))
  have hVK : V ⊆ flatRadialTruncation (flatInteriorAngularWindow a b) R := by
    intro z hz
    refine ⟨⟨?_, hz.2.2.1.le⟩, ?_⟩
    · rw [closedEuclideanSector_eq_halfplanes (ha.trans hab) hbπ]
      exact ⟨hz.1.le, hz.2.1.le⟩
    · simpa only [mem_closedBall, dist_zero_right] using hz.2.2.2.le
  let q := sectorPolar (R / 2) c
  have hqV : q ∈ V := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change 0 < (sectorPolar (R / 2) c).im
      rw [sectorPolar_im]
      exact mul_pos (half_pos hR) (Real.sin_pos_of_pos_of_lt_pi hc hcπ)
    · rw [show q = sectorPolar (R / 2) c from rfl, sectorPolar_support_side,
        show c - b = -(b - c) by ring, Real.sin_neg]
      exact mul_neg_of_pos_of_neg (half_pos hR)
        (neg_neg_of_pos (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hcb) (by linarith)))
    · rw [show q = sectorPolar (R / 2) c from rfl, sectorPolar_support_side]
      exact mul_pos (half_pos hR)
        (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hac) (by linarith))
    · rw [show q = sectorPolar (R / 2) c from rfl, sectorPolar_norm (half_pos hR).le]
      exact half_lt_self hR
  exact ⟨q, interior_mono hVK (by simpa only [hV.interior_eq] using hqV)⟩

/-- Construct the actual initial map for a strict interior angular window by
restriction of the genuine capped retained chart. No map is supplied. -/
theorem PointRetainedConeNeighborhood.exists_interior_window_seed
    {m : ℕ} {weights : Fin m → ℝ} (ha : ∀ j, 0 ≤ weights j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood weights y P p)
    {a b : ℝ} (hbwidth : b ≤ C.flatPhysicalWidth) (hbπ : b ≤ Real.pi) :
    ∃ f : flatRadialTruncation (flatInteriorAngularWindow a b) C.radius → P,
      (∀ x z, (pointSmoothConformalEDist weights y (f x).1 (f z).1).toReal = dist x z) ∧
      ∀ z, (f z).1 = C.flatInverse z.1 := by
  have hsub : flatRadialTruncation (flatInteriorAngularWindow a b) C.radius ⊆
      retainedFlatSectorDisk b C.radius := by
    intro z hz
    exact ⟨hz.1.1, by simpa only [mem_closedBall, dist_zero_right, mem_setOf_eq] using hz.2⟩
  let incl : flatRadialTruncation (flatInteriorAngularWindow a b) C.radius →
      retainedFlatSectorDisk b C.radius := fun z ↦ ⟨z.1, hsub z.2⟩
  let f := C.cappedFlatSectorChart hbwidth ∘ incl
  refine ⟨f, ?_, fun _ ↦ rfl⟩
  intro x z
  exact C.cappedFlatInverse_dist hbπ (hsub x.2) (hsub z.2)

end RepulsiveCoulomb
