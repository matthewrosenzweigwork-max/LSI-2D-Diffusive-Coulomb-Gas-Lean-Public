import LeanResearch.RepulsiveCoulomb.SectorVariation

/-!
RECORDS-ONLY PROPOSED MODULE. This file has not been compiled or staged.
Explicit Euclidean chords in an aperture strictly smaller than pi.
-/
noncomputable section
open Set
open scoped ENNReal NNReal
namespace RepulsiveCoulomb

/-- The usual affine chord, parametrized on `[0,1]`. -/
def euclideanRetainedChord (r s β t : ℝ) : ℂ :=
  (1 - t) • sectorPolar r 0 + t • sectorPolar s β

@[simp] theorem euclideanRetainedChord_zero (r s β : ℝ) :
    euclideanRetainedChord r s β 0 = sectorPolar r 0 := by
  simp [euclideanRetainedChord]

@[simp] theorem euclideanRetainedChord_one (r s β : ℝ) :
    euclideanRetainedChord r s β 1 = sectorPolar s β := by
  simp [euclideanRetainedChord]

theorem continuous_euclideanRetainedChord (r s β : ℝ) :
    Continuous (euclideanRetainedChord r s β) := by
  unfold euclideanRetainedChord
  fun_prop

theorem euclideanRetainedChord_sub (r s β t u : ℝ) :
    euclideanRetainedChord r s β t - euclideanRetainedChord r s β u =
      (t - u) • (sectorPolar s β - sectorPolar r 0) := by
  simp only [euclideanRetainedChord, Complex.real_smul, Complex.ofReal_sub,
    Complex.ofReal_one]
  ring

theorem euclideanRetainedChord_norm_sub (r s β t u : ℝ) :
    ‖euclideanRetainedChord r s β t - euclideanRetainedChord r s β u‖ =
      |t - u| * ‖sectorPolar r 0 - sectorPolar s β‖ := by
  calc
    _ = |t - u| * ‖sectorPolar s β - sectorPolar r 0‖ := by
      rw [euclideanRetainedChord_sub, norm_smul, Real.norm_eq_abs]
    _ = _ := by rw [norm_sub_rev]

theorem euclideanRetainedChord_dist (r s β t u : ℝ) :
    dist (euclideanRetainedChord r s β t) (euclideanRetainedChord r s β u) =
      |t - u| * ‖sectorPolar r 0 - sectorPolar s β‖ := by
  rw [dist_eq_norm, euclideanRetainedChord_norm_sub]

theorem euclideanRetainedChord_lipschitz (r s β : ℝ) :
    LipschitzWith ‖sectorPolar r 0 - sectorPolar s β‖₊
      (euclideanRetainedChord r s β) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  rw [euclideanRetainedChord_dist, Real.dist_eq]
  change |t - u| * ‖sectorPolar r 0 - sectorPolar s β‖ ≤
    ‖sectorPolar r 0 - sectorPolar s β‖ * |t - u|
  exact le_of_eq (mul_comm _ _)

/-- The metric variation of the affine chord is exactly its endpoint distance. -/
theorem euclideanRetainedChord_eVariationOn (r s β : ℝ) :
    eVariationOn (euclideanRetainedChord r s β) (Icc (0 : ℝ) 1) =
      ENNReal.ofReal ‖sectorPolar r 0 - sectorPolar s β‖ := by
  apply le_antisymm
  · have hu := (euclideanRetainedChord_lipschitz r s β).lipschitzOnWith.comp_eVariationOn_le
      (g := id) (s := Icc (0 : ℝ) 1) (mapsTo_univ _ _)
    have hu' : eVariationOn (euclideanRetainedChord r s β) (Icc (0 : ℝ) 1) ≤
        (‖sectorPolar r 0 - sectorPolar s β‖₊ : ℝ≥0∞) := by
      simpa only [Function.comp_id, eVariationOn_id_Icc, sub_zero,
        ENNReal.ofReal_one, mul_one] using hu
    rw [ENNReal.coe_nnreal_eq] at hu'
    exact hu'
  · have hl := eVariationOn.edist_le (euclideanRetainedChord r s β)
      (s := Icc (0 : ℝ) 1) (x := 0) (y := 1)
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
    simpa only [euclideanRetainedChord_zero, euclideanRetainedChord_one,
      edist_dist, dist_eq_norm] using hl

theorem euclideanRetainedChord_re (r s β t : ℝ) :
    (euclideanRetainedChord r s β t).re =
      (1 - t) * r + t * s * Real.cos β := by
  simp [euclideanRetainedChord, Complex.smul_re, smul_eq_mul, sectorPolar_re,
    mul_assoc]

theorem euclideanRetainedChord_im (r s β t : ℝ) :
    (euclideanRetainedChord r s β t).im = t * s * Real.sin β := by
  simp [euclideanRetainedChord, Complex.smul_im, smul_eq_mul, sectorPolar_im,
    mul_assoc]

/-- Two explicit linear inequalities put a point in the positive short sector.
The strictly positive aperture avoids the degenerate half-plane description
of the zero-aperture sector. -/
theorem mem_closedEuclideanSector_of_halfplanes {β : ℝ}
    (hβ0 : 0 < β) (hβπ : β < Real.pi) {z : ℂ}
    (hi : 0 ≤ z.im)
    (hw : Real.cos β * z.im - Real.sin β * z.re ≤ 0) :
    z ∈ closedEuclideanSector β := by
  change 0 ≤ Complex.arg z ∧ Complex.arg z ≤ β
  refine ⟨Complex.arg_nonneg_iff.mpr hi, ?_⟩
  by_cases hz : z = 0
  · simp [hz, hβ0.le]
  · by_contra hle
    have hlt : β < Complex.arg z := lt_of_not_ge hle
    have hsin : 0 < Real.sin (Complex.arg z - β) :=
      Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hlt)
        (by linarith [Complex.arg_le_pi z])
    have hid : ‖z‖ * Real.sin (Complex.arg z - β) =
        Real.cos β * z.im - Real.sin β * z.re := by
      calc
        _ = (‖z‖ * Real.sin (Complex.arg z)) * Real.cos β -
            (‖z‖ * Real.cos (Complex.arg z)) * Real.sin β := by
              rw [Real.sin_sub]
              ring
        _ = _ := by
          rw [Complex.norm_mul_sin_arg, Complex.norm_mul_cos_arg]
          ring
    have hp := mul_pos (norm_pos_iff.mpr hz) hsin
    rw [hid] at hp
    exact (not_lt_of_ge hw) hp

/-- The whole affine chord remains in its closed Euclidean sector, including
the zero-aperture case and zero endpoint radii. -/
theorem euclideanRetainedChord_mem_sector {r s β t : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hβ0 : 0 ≤ β) (hβπ : β < Real.pi)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    euclideanRetainedChord r s β t ∈ closedEuclideanSector β := by
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  rcases eq_or_lt_of_le hβ0 with hβ | hβ
  · have hβ' : β = 0 := hβ.symm
    subst β
    have hreal : euclideanRetainedChord r s 0 t =
        (((1 - t) * r + t * s : ℝ) : ℂ) := by
      apply Complex.ext <;>
        simp [euclideanRetainedChord_re, euclideanRetainedChord_im]
    have hnonneg : 0 ≤ (1 - t) * r + t * s :=
      add_nonneg (mul_nonneg ht' hr) (mul_nonneg ht.1 hs)
    change 0 ≤ Complex.arg (euclideanRetainedChord r s 0 t) ∧
      Complex.arg (euclideanRetainedChord r s 0 t) ≤ 0
    rw [hreal, Complex.arg_ofReal_of_nonneg hnonneg]
    exact ⟨le_rfl, le_rfl⟩
  · have hsin : 0 ≤ Real.sin β := Real.sin_nonneg_of_mem_Icc ⟨hβ0, hβπ.le⟩
    apply mem_closedEuclideanSector_of_halfplanes hβ hβπ
    · rw [euclideanRetainedChord_im]
      exact mul_nonneg (mul_nonneg ht.1 hs) hsin
    · rw [euclideanRetainedChord_re, euclideanRetainedChord_im]
      have hp : 0 ≤ (1 - t) * r * Real.sin β :=
        mul_nonneg (mul_nonneg ht' hr) hsin
      nlinarith

theorem euclideanRetainedChord_mapsTo_sector {r s β : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hβ0 : 0 ≤ β) (hβπ : β < Real.pi) :
    MapsTo (euclideanRetainedChord r s β) (Icc (0 : ℝ) 1)
      (closedEuclideanSector β) :=
  fun _ ht => euclideanRetainedChord_mem_sector hr hs hβ0 hβπ ht

/-- Convexity of the norm gives the sharper affine radial bound. -/
theorem euclideanRetainedChord_norm_le_affine {r s β t : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖euclideanRetainedChord r s β t‖ ≤ (1 - t) * r + t * s := by
  calc
    _ ≤ ‖(1 - t) • sectorPolar r 0‖ + ‖t • sectorPolar s β‖ := norm_add_le _ _
    _ = _ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1,
        abs_of_nonneg (sub_nonneg.mpr ht.2), sectorPolar_norm hr, sectorPolar_norm hs]

theorem euclideanRetainedChord_norm_le_max {r s β t : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖euclideanRetainedChord r s β t‖ ≤ max r s := by
  apply (euclideanRetainedChord_norm_le_affine hr hs ht).trans
  calc
    (1 - t) * r + t * s ≤ (1 - t) * max r s + t * max r s :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left r s) (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left (le_max_right r s) ht.1)
    _ = max r s := by ring

/-- For two positive radii and an aperture below pi, the straight chord is
strictly shorter than travelling through the vertex. -/
theorem sectorPolar_short_chord_lt_sum {r s β : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hβ0 : 0 ≤ β) (hβπ : β < Real.pi) :
    ‖sectorPolar r 0 - sectorPolar s β‖ < r + s := by
  have hc : -1 < Real.cos β := by
    simpa only [Real.cos_pi] using
      Real.cos_lt_cos_of_nonneg_of_le_pi hβ0 le_rfl hβπ
  have hgap : 0 < 2 * r * s * (Real.cos β + 1) := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) hr) hs) (by linarith)
  have hd := sectorPolar_distance_sq r s 0 β
  simp only [zero_sub, Real.cos_neg] at hd
  have hn := norm_nonneg (sectorPolar r 0 - sectorPolar s β)
  nlinarith

end RepulsiveCoulomb
