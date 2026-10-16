import LeanResearch.RepulsiveCoulomb.ClassicalConeSectorIsometry
import LeanResearch.RepulsiveCoulomb.EuclideanRetainedChord
import LeanResearch.RepulsiveCoulomb.PointRetainedConeNeighborhood

/-! RECORDS-ONLY, UNCOMPILED DRAFT.

An explicit short chord in a literal retained angular interval. The curve is
the ordinary Euclidean chord in developed angle, contracted angularly and
rotated to the prescribed base ray. Its length is the genuine partition
variation in `classicalConeMetricSpace`. -/
noncomputable section
open Set
open scoped ENNReal NNReal
namespace RepulsiveCoulomb

def classicalConeCurveLength (α : ℝ) (hα : 0 ≤ α) (γ : ℝ → ℂ) : ℝ≥0∞ :=
  @eVariationOn ℝ _ ℂ (classicalConeMetricSpace α hα).toUniformSpace.toTopologicalSpace
    (@PseudoEMetricSpace.toWeakPseudoEMetricSpace ℂ
      (classicalConeMetricSpace α hα).toPseudoEMetricSpace) γ (Icc (0 : ℝ) 1)

def classicalConeRetainedChord (α r s θ φ t : ℝ) : ℂ :=
  conePhase θ * sectorAngularMap (α + 1)⁻¹
    (euclideanRetainedChord r s ((α + 1) * (φ - θ)) t)

theorem classicalConeRetainedChord_norm_le_max {α r s θ φ t : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖classicalConeRetainedChord α r s θ φ t‖ ≤ max r s := by
  rw [classicalConeRetainedChord, norm_mul, conePhase_norm, one_mul,
    sectorAngularMap_norm]
  exact euclideanRetainedChord_norm_le_max hr hs ht

theorem classicalConeRetainedChord_endpoints {α r s θ φ : ℝ}
    (hα : 0 ≤ α) (hr : 0 ≤ r) (hs : 0 ≤ s) (hθφ : θ ≤ φ)
    (hshort : (α + 1) * (φ - θ) < Real.pi) :
    classicalConeRetainedChord α r s θ φ 0 = pointRadialSectorPoint r θ ∧
      classicalConeRetainedChord α r s θ φ 1 = pointRadialSectorPoint s φ := by
  have ha1 : 0 < α + 1 := by linarith
  have hβ : (α + 1) * (φ - θ) ∈ Ioc (-Real.pi) Real.pi :=
    ⟨(neg_neg_of_pos Real.pi_pos).trans_le (mul_nonneg ha1.le (sub_nonneg.mpr hθφ)),
      hshort.le⟩
  have hcancel : θ + (α + 1)⁻¹ * ((α + 1) * (φ - θ)) = φ := by
    rw [← mul_assoc, inv_mul_cancel₀ ha1.ne', one_mul]
    ring
  constructor
  · rw [classicalConeRetainedChord, euclideanRetainedChord_zero,
      sectorAngularMap_polar hr ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩,
      mul_zero, conePhase_mul_sectorPolar, add_zero, sectorPolar_eq_pointRadialSectorPoint]
  · rw [classicalConeRetainedChord, euclideanRetainedChord_one,
      sectorAngularMap_polar hs hβ, conePhase_mul_sectorPolar, hcancel,
      sectorPolar_eq_pointRadialSectorPoint]

theorem classicalConeRetainedChord_continuousOn {α r s θ φ : ℝ}
    (hα : 0 ≤ α) (hr : 0 ≤ r) (hs : 0 ≤ s) (hθφ : θ ≤ φ)
    (hshort : (α + 1) * (φ - θ) < Real.pi) :
    ContinuousOn (classicalConeRetainedChord α r s θ φ) (Icc (0 : ℝ) 1) := by
  have ha1 : 0 < α + 1 := by linarith
  have hL0 : 0 ≤ (α + 1)⁻¹ := (inv_pos.mpr ha1).le
  have hL1 : (α + 1)⁻¹ ≤ 1 := (inv_le_one₀ ha1).mpr (by linarith)
  have hc := (sectorAngularMap_lipschitzOn hL0 hL1 hshort.le).continuousOn.comp
    (continuous_euclideanRetainedChord r s ((α + 1) * (φ - θ))).continuousOn
    (euclideanRetainedChord_mapsTo_sector hr hs
      (mul_nonneg ha1.le (sub_nonneg.mpr hθφ)) hshort)
  exact continuous_const.continuousOn.mul hc

theorem classicalConeRetainedChord_mapsTo {α R lo hi r s θ φ : ℝ}
    (hα : 0 ≤ α) (hr : r ∈ Icc (0 : ℝ) R) (hs : s ∈ Icc (0 : ℝ) R)
    (hθ : θ ∈ Icc lo hi) (hφ : φ ∈ Icc lo hi) (hθφ : θ ≤ φ)
    (hshort : (α + 1) * (φ - θ) < Real.pi) :
    MapsTo (classicalConeRetainedChord α r s θ φ) (Icc (0 : ℝ) 1)
      (pointClosedRadialInterval R lo hi) := by
  have ha1 : 0 < α + 1 := by linarith
  have hcancel : θ + (α + 1)⁻¹ * ((α + 1) * (φ - θ)) = φ := by
    rw [← mul_assoc, inv_mul_cancel₀ ha1.ne', one_mul]
    ring
  intro t ht
  have hw := euclideanRetainedChord_mem_sector hr.1 hs.1
    (mul_nonneg ha1.le (sub_nonneg.mpr hθφ)) hshort ht
  have hn := (euclideanRetainedChord_norm_le_max
    (β := (α + 1) * (φ - θ)) hr.1 hs.1 ht).trans
    (max_le hr.2 hs.2)
  obtain ⟨ρ, hρ, ψ, hψ, he⟩ :=
    rotated_sectorAngularMap_radial_representative hα hshort θ hw hn
  rw [hcancel] at hψ
  exact ⟨ρ, hρ, ψ, ⟨hθ.1.trans hψ.1, hψ.2.trans hφ.2⟩, he⟩

/-- Actual cone variation equals the ordinary Euclidean developed chord
variation, since every partition edge is exactly preserved. -/
theorem classicalConeRetainedChord_variation_eq {α r s θ φ : ℝ}
    (hα : 0 ≤ α) (hr : 0 ≤ r) (hs : 0 ≤ s) (hθφ : θ ≤ φ)
    (hshort : (α + 1) * (φ - θ) < Real.pi) :
    classicalConeCurveLength α hα (classicalConeRetainedChord α r s θ φ) =
      eVariationOn (euclideanRetainedChord r s ((α + 1) * (φ - θ))) (Icc (0 : ℝ) 1) := by
  have hm := euclideanRetainedChord_mapsTo_sector hr hs
    (mul_nonneg (by linarith : 0 ≤ α + 1) (sub_nonneg.mpr hθφ)) hshort
  unfold classicalConeCurveLength eVariationOn
  apply iSup_congr
  rintro ⟨n, u, hu, huI⟩
  apply Finset.sum_congr rfl
  intro i hi
  rw [@edist_dist ℂ (classicalConeMetricSpace α hα).toPseudoMetricSpace,
    edist_dist, dist_eq_norm]
  apply congrArg ENNReal.ofReal
  exact rotated_sectorAngularMap_classicalCone_dist hα hshort θ
    (hm (huI (i + 1))) (hm (huI i))

theorem classicalConeRetainedChord_length {α r s θ φ : ℝ}
    (hα : 0 ≤ α) (hr : 0 ≤ r) (hs : 0 ≤ s) (hθφ : θ ≤ φ)
    (hshort : (α + 1) * (φ - θ) < Real.pi) :
    classicalConeCurveLength α hα (classicalConeRetainedChord α r s θ φ) =
      ENNReal.ofReal ‖sectorPolar r 0 - sectorPolar s ((α + 1) * (φ - θ))‖ := by
  rw [classicalConeRetainedChord_variation_eq hα hr hs hθφ hshort,
    euclideanRetainedChord_eVariationOn]

/-- A genuine, explicitly constructed competitor in the retained interval.
Positive endpoint radii are necessary for strict shortening. The theorem
includes exponent zero and equal-angle rays. -/
theorem exists_classicalCone_retained_short_chord {α R lo hi r s θ φ : ℝ}
    (hα : 0 ≤ α) (hr : 0 < r) (hs : 0 < s) (hrR : r ≤ R) (hsR : s ≤ R)
    (hθ : θ ∈ Icc lo hi) (hφ : φ ∈ Icc lo hi) (hθφ : θ ≤ φ)
    (hshort : (α + 1) * (φ - θ) < Real.pi) :
    ∃ γ : ℝ → ℂ, γ 0 = pointRadialSectorPoint r θ ∧
      γ 1 = pointRadialSectorPoint s φ ∧ ContinuousOn γ (Icc (0 : ℝ) 1) ∧
      MapsTo γ (Icc (0 : ℝ) 1) (pointClosedRadialInterval R lo hi) ∧
      classicalConeCurveLength α hα γ < ENNReal.ofReal (r + s) := by
  have he := classicalConeRetainedChord_endpoints hα hr.le hs.le hθφ hshort
  refine ⟨classicalConeRetainedChord α r s θ φ, he.1, he.2,
    classicalConeRetainedChord_continuousOn hα hr.le hs.le hθφ hshort,
    classicalConeRetainedChord_mapsTo hα ⟨hr.le, hrR⟩ ⟨hs.le, hsR⟩ hθ hφ hθφ hshort, ?_⟩
  rw [classicalConeRetainedChord_length hα hr.le hs.le hθφ hshort]
  exact (ENNReal.ofReal_lt_ofReal_iff (add_pos hr hs)).mpr
    (sectorPolar_short_chord_lt_sum hr hs
      (mul_nonneg (by linarith : 0 ≤ α + 1) (sub_nonneg.mpr hθφ)) hshort)

/-- With an endpoint at the apex there is no strict shortcut: the same
constructed curve has exactly the sum of the two radii as its length. -/
theorem classicalConeRetainedChord_length_apex {α r s θ φ : ℝ}
    (hα : 0 ≤ α) (hr : 0 ≤ r) (hs : 0 ≤ s) (hθφ : θ ≤ φ)
    (hshort : (α + 1) * (φ - θ) < Real.pi) (hapex : r = 0 ∨ s = 0) :
    classicalConeCurveLength α hα (classicalConeRetainedChord α r s θ φ) =
      ENNReal.ofReal (r + s) := by
  rw [classicalConeRetainedChord_length hα hr hs hθφ hshort]
  rcases hapex with rfl | rfl
  · rw [sectorPolar_zero, zero_sub, norm_neg, sectorPolar_norm hs, zero_add]
  · rw [sectorPolar_zero, sub_zero, sectorPolar_norm hr, add_zero]

end RepulsiveCoulomb
