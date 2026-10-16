module

public import LeanResearch.RepulsiveCoulomb.PointRadialSectorTopology
public import LeanResearch.RepulsiveCoulomb.PointGeodesicStrictSectors

@[expose] public section

/-! Normalize an actual pair of distinct equal-radius rays by a unit rotation.
The two directed polar sector widths are identified with the previously proved
short/long cone angles, without a principal-argument branch assumption. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

@[simp] theorem pointRadialSectorPoint_angle_zero (r : ℝ) :
    pointRadialSectorPoint r 0 = (r : ℂ) := by
  simp [pointRadialSectorPoint]

/-- Both directions fit the same normalized [0,2*pi) polar chart, with the
second angle strictly interior because the rays are distinct. -/
theorem exists_pointRadialSector_normalization {u v : ℂ}
    (hnorm : ‖u‖ = ‖v‖) (hne : u ≠ v) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧
      c * u = pointRadialSectorPoint ‖u‖ 0 ∧
      c * v = pointRadialSectorPoint ‖u‖ θ ∧
      v / u = (Circle.exp θ : ℂ) := by
  have hu : u ≠ 0 := by
    intro hu
    have hv : v = 0 := norm_eq_zero.mp (by rw [← hnorm, hu, norm_zero])
    exact hne (hu.trans hv.symm)
  have hv : v ≠ 0 := by
    intro hv
    have hu0 : u = 0 := norm_eq_zero.mp (by rw [hnorm, hv, norm_zero])
    exact hu hu0
  let c := conePhase (-Complex.arg u)
  have hcnorm : ‖c‖ = 1 := conePhase_norm _
  have hc : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hcnorm]; norm_num)
  have hcu : c * u = (‖u‖ : ℂ) := conePhase_neg_arg_mul u
  obtain ⟨θ, hθ, hpolar⟩ := exists_pointRadialSectorPoint_angle (c * v) (mul_ne_zero hc hv)
  have hncv : ‖c * v‖ = ‖u‖ := by rw [norm_mul, hcnorm, one_mul, ← hnorm]
  rw [hncv] at hpolar
  have hθne : θ ≠ 0 := by
    intro he
    rw [he, pointRadialSectorPoint_angle_zero] at hpolar
    exact hne (mul_left_cancel₀ hc (hcu.trans hpolar))
  have hratio : v / u = (Circle.exp θ : ℂ) := by
    calc
      v / u = (c * v) / (c * u) := (mul_div_mul_left v u hc).symm
      _ = pointRadialSectorPoint ‖u‖ θ / (‖u‖ : ℂ) := by rw [← hpolar, hcu]
      _ = (Circle.exp θ : ℂ) := by
        unfold pointRadialSectorPoint
        rw [mul_comm, mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu))]
  exact ⟨c, hcnorm, θ, lt_of_le_of_ne hθ.1 (Ne.symm hθne), hθ.2,
    by simpa only [pointRadialSectorPoint_angle_zero] using hcu, hpolar.symm, hratio⟩

/-- The absolute principal angle records the smaller of the two directed
sector widths, including angles strictly larger than pi. -/
theorem pointRadialSector_principal_abs {θ : ℝ}
    (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi) :
    |Complex.arg (Circle.exp θ : ℂ)| = min θ (2 * Real.pi - θ) := by
  by_cases hθπ : θ ≤ Real.pi
  · rw [Circle.arg_exp (by linarith [Real.pi_pos]) hθπ, abs_of_pos hθ0,
      min_eq_left (by linarith)]
  · have harg : Complex.arg (Circle.exp θ : ℂ) = θ - 2 * Real.pi := by
      have h := Circle.arg_exp (x := θ - 2 * Real.pi) (by linarith) (by linarith [Real.pi_pos])
      rw [Circle.exp_sub_two_pi] at h
      exact h
    rw [harg, abs_of_neg (by linarith), min_eq_right (by linarith)]
    ring

/-- Each normalized directed sector angle is exactly one of the two actual
cone-sector angles used in the strict endpoint bounds. -/
theorem cone_directed_sector_angles_eq_short_long {α θ : ℝ} {u v : ℂ}
    (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (hratio : v / u = (Circle.exp θ : ℂ)) :
    ((α + 1) * θ = coneShortSectorAngle α u v ∧
      (α + 1) * (2 * Real.pi - θ) = coneLongSectorAngle α u v) ∨
    ((α + 1) * θ = coneLongSectorAngle α u v ∧
      (α + 1) * (2 * Real.pi - θ) = coneShortSectorAngle α u v) := by
  have hs : coneShortSectorAngle α u v = (α + 1) * min θ (2 * Real.pi - θ) := by
    rw [coneShortSectorAngle, hratio, pointRadialSector_principal_abs hθ0 hθ2]
  by_cases hθπ : θ ≤ Real.pi
  · rw [min_eq_left (by linarith)] at hs
    refine Or.inl ⟨hs.symm, ?_⟩
    rw [coneLongSectorAngle, hs]
    ring
  · rw [min_eq_right (by linarith)] at hs
    refine Or.inr ⟨?_, hs.symm⟩
    rw [coneLongSectorAngle, hs]
    ring

end RepulsiveCoulomb
