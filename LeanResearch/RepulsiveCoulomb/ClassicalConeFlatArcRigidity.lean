module

public import LeanResearch.RepulsiveCoulomb.ClassicalConeSectorIsometry
public import LeanResearch.RepulsiveCoulomb.JordanTurnAngleLift
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

/-! Isolated, uncompiled author draft. A continuous, genuinely isometric
positive-radius source arc determines its entire directed cone-angle lift.
No occupied-angle, monotonicity, orientation, or local-increment certificate
is an input. Principal arguments are used only in a proved small window. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- Coordinate and physical widths remain distinct, including at alpha = 0. -/
theorem flatLink_coordinate_width {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (hβπ : β ≤ Real.pi) :
    0 < β / (α + 1) ∧ β / (α + 1) ≤ Real.pi ∧
      (α + 1) * (β / (α + 1)) = β := by
  have hk : 0 < α + 1 := by linarith
  refine ⟨div_pos hβ hk, (div_le_iff₀ hk).mpr ?_, mul_div_cancel₀ _ hk.ne'⟩
  nlinarith [mul_nonneg Real.pi_pos.le hα]

/-- A source interval of width at most pi has no repeated positive-radius
polar points, including both endpoints at width pi. -/
theorem flatLink_source_arc_injective {r β : ℝ} (hr : 0 < r)
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) :
    Function.Injective (fun t : unitInterval ↦ sectorPolar r (β * t.1)) := by
  intro s t hst
  have hwindow (u : unitInterval) : β * u.1 ∈ Ioc (-Real.pi) Real.pi :=
    ⟨(neg_neg_of_pos Real.pi_pos).trans_le (mul_nonneg hβ.le u.2.1),
      (mul_le_of_le_one_right hβ.le u.2.2).trans hβπ⟩
  have h := congrArg Complex.arg hst
  rw [sectorPolar_arg hr (hwindow s), sectorPolar_arg hr (hwindow t)] at h
  exact Subtype.ext (mul_left_cancel₀ hβ.ne' h)

/-- Small-window cosine law, also at the regular exponent zero. Neither a
circular principal representative nor a clipped angle is silently enlarged. -/
theorem classicalCone_polar_small_distance_sq {α r φ ψ : ℝ}
    (hα : 0 ≤ α) (hr : 0 < r) (hsmall : |φ - ψ| < Real.pi)
    (hphysical : (α + 1) * |φ - ψ| ≤ Real.pi) :
    (@dist ℂ (classicalConeMetricSpace α hα).toDist
      (sectorPolar r φ) (sectorPolar r ψ)) ^ 2 =
      r ^ 2 + r ^ 2 - 2 * r * r * Real.cos ((α + 1) * |φ - ψ|) := by
  rcases hα.eq_or_lt with he | hp
  · subst α
    rw [classicalCone_zero_dist, norm_sub_rev, sectorPolar_distance_sq]
    simp only [zero_add, one_mul, Real.cos_abs]
  · have harg : Complex.arg (sectorPolar r ψ / sectorPolar r φ) = ψ - φ := by
      rw [sectorPolar_eq_pointRadialSectorPoint, sectorPolar_eq_pointRadialSectorPoint,
        pointRadialSectorPoint_div, div_self hr.ne', Complex.ofReal_one, one_mul]
      apply Circle.arg_exp
      · have := (abs_lt.mp hsmall).2
        linarith
      · have := (abs_lt.mp hsmall).1
        linarith
    rw [classicalCone_distance_sq hp, sectorPolar_norm hr.le,
      sectorPolar_norm hr.le, harg, abs_sub_comm, min_eq_right hphysical]

/-- The real local-isometry rigidity step. Continuity and injectivity choose
a single orientation, and local increments are globalized by connectedness. -/
theorem flatLink_real_lift_rigidity {f : unitInterval → ℝ} {L : ℝ}
    (hc : Continuous f) (hi : Function.Injective f)
    (hlocal : ∀ t, ∀ᶠ u in 𝓝 t, |f u - f t| = L * |u.1 - t.1|) :
    (∀ t, f t = f 0 + L * t.1) ∨ (∀ t, f t = f 0 - L * t.1) := by
  rcases hc.strictMono_of_inj_boundedOrder' hi with hm | hm
  · left
    have hconst : IsLocallyConstant (fun t : unitInterval ↦ f t - L * t.1) := by
      apply (IsLocallyConstant.iff_eventually_eq _).mpr
      intro t
      filter_upwards [hlocal t] with u hu
      rcases le_total t u with htu | hut
      · rw [abs_of_nonneg (sub_nonneg.mpr (hm.monotone htu)),
          abs_of_nonneg (sub_nonneg.mpr (show t.1 ≤ u.1 from htu))] at hu
        linarith
      · rw [abs_of_nonpos (sub_nonpos.mpr (hm.monotone hut)),
          abs_of_nonpos (sub_nonpos.mpr (show u.1 ≤ t.1 from hut))] at hu
        linarith
    intro t
    have h := hconst.apply_eq_of_preconnectedSpace t 0
    change f t - L * t.1 = f 0 - L * 0 at h
    linarith
  · right
    have hconst : IsLocallyConstant (fun t : unitInterval ↦ f t + L * t.1) := by
      apply (IsLocallyConstant.iff_eventually_eq _).mpr
      intro t
      filter_upwards [hlocal t] with u hu
      rcases le_total t u with htu | hut
      · rw [abs_of_nonpos (sub_nonpos.mpr (hm.antitone htu)),
          abs_of_nonneg (sub_nonneg.mpr (show t.1 ≤ u.1 from htu))] at hu
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr (hm.antitone hut)),
          abs_of_nonpos (sub_nonpos.mpr (show u.1 ≤ t.1 from hut))] at hu
        linarith
    intro t
    have h := hconst.apply_eq_of_preconnectedSpace t 0
    change f t + L * t.1 = f 0 + L * 0 at h
    linarith

/-- An actual equal-radius isometric arc in the full cone has a constructed
continuous injective lift and exactly one of the two source orientations.
The physical angular speed is beta, for every alpha >= 0. -/
theorem classicalCone_flat_arc_directed_lift {α r β : ℝ}
    (hα : 0 ≤ α) (hr : 0 < r) (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    {v : unitInterval → ℂ} (hc : Continuous v) (hnorm : ∀ t, ‖v t‖ = r)
    (hd : ∀ s t, @dist ℂ (classicalConeMetricSpace α hα).toDist (v s) (v t) =
      ‖sectorPolar r (β * s.1) - sectorPolar r (β * t.1)‖) :
    ∃ φ : unitInterval → ℝ, Continuous φ ∧ Function.Injective φ ∧
      (∀ t, v t = sectorPolar r (φ t)) ∧
      ((∀ t, φ t = φ 0 + (β / (α + 1)) * t.1) ∨
       (∀ t, φ t = φ 0 - (β / (α + 1)) * t.1)) := by
  have hk : 0 < α + 1 := by linarith
  have hv0 (t : unitInterval) : v t ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; exact hr.ne')
  obtain ⟨φ, hφ, hlift⟩ := exists_interval_euclidean_angle_lift hc hv0
  have hpolar (t : unitInterval) : v t = sectorPolar r (φ t) := by
    have h := hlift t
    rw [hnorm] at h
    change v t = (r : ℂ) * Complex.exp ((φ t : ℂ) * Complex.I)
    rw [h, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')]
  have hvi : Function.Injective v := by
    intro s t hst
    have h := hd s t
    rw [hst, @dist_self ℂ (classicalConeMetricSpace α hα).toPseudoMetricSpace] at h
    exact flatLink_source_arc_injective hr hβ hβπ
      (sub_eq_zero.mp (norm_eq_zero.mp h.symm))
  have hφi : Function.Injective φ := by
    intro s t hst
    apply hvi
    rw [hpolar s, hpolar t, hst]
  have hlocal : ∀ t, ∀ᶠ u in 𝓝 t,
      |φ u - φ t| = (β / (α + 1)) * |u.1 - t.1| := by
    intro t
    have hsmall : ∀ᶠ u in 𝓝 t, |φ u - φ t| < Real.pi / (α + 1) := by
      have hcont : ContinuousAt (fun u : unitInterval ↦ |φ u - φ t|) t :=
        (hφ.continuousAt.sub
          (continuousAt_const : ContinuousAt (fun _ : unitInterval ↦ φ t) t)).abs
      exact hcont.eventually_lt
        (continuousAt_const : ContinuousAt (fun _ : unitInterval ↦ Real.pi / (α + 1)) t)
        (by simpa only [sub_self, abs_zero] using div_pos Real.pi_pos hk)
    filter_upwards [hsmall] with u hu
    have hphysical : (α + 1) * |φ u - φ t| < Real.pi := by
      have := (lt_div_iff₀ hk).mp hu
      nlinarith
    have hprincipal : |φ u - φ t| < Real.pi := by
      have hle : |φ u - φ t| ≤ (α + 1) * |φ u - φ t| := by
        nlinarith [mul_nonneg hα (abs_nonneg (φ u - φ t))]
      exact hle.trans_lt hphysical
    have hsource : β * |u.1 - t.1| ≤ Real.pi := by
      have hdiff : |u.1 - t.1| ≤ 1 := abs_le.mpr ⟨by linarith [u.2.1, t.2.2],
        by linarith [u.2.2, t.2.1]⟩
      exact (mul_le_of_le_one_right hβ.le hdiff).trans hβπ
    have hsquare := congrArg (fun x : ℝ ↦ x ^ 2) (hd u t)
    rw [hpolar u, hpolar t,
      classicalCone_polar_small_distance_sq hα hr hprincipal hphysical.le,
      sectorPolar_distance_sq] at hsquare
    have hcosSource : Real.cos (β * u.1 - β * t.1) = Real.cos (β * |u.1 - t.1|) := by
      rw [← mul_sub, ← Real.cos_abs, abs_mul, abs_of_pos hβ]
    rw [hcosSource] at hsquare
    have hcos : Real.cos ((α + 1) * |φ u - φ t|) =
        Real.cos (β * |u.1 - t.1|) := by
      have hz : (2 * r * r) * (Real.cos ((α + 1) * |φ u - φ t|) -
          Real.cos (β * |u.1 - t.1|)) = 0 := by nlinarith [hsquare]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (by positivity))
    have he := Real.strictAntiOn_cos.injOn
      (show (α + 1) * |φ u - φ t| ∈ Icc 0 Real.pi from
        ⟨mul_nonneg hk.le (abs_nonneg _), hphysical.le⟩)
      (show β * |u.1 - t.1| ∈ Icc 0 Real.pi from
        ⟨mul_nonneg hβ.le (abs_nonneg _), hsource⟩) hcos
    have hdiv : |φ u - φ t| = (β * |u.1 - t.1|) / (α + 1) :=
      (eq_div_iff hk.ne').mpr (by nlinarith [he])
    calc
      _ = (β * |u.1 - t.1|) / (α + 1) := hdiv
      _ = (β / (α + 1)) * |u.1 - t.1| := by ring
  exact ⟨φ, hφ, hφi, hpolar, flatLink_real_lift_rigidity hφ hφi hlocal⟩

end RepulsiveCoulomb
