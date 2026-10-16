module

public import LeanResearch.RepulsiveCoulomb.PointRetainedConeNeighborhood
public import LeanResearch.RepulsiveCoulomb.PointMetricLineNormalizedChart

@[expose] public section

/-! Isolated, uncompiled geometric normalization. A unit rotation translates
both endpoints of a genuine full retained interval by the SAME real amount.
It does not replace either interval by a principal angle or select a cap side. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

 theorem sectorReturn_rotate_radial_point (r θ φ : ℝ) :
    conePhase (-φ) * pointRadialSectorPoint r θ = pointRadialSectorPoint r (θ - φ) := by
  have he : (((θ - φ : ℝ) : ℂ) * Complex.I) =
      (((-φ : ℝ) : ℂ) * Complex.I) + ((θ : ℂ) * Complex.I) := by
    push_cast
    ring
  simp only [pointRadialSectorPoint, Circle.coe_exp, conePhase]
  rw [he, Complex.exp_add]
  ring

/-- Translate literal full angular intervals under an actual unit rotation.
There is no restriction on the real endpoints and no angular wrapping. -/
theorem sectorReturn_rotate_closed_interval_iff
    (R lo hi φ : ℝ) (w : ℂ) :
    conePhase (-φ) * w ∈ pointClosedRadialInterval R (lo - φ) (hi - φ) ↔
      w ∈ pointClosedRadialInterval R lo hi := by
  have hc : conePhase (-φ) ≠ 0 := Complex.exp_ne_zero _
  constructor
  · rintro ⟨r, hr, θ, hθ, he⟩
    refine ⟨r, hr, θ + φ, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, ?_⟩
    apply mul_left_cancel₀ hc
    rw [sectorReturn_rotate_radial_point]
    simpa only [add_sub_cancel_right] using he
  · rintro ⟨r, hr, θ, hθ, rfl⟩
    exact ⟨r, hr, θ - φ, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩,
      sectorReturn_rotate_radial_point r θ φ⟩

/-- Rotate an existing genuine retained cone neighborhood. All metric,
whole-disk, onto, and exact local-region fields are constructed. The full
real interval becomes [lo−φ,hi−φ], preserving its ordered width. -/
theorem PointRetainedConeNeighborhood.exists_rotate
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (φ : ℝ) :
    ∃ D : PointRetainedConeNeighborhood a y P p,
      D.radius = C.radius ∧ D.chart.source = C.chart.source ∧
      (∀ z, D.chart z = conePhase (-φ) * C.chart z) ∧
      D.lo = C.lo - φ ∧ D.hi = C.hi - φ := by
  let c := conePhase (-φ)
  have hc : ‖c‖ = 1 := conePhase_norm _
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  let F := C.chart.trans (Homeomorph.mulLeft₀ c hc0).toOpenPartialHomeomorph
  have hF (z : ℂ) : F z = c * C.chart z := rfl
  have hsrc : F.source = C.chart.source := by simp [F]
  have hrot : BijOn (fun z : ℂ => c * z)
      {z : ℂ | ‖z‖ ≤ C.radius} {z : ℂ | ‖z‖ ≤ C.radius} := by
    refine ⟨?_, fun _ _ _ _ he => mul_left_cancel₀ hc0 he, ?_⟩
    · intro z hz
      change ‖c * z‖ ≤ C.radius
      rwa [norm_mul, hc, one_mul]
    · intro z hz
      refine ⟨c⁻¹ * z, ?_, ?_⟩
      · change ‖c⁻¹ * z‖ ≤ C.radius
        rwa [norm_mul, norm_inv, hc, inv_one, one_mul]
      · exact mul_inv_cancel_left₀ hc0 z
  let D : PointRetainedConeNeighborhood a y P p :=
    { chart := F
      radius := C.radius
      radius_pos := C.radius_pos
      center := by rw [hF, C.center, mul_zero]
      source := by rw [hsrc]; exact C.source
      onto := hrot.comp C.onto
      metric := by
        intro z hz w hw
        rw [hF, hF, pointClassicalConeDist_rotation a y p hc]
        exact C.metric z hz w hw
      lo := C.lo - φ
      hi := C.hi - φ
      width_pos := by linarith [C.width_pos]
      width_le_full := by linarith [C.width_le_full]
      retained := by
        intro z hz
        rw [hF]
        exact (C.retained z hz).trans
          (sectorReturn_rotate_closed_interval_iff C.radius C.lo C.hi φ (C.chart z)).symm }
  exact ⟨D, rfl, hsrc, hF, rfl, rfl⟩

/-- The removed-side admissibility inequality forces a proper old interval.
It does not bound its full physical retained angle by pi. -/
theorem PointRetainedConeNeighborhood.sectorReturn_width_lt_full_of_admissible
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hC : C.Admissible) :
    C.hi - C.lo < 2 * Real.pi := by
  change Real.pi ≤ (coalescedPointExponent a y p / 2 + 1) *
    (2 * Real.pi - (C.hi - C.lo)) at hC
  by_contra hn
  have he : C.hi - C.lo = 2 * Real.pi := le_antisymm C.width_le_full (le_of_not_gt hn)
  rw [he, sub_self, mul_zero] at hC
  exact Real.pi_pos.not_ge hC

end RepulsiveCoulomb
