import LeanResearch.RepulsiveCoulomb.ClassicalConeFlatArcRigidity

/-! Isolated, uncompiled author draft. Full directed widths are recovered from
actual equal-radius cone distances, using only LOCAL cosine injectivity. A
midpoint-centered branch is constructed on a proper closed target interval;
it works for reflex intervals and does not replace them by principal angles. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- The midpoint of a proper interval places its entire closed interval
strictly inside the principal-argument window. -/
theorem retainedWidth_midpoint_window {lo hi θ : ℝ}
    (hproper : hi - lo < 2 * Real.pi) (hθ : θ ∈ Icc lo hi) :
    θ - (lo + hi) / 2 ∈ Ioo (-Real.pi) Real.pi := by
  constructor <;> linarith [hθ.1, hθ.2]

/-- A positive-radius proper closed polar arc is injective, even when its
width is greater than pi. -/
theorem retainedWidth_polar_arc_injective {r A L : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hproper : L < 2 * Real.pi) :
    Function.Injective (fun t : unitInterval => sectorPolar r (A + L * t.1)) := by
  intro s t hst
  have hphase : Circle.exp (A + L * s.1) = Circle.exp (A + L * t.1) := by
    apply Subtype.ext
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')
    simpa only [sectorPolar_eq_pointRadialSectorPoint, pointRadialSectorPoint] using hst
  have hwin (u : unitInterval) : A + L * u.1 ∈ Ico A (A + 2 * Real.pi) := by
    constructor
    · linarith [mul_nonneg hL.le u.2.1]
    · have := mul_le_of_le_one_right hL.le u.2.2
      linarith
  have he := (Circle.exp_injOn_Ico (a := A) (b := A + 2 * Real.pi) (by linarith))
    (hwin s) (hwin t) hphase
  apply Subtype.ext
  exact mul_left_cancel₀ hL.ne' (add_left_cancel he)

/-- The actual target-side angle lift, with its full interval range proved
from literal polar membership. No lift or orientation is supplied as input. -/
theorem retainedWidth_exists_target_lift {r lo hi : ℝ}
    (hr : 0 < r) (hproper : hi - lo < 2 * Real.pi)
    {v : unitInterval → ℂ} (hc : Continuous v)
    (hmem : ∀ t, ∃ θ ∈ Icc lo hi, v t = sectorPolar r θ) :
    ∃ φ : unitInterval → ℝ, Continuous φ ∧
      (∀ t, φ t ∈ Icc lo hi) ∧ (∀ t, v t = sectorPolar r (φ t)) := by
  let M := (lo + hi) / 2
  let w : unitInterval → ℂ := fun t => conePhase (-M) * v t
  let φ : unitInterval → ℝ := fun t => M + Complex.arg (w t)
  have hbranch (t : unitInterval) {θ : ℝ} (hθ : θ ∈ Icc lo hi)
      (he : v t = sectorPolar r θ) : Complex.arg (w t) = θ - M := by
    have hwindow := retainedWidth_midpoint_window hproper hθ
    have hw : w t = sectorPolar r (θ - M) := by
      dsimp [w]
      rw [he, conePhase_mul_sectorPolar]
      congr 1
      ring
    rw [hw, sectorPolar_arg hr ⟨hwindow.1, hwindow.2.le⟩]
  have hslit (t : unitInterval) : w t ∈ Complex.slitPlane := by
    obtain ⟨θ, hθ, he⟩ := hmem t
    apply Complex.mem_slitPlane_iff_arg.mpr
    refine ⟨?_, ?_⟩
    · rw [hbranch t hθ he]
      exact ne_of_lt (retainedWidth_midpoint_window hproper hθ).2
    · have hw : ‖w t‖ = r := by
        dsimp [w]
        rw [norm_mul, conePhase_norm, one_mul, he, sectorPolar_norm hr.le]
      apply norm_ne_zero_iff.mp
      rw [hw]
      exact hr.ne'
  have hwc : Continuous w := continuous_const.mul hc
  refine ⟨φ, continuous_const.add ?_, ?_, ?_⟩
  · exact Complex.continuousOn_arg.comp_continuous hwc hslit
  · intro t
    obtain ⟨θ, hθ, he⟩ := hmem t
    have hφ : φ t = θ := by dsimp [φ]; rw [hbranch t hθ he]; ring
    rwa [hφ]
  · intro t
    obtain ⟨θ, hθ, he⟩ := hmem t
    have hφ : φ t = θ := by dsimp [φ]; rw [hbranch t hθ he]; ring
    rwa [hφ]

/-- Equal actual cone distances force equality of sufficiently small angular
increments in continuous lifts. The entire interval need not be short. The
zero exponent is covered by the underlying small-distance theorem. -/
theorem retainedWidth_local_increment {α r A L : ℝ}
    (hα : 0 ≤ α) (hr : 0 < r) (hL : 0 < L)
    {φ : unitInterval → ℝ} (hc : Continuous φ)
    (hd : ∀ s t,
      @dist ℂ (classicalConeMetricSpace α hα).toDist
        (sectorPolar r (φ s)) (sectorPolar r (φ t)) =
      @dist ℂ (classicalConeMetricSpace α hα).toDist
        (sectorPolar r (A + L * s.1)) (sectorPolar r (A + L * t.1))) :
    ∀ t, ∀ᶠ u in 𝓝 t, |φ u - φ t| = L * |u.1 - t.1| := by
  have hk : 0 < α + 1 := by linarith
  intro t
  have hsmallφ : ∀ᶠ u in 𝓝 t, |φ u - φ t| < Real.pi / (α + 1) := by
    have hcont : ContinuousAt (fun u : unitInterval => |φ u - φ t|) t :=
      (hc.continuousAt.sub
        (continuousAt_const : ContinuousAt (fun _ : unitInterval => φ t) t)).abs
    exact hcont.eventually_lt
      (continuousAt_const : ContinuousAt (fun _ : unitInterval => Real.pi / (α + 1)) t)
      (by simpa only [sub_self, abs_zero] using div_pos Real.pi_pos hk)
  have hsmallsrc : ∀ᶠ u in 𝓝 t,
      |(A + L * u.1) - (A + L * t.1)| < Real.pi / (α + 1) := by
    have hcsrc : Continuous (fun u : unitInterval => A + L * u.1) := by fun_prop
    have hcont : ContinuousAt
        (fun u : unitInterval => |(A + L * u.1) - (A + L * t.1)|) t :=
      (hcsrc.continuousAt.sub
        (continuousAt_const : ContinuousAt (fun _ : unitInterval => A + L * t.1) t)).abs
    exact hcont.eventually_lt
      (continuousAt_const : ContinuousAt (fun _ : unitInterval => Real.pi / (α + 1)) t)
      (by simpa only [sub_self, abs_zero] using div_pos Real.pi_pos hk)
  filter_upwards [hsmallφ, hsmallsrc] with u hu hv
  have hlocal (d : ℝ) (h : |d| < Real.pi / (α + 1)) :
      |d| < Real.pi ∧ (α + 1) * |d| < Real.pi := by
    have hp : (α + 1) * |d| < Real.pi := by
      have := (lt_div_iff₀ hk).mp h
      nlinarith
    exact ⟨(show |d| ≤ (α + 1) * |d| by
      nlinarith [mul_nonneg hα (abs_nonneg d)]).trans_lt hp, hp⟩
  have hu' := hlocal (φ u - φ t) hu
  have hv' := hlocal ((A + L * u.1) - (A + L * t.1)) hv
  have hsquare := congrArg (fun x : ℝ => x ^ 2) (hd u t)
  rw [classicalCone_polar_small_distance_sq hα hr hu'.1 hu'.2.le,
    classicalCone_polar_small_distance_sq hα hr hv'.1 hv'.2.le] at hsquare
  have hcos : Real.cos ((α + 1) * |φ u - φ t|) =
      Real.cos ((α + 1) * |(A + L * u.1) - (A + L * t.1)|) := by
    have hz : (2 * r * r) *
        (Real.cos ((α + 1) * |φ u - φ t|) -
          Real.cos ((α + 1) * |(A + L * u.1) - (A + L * t.1)|)) = 0 := by
      nlinarith [hsquare]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (by positivity))
  have he := Real.strictAntiOn_cos.injOn
    (show (α + 1) * |φ u - φ t| ∈ Icc 0 Real.pi from
      ⟨mul_nonneg hk.le (abs_nonneg _), hu'.2.le⟩)
    (show (α + 1) * |(A + L * u.1) - (A + L * t.1)| ∈ Icc 0 Real.pi from
      ⟨mul_nonneg hk.le (abs_nonneg _), hv'.2.le⟩) hcos
  have habs := mul_left_cancel₀ hk.ne' he
  calc
    |φ u - φ t| = |(A + L * u.1) - (A + L * t.1)| := habs
    _ = |L * (u.1 - t.1)| := by congr 1; ring
    _ = L * |u.1 - t.1| := by rw [abs_mul, abs_of_pos hL]

/-- An actual equal-radius cone-isometric proper source arc occupying a
proper target interval has no greater FULL coordinate width. This includes
all reflex intervals. Source and target may have different base directions. -/
theorem classicalCone_retained_arc_width_le {α r A L lo hi : ℝ}
    (hα : 0 ≤ α) (hr : 0 < r) (hL : 0 < L) (hLfull : L < 2 * Real.pi)
    (hproper : hi - lo < 2 * Real.pi)
    {v : unitInterval → ℂ} (hc : Continuous v)
    (hmem : ∀ t, ∃ θ ∈ Icc lo hi, v t = sectorPolar r θ)
    (hd : ∀ s t,
      @dist ℂ (classicalConeMetricSpace α hα).toDist (v s) (v t) =
      @dist ℂ (classicalConeMetricSpace α hα).toDist
        (sectorPolar r (A + L * s.1)) (sectorPolar r (A + L * t.1))) :
    L ≤ hi - lo := by
  obtain ⟨φ, hφ, hφmem, hpolar⟩ := retainedWidth_exists_target_lift hr hproper hc hmem
  have hiφ : Function.Injective φ := by
    intro s t hst
    have hv : v s = v t := by rw [hpolar s, hpolar t, hst]
    have hdist := hd s t
    rw [hv, @dist_self ℂ (classicalConeMetricSpace α hα).toPseudoMetricSpace] at hdist
    have he : sectorPolar r (A + L * s.1) = sectorPolar r (A + L * t.1) :=
      (@dist_eq_zero ℂ (classicalConeMetricSpace α hα) _ _).mp hdist.symm
    exact retainedWidth_polar_arc_injective hr hL hLfull he
  have hmetric : ∀ s t,
      @dist ℂ (classicalConeMetricSpace α hα).toDist
        (sectorPolar r (φ s)) (sectorPolar r (φ t)) =
      @dist ℂ (classicalConeMetricSpace α hα).toDist
        (sectorPolar r (A + L * s.1)) (sectorPolar r (A + L * t.1)) := by
    intro s t
    rw [← hpolar s, ← hpolar t]
    exact hd s t
  rcases flatLink_real_lift_rigidity hφ hiφ
    (retainedWidth_local_increment hα hr hL hφ hmetric) with hp | hm
  · have h := hp 1
    change φ 1 = φ 0 + L * 1 at h
    linarith [(hφmem 0).1, (hφmem 1).2]
  · have h := hm 1
    change φ 1 = φ 0 - L * 1 at h
    linarith [(hφmem 1).1, (hφmem 0).2]

end RepulsiveCoulomb
