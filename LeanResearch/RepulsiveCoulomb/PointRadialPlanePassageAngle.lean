import LeanResearch.RepulsiveCoulomb.PointRadialC1PassageAngle
import LeanResearch.RepulsiveCoulomb.PointRadialC1PlaneArc

/-! The same-chart passage bound for two actual radial plane arcs with local
metric additivity. This covers the retained triangle corner even when its
incoming and outgoing germs have different original geodesic sources. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

private theorem point_metric_bound_eventually
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {C : ℝ → ℂ} (hC : ContinuousAt C 0) {p : ℂ} (hC0 : C 0 = p)
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ t in 𝓝 (0 : ℝ), (pointSmoothConformalEDist a y (C t) p).toReal ≤ R := by
  have hlim := (pointSmoothConformalEDist_tendsto_zero ha y p).comp
    (show Tendsto C (𝓝 0) (𝓝 p) by simpa only [hC0] using hC.tendsto)
  have he := hlim.eventually (eventually_lt_nhds (ENNReal.ofReal_pos.mpr hR))
  filter_upwards [he] with t ht
  rw [pointSmoothConformalEDist_comm a y (C t) p]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top ht.le).trans_eq (ENNReal.toReal_ofReal hR.le)

/-- Actual local metric additivity at a common vertex forces both metric
sector turns to be nonpositive in the SAME chosen holomorphic chart. -/
theorem PointRadialC1PlaneArc.local_passage_sector_turns_nonpos
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    (e f : PointRadialC1PlaneArc ha y) (hjoin : e.curve 1 = f.curve 0)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hlocal : ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      (pointSmoothConformalEDist a y (e.curve s) (e.curve 1)).toReal ≤ r₀ →
      (pointSmoothConformalEDist a y (f.curve t) (e.curve 1)).toReal ≤ r₀ →
      (pointSmoothConformalEDist a y (e.curve s) (f.curve t)).toReal =
        (pointSmoothConformalEDist a y (e.curve s) (e.curve 1)).toReal +
        (pointSmoothConformalEDist a y (e.curve 1) (f.curve t)).toReal) :
    Real.pi - coneShortSectorAngle (coalescedPointExponent a y (e.curve 1) / 2)
      e.rightVector f.leftVector ≤ 0 ∧
    Real.pi - coneLongSectorAngle (coalescedPointExponent a y (e.curve 1) / 2)
      e.rightVector f.leftVector ≤ 0 := by
  let p := e.curve 1
  let E := pointChosenSmoothRadialChart ha y p
  let u := e.rightVector
  let v := f.leftVector
  let L : ℝ → ℂ := fun r => e.curve (1 - r / ‖u‖)
  let G : ℝ → ℂ := fun r => f.curve (r / ‖v‖)
  have hu : 0 < ‖u‖ := norm_pos_iff.mpr e.rightVector_ne
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr f.leftVector_ne
  obtain ⟨R, hR, hE0, hsource, hmetric⟩ := pointChosenSmoothRadialChart_metric_spec ha y p
  change E p = 0 at hE0
  change ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ R → z ∈ E.source at hsource
  change ∀ u, (pointSmoothConformalEDist a y u p).toReal ≤ R →
    ∀ v, (pointSmoothConformalEDist a y v p).toReal ≤ R →
      pointSmoothConformalEDist a y u v =
        pointSmoothConformalEDist (standardConeExponents (coalescedPointExponent a y p / 2))
          standardConeLocations (E u) (E v) at hmetric
  have hpR : (pointSmoothConformalEDist a y p p).toReal ≤ R := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact hR.le
  have hEt : (0 : ℂ) ∈ E.target := hE0 ▸ E.mapsTo (hsource p hpR)
  have hL0 : L 0 = p := by simp only [L, zero_div, sub_zero, p]
  have hG0 : G 0 = p := by simpa only [G, zero_div, p] using hjoin.symm
  have hLc : Continuous L := e.smooth.continuous.comp (by fun_prop)
  have hGc : Continuous G := f.smooth.continuous.comp (by fun_prop)
  have hsmall : 0 < min R r₀ := lt_min hR hr₀
  have hLb := point_metric_bound_eventually ha y hLc.continuousAt hL0 hsmall
  have hGb := point_metric_bound_eventually ha y hGc.continuousAt hG0 hsmall
  have hleft : ∀ᶠ r in 𝓝 (0 : ℝ), L r = E.symm ((r / ‖u‖) • u) := by
    have ht : Tendsto (fun r : ℝ => 1 - r / ‖u‖) (𝓝 0) (𝓝 1) := by
      simpa using (show Continuous (fun r : ℝ => 1 - r / ‖u‖) by fun_prop).tendsto 0
    filter_upwards [e.right_radial.comp_tendsto ht] with r he
    simpa only [Function.comp_def, sub_sub_cancel, L, E, p, u] using he
  have hright : ∀ᶠ r in 𝓝 (0 : ℝ), G r = E.symm ((r / ‖v‖) • v) := by
    have ht : Tendsto (fun r : ℝ => r / ‖v‖) (𝓝 0) (𝓝 0) := by
      simpa using (show Continuous (fun r : ℝ => r / ‖v‖) by fun_prop).tendsto 0
    filter_upwards [f.left_radial.comp_tendsto ht] with r he
    simpa only [Function.comp_def, G, E, p, v, ← hjoin] using he
  have htu : ∀ᶠ r in 𝓝 (0 : ℝ), (r / ‖u‖) • u ∈ E.target := by
    have ht : Tendsto (fun r : ℝ => (r / ‖u‖) • u) (𝓝 0) (𝓝 0) := by
      simpa using (show Continuous (fun r : ℝ => (r / ‖u‖) • u) by fun_prop).tendsto 0
    exact ht.eventually (E.open_target.mem_nhds hEt)
  have htv : ∀ᶠ r in 𝓝 (0 : ℝ), (r / ‖v‖) • v ∈ E.target := by
    have ht : Tendsto (fun r : ℝ => (r / ‖v‖) • v) (𝓝 0) (𝓝 0) := by
      simpa using (show Continuous (fun r : ℝ => (r / ‖v‖) • v) by fun_prop).tendsto 0
    exact ht.eventually (E.open_target.mem_nhds hEt)
  have hall : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r < ‖u‖ ∧ r < ‖v‖ ∧
      L r = E.symm ((r / ‖u‖) • u) ∧ G r = E.symm ((r / ‖v‖) • v) ∧
      (r / ‖u‖) • u ∈ E.target ∧ (r / ‖v‖) • v ∈ E.target ∧
      (pointSmoothConformalEDist a y (L r) p).toReal ≤ min R r₀ ∧
      (pointSmoothConformalEDist a y (G r) p).toReal ≤ min R r₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hu).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hv).filter_mono nhdsWithin_le_nhds,
      hleft.filter_mono nhdsWithin_le_nhds, hright.filter_mono nhdsWithin_le_nhds,
      htu.filter_mono nhdsWithin_le_nhds, htv.filter_mono nhdsWithin_le_nhds,
      hLb.filter_mono nhdsWithin_le_nhds, hGb.filter_mono nhdsWithin_le_nhds]
      with r hr hru hrv hl hg htu htv hlb hgb
    exact ⟨hr, hru, hrv, hl, hg, htu, htv, hlb, hgb⟩
  obtain ⟨r, hr, hru, hrv, hl, hg, htu, htv, hlb, hgb⟩ := hall.exists
  let x : ℂ := (r / ‖u‖) • u
  let z : ℂ := (r / ‖v‖) • v
  have hux : 0 < r / ‖u‖ := div_pos hr hu
  have hvz : 0 < r / ‖v‖ := div_pos hr hv
  have hux1 : r / ‖u‖ < 1 := (div_lt_one hu).mpr hru
  have hvz1 : r / ‖v‖ < 1 := (div_lt_one hv).mpr hrv
  have hx : E (L r) = x := by rw [hl]; exact E.right_inv htu
  have hz : E (G r) = z := by rw [hg]; exact E.right_inv htv
  have hnormx : ‖x‖ = r := by
    change ‖(r / ‖u‖) • u‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hux, div_mul_cancel₀ _ hu.ne']
  have hnormz : ‖z‖ = r := by
    change ‖(r / ‖v‖) • v‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hvz, div_mul_cancel₀ _ hv.ne']
  let α := coalescedPointExponent a y p / 2
  have hα : 0 ≤ α := div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)
  have hmin := hlocal (1 - r / ‖u‖) (r / ‖v‖)
    (show 1 - r / ‖u‖ ∈ Icc (0 : ℝ) 1 by constructor <;> linarith)
    (show r / ‖v‖ ∈ Icc (0 : ℝ) 1 from ⟨hvz.le, hvz1.le⟩)
    (hlb.trans (min_le_right _ _)) (hgb.trans (min_le_right _ _))
  change (pointSmoothConformalEDist a y (L r) (G r)).toReal =
    (pointSmoothConformalEDist a y (L r) p).toReal +
      (pointSmoothConformalEDist a y p (G r)).toReal at hmin
  have hlR := hlb.trans (min_le_left R r₀)
  have hgR := hgb.trans (min_le_left R r₀)
  rw [hmetric _ hlR _ hgR, hmetric _ hlR _ hpR, hmetric _ hpR _ hgR,
    hx, hz, hE0] at hmin
  change (pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x z).toReal =
    (pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x 0).toReal +
      (pointSmoothConformalEDist (standardConeExponents α) standardConeLocations 0 z).toReal at hmin
  rw [pointSmoothConformalEDist_comm (standardConeExponents α) standardConeLocations x 0,
    standardCone_distance_from_apex_nonneg hα, standardCone_distance_from_apex_nonneg hα,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hmin
  have hpot : (pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x z).toReal =
      coneRadialPotential α x + coneRadialPotential α z := by
    simpa only [coneRadialPotential, div_eq_mul_inv, mul_comm] using hmin
  have hturn := standardCone_equal_radius_minimizing_turns_nonpos hα
    (norm_ne_zero_iff.mp (by rw [hnormx]; exact hr.ne'))
    (norm_ne_zero_iff.mp (by rw [hnormz]; exact hr.ne'))
    (hnormx.trans hnormz.symm) hpot
  have harg : Complex.arg (z / x) = Complex.arg (v / u) := by
    change Complex.arg (((r / ‖v‖) • v) / ((r / ‖u‖) • u)) = _
    simp only [Complex.real_smul]
    rw [mul_div_mul_comm, ← Complex.ofReal_div, Complex.arg_real_mul _ (div_pos hvz hux)]
  simpa only [coneShortSectorAngle, coneLongSectorAngle, harg, α, p, u, v] using hturn

end RepulsiveCoulomb
