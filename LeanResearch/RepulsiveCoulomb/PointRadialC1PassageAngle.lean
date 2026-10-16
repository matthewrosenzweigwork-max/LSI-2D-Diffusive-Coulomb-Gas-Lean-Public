import LeanResearch.RepulsiveCoulomb.PointRadialC1ArcChain
import LeanResearch.RepulsiveCoulomb.PointGeodesicTriangleCorner

/-! Passage-angle bounds in the same chosen holomorphic chart carried by the
actual C1 macro-pieces. The source geodesic supplies metric additivity; the
chosen chart supplies its actual power-cone metric. No angle bound is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- Recover the metric information of the already chosen common chart. -/
theorem pointChosenSmoothRadialChart_metric_spec
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    let E := pointChosenSmoothRadialChart ha y p
    ∃ R : ℝ, 0 < R ∧ E p = 0 ∧
      (∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ R → z ∈ E.source) ∧
      ∀ u, (pointSmoothConformalEDist a y u p).toReal ≤ R →
        ∀ v, (pointSmoothConformalEDist a y v p).toReal ≤ R →
          pointSmoothConformalEDist a y u v =
            pointSmoothConformalEDist (standardConeExponents (coalescedPointExponent a y p / 2))
              standardConeLocations (E u) (E v) := by
  obtain ⟨R, hR, hE0, _, _, hsource, hmetric, _⟩ :=
    Classical.choose_spec (exists_pointConformal_smooth_radial_germ_chart ha y p)
  exact ⟨R, hR, hE0, hsource, hmetric⟩

/-- Two adjacent actual source pieces inherit exact metric additivity at
all their points from the same original minimizing geodesic. -/
theorem PointRadialC1ArcPiece.join_metric_additive
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {γ : Icc (0 : ℝ) 1 → ℂ} (e f : PointRadialC1ArcPiece ha y γ)
    (hjoin : e.finish = f.start) {D : ℝ}
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = |t.1 - s.1| * D)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (pointSmoothConformalEDist a y (e.curve s) (f.curve t)).toReal =
      (pointSmoothConformalEDist a y (e.curve s) (γ e.finish)).toReal +
      (pointSmoothConformalEDist a y (γ e.finish) (f.curve t)).toReal := by
  have he : e.curve s ∈ γ '' Icc e.start e.finish := by
    rw [← e.image]
    exact ⟨s, hs, rfl⟩
  have hf : f.curve t ∈ γ '' Icc f.start f.finish := by
    rw [← f.image]
    exact ⟨t, ht, rfl⟩
  obtain ⟨u, hu, heu⟩ := he
  obtain ⟨v, hv, hfv⟩ := hf
  have hur : (u : ℝ) ≤ e.finish := hu.2
  have hrv : (e.finish : ℝ) ≤ v := by
    rw [hjoin]
    exact hv.1
  rw [← heu, ← hfv, hd, hd, hd,
    abs_of_nonneg (sub_nonneg.mpr (hur.trans hrv)),
    abs_of_nonneg (sub_nonneg.mpr hur), abs_of_nonneg (sub_nonneg.mpr hrv)]
  ring

/-- Metric additivity in power-cone coordinates gives both sector bounds.
The classical radial isometry preserves precisely the coordinate argument. -/
theorem standardCone_equal_radius_minimizing_turns_nonpos
    {α : ℝ} (hα : 0 ≤ α) {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hn : ‖u‖ = ‖v‖)
    (hmin : (pointSmoothConformalEDist (standardConeExponents α) standardConeLocations u v).toReal =
      coneRadialPotential α u + coneRadialPotential α v) :
    Real.pi - coneShortSectorAngle α u v ≤ 0 ∧
      Real.pi - coneLongSectorAngle α u v ≤ 0 := by
  let E := coneRadialEquiv α hα
  have hdist : @dist ℂ (classicalConeMetricSpace α hα).toDist (E u) (E v) =
      (pointSmoothConformalEDist (standardConeExponents α) standardConeLocations u v).toReal := by
    change (pointSmoothConformalEDist (standardConeExponents α) standardConeLocations
      (E.symm (E u)) (E.symm (E v))).toReal = _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hminE : @dist ℂ (classicalConeMetricSpace α hα).toDist (E u) (E v) = ‖E u‖ + ‖E v‖ := by
    simpa only [E, coneRadialEquiv_norm] using hdist.trans hmin
  have hnE : ‖E u‖ = ‖E v‖ := by
    simp only [E, coneRadialEquiv_norm, coneRadialPotential, hn]
  have hturn := cone_equal_radius_minimizing_turns_nonpos hα
    (coneRadialEquiv_ne_zero hα hu) (coneRadialEquiv_ne_zero hα hv) hnE hminE
  simpa only [coneShortSectorAngle, coneLongSectorAngle, E, coneRadialEquiv_arg_div] using hturn

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

/-- Both actual side sectors at an internal macro-vertex have nonpositive
metric turn. The radial vectors are those stored in the SAME chosen chart
by the original source pieces, so no chart-angle compatibility is assumed. -/
theorem PointRadialC1ArcPiece.join_sector_turns_nonpos
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {γ : Icc (0 : ℝ) 1 → ℂ} (e f : PointRadialC1ArcPiece ha y γ)
    (hjoin : e.finish = f.start) {D : ℝ}
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = |t.1 - s.1| * D) :
    Real.pi - coneShortSectorAngle (coalescedPointExponent a y (γ e.finish) / 2)
      e.rightVector f.leftVector ≤ 0 ∧
    Real.pi - coneLongSectorAngle (coalescedPointExponent a y (γ e.finish) / 2)
      e.rightVector f.leftVector ≤ 0 := by
  let p := γ e.finish
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
  have hL0 : L 0 = p := by simpa only [L, zero_div, sub_zero, p] using e.at_one
  have hG0 : G 0 = p := by simpa only [G, zero_div, p, hjoin] using f.at_zero
  have hLc : Continuous L := e.smooth.continuous.comp (by fun_prop)
  have hGc : Continuous G := f.smooth.continuous.comp (by fun_prop)
  have hLb := point_metric_bound_eventually ha y hLc.continuousAt hL0 hR
  have hGb := point_metric_bound_eventually ha y hGc.continuousAt hG0 hR
  have hleft : ∀ᶠ r in 𝓝 (0 : ℝ), L r = E.symm ((r / ‖u‖) • u) := by
    have ht : Tendsto (fun r : ℝ => 1 - r / ‖u‖) (𝓝 0) (𝓝 1) := by
      simpa using (show Continuous (fun r : ℝ => 1 - r / ‖u‖) by fun_prop).tendsto 0
    filter_upwards [e.right_radial.comp_tendsto ht] with r he
    simpa only [Function.comp_def, sub_sub_cancel, L, E, p, u] using he
  have hright : ∀ᶠ r in 𝓝 (0 : ℝ), G r = E.symm ((r / ‖v‖) • v) := by
    have ht : Tendsto (fun r : ℝ => r / ‖v‖) (𝓝 0) (𝓝 0) := by
      simpa using (show Continuous (fun r : ℝ => r / ‖v‖) by fun_prop).tendsto 0
    filter_upwards [f.left_radial.comp_tendsto ht] with r he
    simpa only [Function.comp_def, G, E, p, v, hjoin] using he
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
      (pointSmoothConformalEDist a y (L r) p).toReal ≤ R ∧
      (pointSmoothConformalEDist a y (G r) p).toReal ≤ R := by
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
  have hmin := e.join_metric_additive f hjoin hd
    (show 1 - r / ‖u‖ ∈ Icc (0 : ℝ) 1 by constructor <;> linarith)
    (show r / ‖v‖ ∈ Icc (0 : ℝ) 1 from ⟨hvz.le, hvz1.le⟩)
  change (pointSmoothConformalEDist a y (L r) (G r)).toReal =
    (pointSmoothConformalEDist a y (L r) p).toReal +
      (pointSmoothConformalEDist a y p (G r)).toReal at hmin
  rw [hmetric _ hlb _ hgb, hmetric _ hlb _ hpR, hmetric _ hpR _ hgb,
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
