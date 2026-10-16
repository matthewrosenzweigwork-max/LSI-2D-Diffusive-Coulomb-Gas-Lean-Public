module

public import LeanResearch.RepulsiveCoulomb.PointFiniteRadialCornerGeometry
public import LeanResearch.RepulsiveCoulomb.PointFiniteCyclicCornerOrder
public import LeanResearch.RepulsiveCoulomb.PointRotatedRadialChart
public import LeanResearch.RepulsiveCoulomb.PointRadialCyclicTurnCharts

@[expose] public section

/-! Build the actual finite corner geometry from the literal chosen charts
and radial germs carried by the original macro-arcs. A common positive width
and target disk are chosen inside those original germs. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

/-- Given the literal cyclic re-enumeration, every actual macro-corner has
a normalized geometric record. No normalized collar or corner angle is an
input: both are constructed from its two original physical radial germs. -/
theorem exists_point_radial_corner_geometry_of_order
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (arcs : ℕ → PointRadialC1PlaneArc ha y) (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k ≤ n)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      (arcs i).curve s = (arcs j).curve t → i = j ∧ s = t)
    (q : ℕ → ℕ) (hq : ∀ i ≤ n, q i ≤ n)
    (hqi : ∀ i ≤ n, ∀ j ≤ n, q i = q j → i = j)
    (hqs : ∀ j ≤ n, ∃ i ≤ n, q i = j) (hq0 : q 0 = k)
    (hqv : ∀ i < n, (arcs (q i)).curve 1 = (arcs (q (i + 1))).curve 0)
    (hqc : (arcs (q n)).curve 1 = (arcs (q 0)).curve 0) :
    ∃ θ : ℝ, ∃ D : PointFiniteRadialCornerAt (fun i => (arcs i).curve) n k θ, D.order = q := by
  let p := (arcs k).curve 0
  let e := pointChosenSmoothRadialChart ha y p
  have hqn : q n ≠ k := by
    intro he
    have hzero := hqi n le_rfl 0 (Nat.zero_le n) (he.trans hq0.symm)
    omega
  have hjoin : (arcs (q n)).curve 1 = p := by simpa only [hq0, p] using hqc
  have hdisj : Disjoint ((arcs (q n)).curve '' Ico (0 : ℝ) 1)
      ((arcs k).curve '' Ico (0 : ℝ) 1) := by
    apply disjoint_left.mpr
    rintro z ⟨s, hs, hsz⟩ ⟨t, ht, htz⟩
    exact hqn (hinj (q n) k (hq n le_rfl) hk s t hs ht (hsz.trans htz.symm)).1
  have hright := (arcs (q n)).right_radial
  rw [hjoin] at hright
  have hleft := (arcs k).left_radial
  have hno := radial_corner_not_positive_multiple_of_halfOpen_disjoint hdisj hright hleft
  have hnorev : ¬ ∃ c : ℝ, 0 < c ∧ (arcs (q n)).rightVector = c • (arcs k).leftVector := by
    rintro ⟨c, hc, he⟩
    apply hno
    refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
    rw [he, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  obtain ⟨_, _, hep, hp, hInv, hFor, _⟩ := pointChosenSmoothRadialChart_spec ha y p
  have h0t : (0 : ℂ) ∈ e.target := hep ▸ e.mapsTo hp
  have hInvReg : deriv e.symm 0 ≠ 0 := pointChosenSmoothRadialChart_inverse_deriv_ne_zero ha y p h0t
  obtain ⟨c, hc, θ, hθ, hθ2, E, _, hEp, hE0, _, _, hEA, hEI, hED, hL, hR⟩ :=
    exists_normalized_actual_radial_chart e hp hep (fun z hz => (hFor z hz).1)
      hInv hInvReg (arcs k).leftVector_ne (arcs (q n)).rightVector_ne hnorev
  have hEL : (arcs k).curve =ᶠ[𝓝 (0 : ℝ)] (fun t =>
      E.symm (pointRadialSectorPoint (‖(arcs k).leftVector‖ * t) 0)) := by
    filter_upwards [hleft] with t ht
    exact ht.trans (hL t)
  have hER : (arcs (q n)).curve =ᶠ[𝓝 (1 : ℝ)] (fun t =>
      E.symm (pointRadialSectorPoint (‖(arcs (q n)).rightVector‖ * (1 - t)) θ)) := by
    filter_upwards [hright] with t ht
    exact ht.trans (hR (1 - t))
  obtain ⟨εL, hεL, hlocL⟩ := Metric.mem_nhds_iff.mp hEL
  obtain ⟨εR, hεR, hlocR⟩ := Metric.mem_nhds_iff.mp hER
  have hEtarget : (0 : ℂ) ∈ E.target := hE0 ▸ E.mapsTo hEp
  obtain ⟨R, hRpos, hball⟩ := Metric.mem_nhds_iff.mp (E.open_target.mem_nhds hEtarget)
  let cL := ‖(arcs k).leftVector‖
  let cR := ‖(arcs (q n)).rightVector‖
  have hcL : 0 < cL := norm_pos_iff.mpr (arcs k).leftVector_ne
  have hcR : 0 < cR := norm_pos_iff.mpr (arcs (q n)).rightVector_ne
  let δ := min (1 / 4 : ℝ) (min (εL / 2) (min (εR / 2) (min (R / (2 * cL)) (R / (2 * cR)))))
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by positivity)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  have hδq : δ ≤ 1 / 4 := min_le_left _ _
  have hδL : δ ≤ εL / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδR : δ ≤ εR / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδcL : δ ≤ R / (2 * cL) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδcR : δ ≤ R / (2 * cR) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let D : PointFiniteRadialCornerAt (fun i => (arcs i).curve) n k θ := by
    refine
      { order := q
        order_le := hq
        order_injective := hqi
        order_surjective := hqs
        order_zero := hq0
        consecutive := hqv
        closing := hqc
        chart := E
        source := hEp
        origin := hE0
        forward_analytic := hEA
        inverse_analytic := hEI
        inverse_regular := hED
        width := δ
        width_pos := hδ
        width_half := by linarith
        leftRate := cL
        rightRate := cR
        leftRate_pos := hcL
        rightRate_pos := hcR
        radius := R
        radius_pos := hRpos
        angle_pos := hθ
        angle_lt := hθ2
        target_ball := hball
        left_radius := ?_
        right_radius := ?_
        left_collar := ?_
        right_collar := ?_ }
    · have hb := (le_div_iff₀ (show 0 < 2 * cL by positivity)).mp hδcL
      nlinarith
    · have hb := (le_div_iff₀ (show 0 < 2 * cR by positivity)).mp hδcR
      nlinarith
    · intro t ht htd
      apply hlocL
      rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht.1]
      linarith
    · intro t ht htd
      apply hlocR
      rw [mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr ht.2)]
      linarith
  exact ⟨θ, D, rfl⟩

/-- Every vertex of the genuine finite radial family supplies its actual
normalized corner geometry, including its constructed original cyclic order. -/
theorem exists_point_radial_finite_corner_geometry
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (arcs : ℕ → PointRadialC1PlaneArc ha y) (n : ℕ) (hn : 0 < n)
    (hv : ∀ i < n, (arcs i).curve 1 = (arcs (i + 1)).curve 0)
    (hclose : (arcs n).curve 1 = (arcs 0).curve 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      (arcs i).curve s = (arcs j).curve t → i = j ∧ s = t)
    (k : ℕ) (hk : k ≤ n) :
    ∃ θ : ℝ, ∃ D : PointFiniteRadialCornerAt (fun i => (arcs i).curve) n k θ,
      D.order = pointFiniteCyclicCornerOrder n k := by
  exact exists_point_radial_corner_geometry_of_order ha y arcs n hn k hk hinj
    (pointFiniteCyclicCornerOrder n k)
    (fun i _ => pointFiniteCyclicCornerOrder_le n k i)
    (fun i hi j hj he => pointFiniteCyclicCornerOrder_injective n k hi hj he)
    (fun j hj => pointFiniteCyclicCornerOrder_surjective n k hk hj)
    (pointFiniteCyclicCornerOrder_zero n k hk)
    (fun i _ => pointFiniteCyclicCornerOrder_consecutive (fun j => (arcs j).curve) n k hv hclose i)
    (pointFiniteCyclicCornerOrder_closing (fun j => (arcs j).curve) n k hk hv hclose)

end RepulsiveCoulomb
