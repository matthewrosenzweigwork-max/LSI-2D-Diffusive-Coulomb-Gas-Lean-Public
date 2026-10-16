module

public import LeanResearch.RepulsiveCoulomb.PointFiniteRadialCornerGeometry
public import LeanResearch.RepulsiveCoulomb.PointFiniteCyclicCornerOrder
public import LeanResearch.RepulsiveCoulomb.PointRotatedRadialChart
public import LeanResearch.RepulsiveCoulomb.PointRadialCyclicTurnCharts
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! Uncompiled records-only successor retaining the actual chosen-chart
rotation that the earlier constructor deliberately forgot. Construct a genuine
radial boundary-atom record inside a mixed finite family. Only the incoming and outgoing original germs at the chosen vertex
are radial. All other arcs, including ordinary circle cap arcs, are arbitrary.
The normalized chart, full angle, radius and common collar width are built. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

/-- Local original radial germs at one physical atom suffice to construct
its actual normalized boundary geometry in the complete original family. -/
theorem exists_point_finite_radial_corner_with_chosen_rotation
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hn : 0 < n)
    (hv : ∀ i < n, f i 1 = f (i + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t)
    (k : ℕ) (hk : k ≤ n) (u v : ℂ) (hu : u ≠ 0) (hv0 : v ≠ 0)
    (hleft : f k =ᶠ[𝓝 (0 : ℝ)]
      (fun t => (pointChosenSmoothRadialChart ha y (f k 0)).symm (t • v)))
    (hright : f (if k = 0 then n else k - 1) =ᶠ[𝓝 (1 : ℝ)]
      (fun t => (pointChosenSmoothRadialChart ha y (f k 0)).symm ((1 - t) • u))) :
    ∃ θ : ℝ, ∃ D : PointFiniteRadialCornerAt f n k θ,
      D.order = pointFiniteCyclicCornerOrder n k ∧
      ∃ c : ℂ, ‖c‖ = 1 ∧ D.chart.source =
        (pointChosenSmoothRadialChart ha y (f k 0)).source ∧ ∀ z, D.chart z =
        c * pointChosenSmoothRadialChart ha y (f k 0) z := by
  let q := pointFiniteCyclicCornerOrder n k
  have hq : ∀ i ≤ n, q i ≤ n := fun i _ => pointFiniteCyclicCornerOrder_le n k i
  have hqi : ∀ i ≤ n, ∀ j ≤ n, q i = q j → i = j :=
    fun i hi j hj he => pointFiniteCyclicCornerOrder_injective n k hi hj he
  have hqs : ∀ j ≤ n, ∃ i ≤ n, q i = j :=
    fun j hj => pointFiniteCyclicCornerOrder_surjective n k hk hj
  have hq0 : q 0 = k := pointFiniteCyclicCornerOrder_zero n k hk
  have hqv : ∀ i < n, f (q i) 1 = f (q (i + 1)) 0 :=
    fun i _ => pointFiniteCyclicCornerOrder_consecutive f n k hv hclose i
  have hqc : f (q n) 1 = f (q 0) 0 := pointFiniteCyclicCornerOrder_closing f n k hk hv hclose
  let p := f k 0
  let e := pointChosenSmoothRadialChart ha y p
  have hqn : q n ≠ k := by
    intro he
    have hzero := hqi n le_rfl 0 (Nat.zero_le n) (he.trans hq0.symm)
    omega
  have hjoin : f (q n) 1 = p := by simpa only [hq0, p] using hqc
  have hdisj : Disjoint (f (q n) '' Ico (0 : ℝ) 1)
      (f k '' Ico (0 : ℝ) 1) := by
    apply disjoint_left.mpr
    rintro z ⟨s, hs, hsz⟩ ⟨t, ht, htz⟩
    exact hqn (hinj (q n) k (hq n le_rfl) hk s t hs ht (hsz.trans htz.symm)).1
  have hright' : f (q n) =ᶠ[𝓝 (1 : ℝ)]
      (fun t => (pointChosenSmoothRadialChart ha y (f k 0)).symm ((1 - t) • u)) := by
    simpa only [q, pointFiniteCyclicCornerOrder_last n k hk] using hright
  have hno := radial_corner_not_positive_multiple_of_halfOpen_disjoint hdisj hright' hleft
  have hnorev : ¬ ∃ c : ℝ, 0 < c ∧ u = c • v := by
    rintro ⟨c, hc, he⟩
    apply hno
    refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
    rw [he, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  obtain ⟨_, _, hep, hp, hInv, hFor, _⟩ := pointChosenSmoothRadialChart_spec ha y p
  have h0t : (0 : ℂ) ∈ e.target := hep ▸ e.mapsTo hp
  have hInvReg : deriv e.symm 0 ≠ 0 := pointChosenSmoothRadialChart_inverse_deriv_ne_zero ha y p h0t
  obtain ⟨c, hc, θ, hθ, hθ2, E, hEsource, hEp, hE0, hEforward, hEinverse, hEA, hEI, hED, hL, hR⟩ :=
    exists_normalized_actual_radial_chart e hp hep (fun z hz => (hFor z hz).1)
      hInv hInvReg hv0 hu hnorev
  have hEL : f k =ᶠ[𝓝 (0 : ℝ)] (fun t =>
      E.symm (pointRadialSectorPoint (‖v‖ * t) 0)) := by
    filter_upwards [hleft] with t ht
    exact ht.trans (hL t)
  have hER : f (q n) =ᶠ[𝓝 (1 : ℝ)] (fun t =>
      E.symm (pointRadialSectorPoint (‖u‖ * (1 - t)) θ)) := by
    filter_upwards [hright'] with t ht
    exact ht.trans (hR (1 - t))
  obtain ⟨εL, hεL, hlocL⟩ := Metric.mem_nhds_iff.mp hEL
  obtain ⟨εR, hεR, hlocR⟩ := Metric.mem_nhds_iff.mp hER
  have hEtarget : (0 : ℂ) ∈ E.target := hE0 ▸ E.mapsTo hEp
  obtain ⟨R, hRpos, hball⟩ := Metric.mem_nhds_iff.mp (E.open_target.mem_nhds hEtarget)
  let cL := ‖v‖
  let cR := ‖u‖
  have hcL : 0 < cL := norm_pos_iff.mpr hv0
  have hcR : 0 < cR := norm_pos_iff.mpr hu
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
  let D : PointFiniteRadialCornerAt f n k θ := by
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
  exact ⟨θ, D, rfl, c, hc, hEsource, hEforward⟩

end RepulsiveCoulomb
