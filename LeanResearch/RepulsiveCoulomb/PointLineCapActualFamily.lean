module

public import LeanResearch.RepulsiveCoulomb.PointLineRadialCrossings
public import LeanResearch.RepulsiveCoulomb.PointLineCapFixedNormal
public import LeanResearch.RepulsiveCoulomb.PointLineCapCompactExhaustion
public import LeanResearch.RepulsiveCoulomb.PointCompleteLineTransverseTails

@[expose] public section

/-! Records-only, uncompiled. Construct actual cap geometry from the actual
line, then identify one fixed component and a common interior anchor. The
record below is OUTPUT data of a construction, never an existence assumption
at the main complete-line endpoint. No turning or mass identity is a field. -/
noncomputable section
open Set Filter Metric Topology
namespace RepulsiveCoulomb

structure LineCapGeometry (c : ℝ → ℂ) (R : ℝ) where
  minus : ℝ
  plus : ℝ
  time_lt : minus < plus
  radius_pos : 0 < R
  alpha : ℝ
  beta : ℝ
  angle_lt : alpha < beta
  angle_width : beta < alpha + 2 * Real.pi
  crosses : ∀ t, ‖c t‖ = R ↔ t = minus ∨ t = plus
  disk_preimage : ∀ t, ‖c t‖ < R ↔ t ∈ Ioo minus plus
  circle_zero : pointCircleCapArc R alpha beta 0 = c plus
  circle_one : pointCircleCapArc R alpha beta 1 = c minus
  inside : Set ℂ
  outside : Set ℂ
  inside_open : IsOpen inside
  outside_open : IsOpen outside
  inside_connected : IsConnected inside
  outside_connected : IsConnected outside
  disjoint : Disjoint inside outside
  cover : inside ∪ outside =
    (c '' Icc minus plus ∪ pointCircleCapArc R alpha beta '' Icc (0 : ℝ) 1)ᶜ
  frontier_inside : frontier inside =
    c '' Icc minus plus ∪ pointCircleCapArc R alpha beta '' Icc (0 : ℝ) 1
  frontier_outside : frontier outside =
    c '' Icc minus plus ∪ pointCircleCapArc R alpha beta '' Icc (0 : ℝ) 1
  compact_closure : IsCompact (closure inside)

namespace LineCapGeometry
variable {c : ℝ → ℂ} {R : ℝ}

def boundary (D : LineCapGeometry c R) : Set ℂ :=
  c '' Icc D.minus D.plus ∪ pointCircleCapArc R D.alpha D.beta '' Icc (0 : ℝ) 1

theorem boundary_subset (D : LineCapGeometry c R) :
    D.boundary ⊆ range c ∪ sphere (0 : ℂ) R := by
  rintro z (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
  · exact Or.inl (mem_range_self t)
  · exact Or.inr (by simpa only [mem_sphere, dist_zero_right] using
      pointCircleCapArc_norm D.radius_pos.le D.alpha D.beta t)

theorem inside_ball_and_disjoint (D : LineCapGeometry c R) :
    D.inside ⊆ ball (0 : ℂ) R ∧ Disjoint D.inside (range c) :=
  lineCap_bounded_region_disjoint_line D.inside_open D.compact_closure D.radius_pos D.disk_preimage
    ⟨(D.crosses D.minus).mpr (Or.inl rfl), (D.crosses D.plus).mpr (Or.inr rfl)⟩ D.frontier_inside

theorem fixed_normal (D : LineCapGeometry c R) (hc : Continuous c) (hi : Function.Injective c)
    {s : ℝ} (hs : ‖c s‖ < R) (hds : DifferentiableAt ℝ c s) (hvs : deriv c s ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε, 0 < ε → ε ≤ r →
      c s + (ε : ℂ) * Complex.I * deriv c s ∈ D.inside :=
  exists_lineCap_fixed_left_normal hc hi D.time_lt D.radius_pos D.angle_lt D.angle_width
    D.crosses D.circle_zero D.circle_one ((D.disk_preimage s).mp hs) hds hvs
    D.inside_open D.inside_connected D.outside_open D.outside_connected D.compact_closure
    D.cover D.inside_ball_and_disjoint.1

end LineCapGeometry

/-- This constructor calls Jordan separation on the actual two arcs. -/
theorem exists_lineCapGeometry {c : ℝ → ℂ} (hc : Continuous c) (hi : Function.Injective c)
    {tm tp R : ℝ} (ht : tm < tp) (hR : 0 < R)
    (hm : ‖c tm‖ = R) (hp : ‖c tp‖ = R)
    (hinside : ∀ t, ‖c t‖ < R ↔ t ∈ Ioo tm tp)
    (hcross : ∀ t, ‖c t‖ = R ↔ t = tm ∨ t = tp) : Nonempty (LineCapGeometry c R) := by
  obtain ⟨α, β, hab, hwidth, hz, ho⟩ := exists_lineCapArc_angles hR hm hp
    (fun he => ht.ne (hi he))
  obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hcover, hfu, hfv, hK⟩ :=
    exists_lineCap_actual_regions hc hi hR ht hab hwidth hcross hz ho
  exact ⟨⟨tm, tp, ht, hR, α, β, hab, hwidth, hcross, hinside, hz, ho,
    U, V, hU, hV, hUc, hVc, hUV, hcover, hfu, hfv, hK⟩⟩

/-- Actual radial signs construct a full large-radius cap family and a fixed
regular line point enclosed by every member. -/
theorem exists_pointMetricLine_actual_cap_family
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {T : ℝ} (hT : 0 < T)
    (hpos : ∀ t, T < t → DifferentiableAt ℝ c t ∧ deriv c t ≠ 0 ∧
      0 < physicalRadialProjection (c t) (deriv c t))
    (hneg : ∀ t, t < -T → DifferentiableAt ℝ c t ∧ deriv c t ≠ 0 ∧
      physicalRadialProjection (c t) (deriv c t) < 0) :
    ∃ R₀ s : ℝ, 0 < R₀ ∧ ‖c s‖ < R₀ ∧ DifferentiableAt ℝ c s ∧ deriv c s ≠ 0 ∧
      Nonempty (∀ R : ℝ, R₀ < R → LineCapGeometry c R) := by
  have he := pointMetricLine_isClosedEmbedding ha y c hd
  obtain ⟨B, hB, hall⟩ := exists_pointMetricLine_transverse_large_circle_crossings ha y c hd hT
    (fun t ht => (hpos t ht).1) (fun t ht => (hneg t ht).1)
    (fun t ht => (hpos t ht).2.2) (fun t ht => (hneg t ht).2.2)
  let s := T + 1
  let R₀ := max B ‖c s‖ + 1
  have hRB : B < R₀ := by dsimp [R₀]; linarith [le_max_left B ‖c s‖]
  have hsR : ‖c s‖ < R₀ := by dsimp [R₀]; linarith [le_max_right B ‖c s‖]
  have hs := hpos s (by dsimp [s]; linarith)
  have hfamily : ∀ R : ℝ, R₀ < R → Nonempty (LineCapGeometry c R) := by
    intro R hR
    obtain ⟨tm, tp, hmT, hTp, hm, hp, hinside, hcross, _⟩ := hall R (hRB.trans hR)
    exact exists_lineCapGeometry he.continuous he.injective (by linarith)
      (hB.trans (hRB.trans hR)) hm hp hinside hcross
  exact ⟨R₀, s, hB.trans hRB, hsR, hs.1, hs.2.1,
    ⟨fun R hR => Classical.choice (hfamily R hR)⟩⟩

/-- The genuine fixed side and common anchor are constructed by overlapping
actual left-normal intervals. Neither a left-side label nor an anchor is input. -/
theorem pointMetricLine_cap_family_fixed_side
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {R₀ s : ℝ} (hsR : ‖c s‖ < R₀) (hds : DifferentiableAt ℝ c s) (hvs : deriv c s ≠ 0)
    (C : ∀ R : ℝ, R₀ < R → LineCapGeometry c R) :
    ∃ A B : Set ℂ, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = (range c)ᶜ ∧ frontier A = range c ∧ frontier B = range c ∧
      ∃ x : ℂ, x ∈ A ∧
        (∀ R (hR : R₀ < R), (C R hR).inside ⊆ A) ∧
        (∀ R (hR : R₀ + 1 ≤ R), x ∈ (C R (by linarith)).inside) := by
  have he := pointMetricLine_isClosedEmbedding ha y c hd
  obtain ⟨A, B, hA, hB, hAc, hBc, hAB, hcover, hfa, hfb⟩ :=
    exists_pointMetricLine_side_regions ha y c hd
  let D := C (R₀ + 1) (by linarith)
  have hsame (R : ℝ) (hR : R₀ < R) : (D.inside ∩ (C R hR).inside).Nonempty := by
    obtain ⟨r, hr, hnormal⟩ := D.fixed_normal he.continuous he.injective (by linarith) hds hvs
    obtain ⟨r', hr', hnormal'⟩ := (C R hR).fixed_normal he.continuous he.injective
      (hsR.trans hR) hds hvs
    exact lineCap_common_left_normal hr hr' hnormal hnormal'
  have hbranch (R : ℝ) (hR : R₀ < R) : (C R hR).inside ⊆ A ∨ (C R hR).inside ⊆ B :=
    lineCap_bounded_region_in_one_line_side (C R hR).inside_connected
      (C R hR).inside_ball_and_disjoint.2 hA hB hAB hcover
  have hbuild (A' B' : Set ℂ) (hA' : IsOpen A') (hB' : IsOpen B')
      (hAc' : IsConnected A') (hBc' : IsConnected B') (hAB' : Disjoint A' B')
      (hcover' : A' ∪ B' = (range c)ᶜ) (hfa' : frontier A' = range c)
      (hfb' : frontier B' = range c) (hDA : D.inside ⊆ A')
      (hbranches : ∀ R (hR : R₀ < R), (C R hR).inside ⊆ A' ∨ (C R hR).inside ⊆ B') :
      ∃ x : ℂ, x ∈ A' ∧ (∀ R (hR : R₀ < R), (C R hR).inside ⊆ A') ∧
        (∀ R (hR : R₀ + 1 ≤ R), x ∈ (C R (by linarith)).inside) := by
    have hside (R : ℝ) (hR : R₀ < R) :=
      lineCap_same_line_side_of_common_normal hAB' hDA (hbranches R hR) (hsame R hR)
    obtain ⟨x, hx⟩ := D.inside_connected.nonempty
    refine ⟨x, hDA hx, hside, ?_⟩
    intro R hR
    let E := C R (by linarith)
    have hsub : D.inside ⊆ E.inside := lineCap_earlier_region_subset D.inside_connected
      D.inside_ball_and_disjoint.1 hR D.inside_ball_and_disjoint.2 (hsame R (by linarith))
      E.inside_open E.outside_open E.disjoint E.cover E.boundary_subset
    exact hsub hx
  rcases hbranch (R₀ + 1) (by linarith) with hDA | hDB
  · exact ⟨A, B, hA, hB, hAc, hBc, hAB, hcover, hfa, hfb,
      hbuild A B hA hB hAc hBc hAB hcover hfa hfb hDA hbranch⟩
  · exact ⟨B, A, hB, hA, hBc, hAc, hAB.symm, by simpa only [union_comm] using hcover,
      hfb, hfa, hbuild B A hB hA hBc hAc hAB.symm (by simpa only [union_comm] using hcover)
        hfb hfa hDB (fun R hR => (hbranch R hR).symm)⟩

/-- The actual-tail worker's endpoint now constructs these cap families from
only finite nonnegative data and positive total half-mass. This is still an
uncompiled dependency chain, not a root-accepted balanced-line theorem. -/
theorem exists_pointConformal_actual_line_cap_family
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hB : 0 < pointExteriorHalfMass a) :
    ∃ c : ℝ → ℂ, Continuous c ∧
      (∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t) ∧
      Tendsto (fun t => c t / (‖c t‖ : ℂ)) atTop (𝓝 (1 : ℂ)) ∧
      Tendsto (fun t => c t / (‖c t‖ : ℂ)) atBot (𝓝 (-1 : ℂ)) ∧
      ∃ R₀ s : ℝ, 0 < R₀ ∧ ‖c s‖ < R₀ ∧ DifferentiableAt ℝ c s ∧ deriv c s ≠ 0 ∧
        Nonempty (∀ R : ℝ, R₀ < R → LineCapGeometry c R) := by
  obtain ⟨c, hc, hd, hpos, hneg, T, hT, htp, htn, _⟩ :=
    exists_pointConformal_complete_line_with_actual_radial_tails ha y hB
  exact ⟨c, hc, hd, hpos, hneg,
    exists_pointMetricLine_actual_cap_family ha y c hd hT htp htn⟩

end RepulsiveCoulomb
