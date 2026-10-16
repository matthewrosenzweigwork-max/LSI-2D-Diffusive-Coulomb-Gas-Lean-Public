module

public import LeanResearch.RepulsiveCoulomb.PointLineCapFixedSideGerms
public import LeanResearch.RepulsiveCoulomb.PointChosenRadialMetricTransition
public import LeanResearch.RepulsiveCoulomb.PointGeodesicTriangleCorner
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Uncompiled records-only successor. The actual two full fixed-side widths
are at least pi. Equal-radius points on their two actual boundary rays lie on
the original metric line; its exact distance forces the through-apex cone
route, and both directed full-angle inequalities follow. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem real_dist_eq_twice_of_equal_dist {s t u R : ℝ}
    (hst : s ≠ t) (hs : dist s u = R) (ht : dist t u = R) : dist s t = 2 * R := by
  rw [Real.dist_eq] at hs ht ⊢
  have he : |s - u| = |t - u| := hs.trans ht.symm
  rcases abs_eq_abs.mp he with he | he
  · exact False.elim (hst (by linarith))
  · have hst' : s - t = 2 * (s - u) := by linarith
    rw [hst', abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), hs]

theorem complementary_region_closed_intersection {A B L : Set ℂ}
    (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hfA : frontier A = L) (hfB : frontier B = L) : closure A ∩ closure B = L := by
  ext z
  constructor
  · rintro ⟨hzA, hzB⟩
    have hznotA : z ∉ A := fun h => disjoint_left.mp (hAB.closure_right hA) h hzB
    rw [closure_eq_self_union_frontier, hfA] at hzA
    exact hzA.resolve_left hznotA
  · intro hz
    exact ⟨frontier_subset_closure (hfA.symm ▸ hz), frontier_subset_closure (hfB.symm ▸ hz)⟩

/-- Full directed side bounds from actual interval membership and an explicit
radial transition to the actual cone metric. No angle-bound certificate is input. -/
theorem pointMetricLine_full_physical_side_widths_ge_pi
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {A B : Set ℂ} (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hfA : frontier A = range c) (hfB : frontier B = range c)
    {p : ℂ} (hpLine : p ∈ range c) (E F : OpenPartialHomeomorph ℂ ℂ)
    {δ r θ : ℝ} (hr : 0 < r) (hrδ : r ≤ δ) (hθ : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (hside : ∀ z ∈ ball (0 : ℂ) r,
      (E.symm z ∈ closure A ↔ z ∈ lineClosedInitialSector δ θ) ∧
      (E.symm z ∈ closure B ↔ z ∈ lineClosedTerminalSector δ θ))
    (hpF : p ∈ F.source) (hF0 : F p = 0) (hFsrc : F.source ⊆ E.source)
    (hF : ∀ z, F z = coneRadialEquiv (coalescedPointExponent a y p / 2)
      (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)) (E z))
    (hmetric : ∀ u ∈ F.source, ∀ v ∈ F.source,
      (pointSmoothConformalEDist a y u v).toReal = pointClassicalConeDist a y p (F u) (F v)) :
    Real.pi ≤ (1 + coalescedPointExponent a y p / 2) * θ ∧
      Real.pi ≤ (1 + coalescedPointExponent a y p / 2) * (2 * Real.pi - θ) := by
  let α := coalescedPointExponent a y p / 2
  have hα : 0 ≤ α := div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)
  have hpE := hFsrc hpF
  have hE0 : E p = 0 := by
    apply (coneRadialEquiv α hα).injective
    rw [← hF, hF0, coneRadialEquiv_zero]
  have h0E : (0 : ℂ) ∈ E.target := hE0 ▸ E.mapsTo hpE
  have hinv : E.symm 0 = p := by rw [← hE0, E.left_inv hpE]
  have htarget : E.target ∩ E.symm ⁻¹' F.source ∈ 𝓝 (0 : ℂ) := by
    apply inter_mem (E.open_target.mem_nhds h0E)
    apply (E.symm.continuousAt h0E).preimage_mem_nhds
    rw [hinv]
    exact F.open_source.mem_nhds hpF
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp htarget
  let σ := min ε r / 2
  have hσ : 0 < σ := half_pos (lt_min hε hr)
  have hσε : σ < ε := by dsimp [σ]; linarith [min_le_left ε r, lt_min hε hr]
  have hσr : σ < r := by dsimp [σ]; linarith [min_le_right ε r, lt_min hε hr]
  have hσδ : σ < δ := hσr.trans_le hrδ
  let u := pointRadialSectorPoint σ 0
  let v := pointRadialSectorPoint σ θ
  let x := E.symm u
  let z := E.symm v
  have huε : u ∈ ball (0 : ℂ) ε := by
    rw [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hσ.le]; exact hσε
  have hvε : v ∈ ball (0 : ℂ) ε := by
    rw [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hσ.le]; exact hσε
  have hur : u ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hσ.le]; exact hσr
  have hvr : v ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hσ.le]; exact hσr
  have hxt : u ∈ E.target := (hεsub huε).1
  have hzt : v ∈ E.target := (hεsub hvε).1
  have hxF : x ∈ F.source := (hεsub huε).2
  have hzF : z ∈ F.source := (hεsub hvε).2
  have hxLine : x ∈ range c := by
    rw [← complementary_region_closed_intersection hA hB hAB hfA hfB]
    exact ⟨(hside u hur).1.mpr (Or.inl (Or.inl ⟨σ, ⟨hσ.le, hσδ⟩, rfl⟩)),
      (hside u hur).2.mpr (Or.inl (Or.inl ⟨σ, ⟨hσ.le, hσδ⟩, rfl⟩))⟩
  have hzLine : z ∈ range c := by
    rw [← complementary_region_closed_intersection hA hB hAB hfA hfB]
    exact ⟨(hside v hvr).1.mpr (Or.inl (Or.inr ⟨σ, ⟨hσ.le, hσδ⟩, rfl⟩)),
      (hside v hvr).2.mpr (Or.inl (Or.inr ⟨σ, ⟨hσ.le, hσδ⟩, rfl⟩))⟩
  let q := σ ^ (α + 1) / (α + 1)
  have hq : 0 < q := div_pos (Real.rpow_pos_of_pos hσ _) (by linarith)
  have hximage : F x = pointRadialSectorPoint q 0 := by
    rw [hF, E.right_inv hxt]
    exact coneRadialEquiv_polar_exact hα hσ 0
  have hzimage : F z = pointRadialSectorPoint q θ := by
    rw [hF, E.right_inv hzt]
    exact coneRadialEquiv_polar_exact hα hσ θ
  have hxnorm : ‖F x‖ = q := by rw [hximage]; exact pointRadialSectorPoint_norm hq.le 0
  have hznorm : ‖F z‖ = q := by rw [hzimage]; exact pointRadialSectorPoint_norm hq.le θ
  have hneq : x ≠ z := by
    intro he
    have huv : u = v := by simpa only [x, z, E.right_inv hxt, E.right_inv hzt] using congrArg E he
    have heθ := (pointRadialSectorPoint_angle_injective hσ hσ.le
      (show (0 : ℝ) ∈ Ico 0 (2 * Real.pi) from ⟨le_rfl, by positivity⟩) ⟨hθ.le, hθ2⟩ huv).2
    linarith
  obtain ⟨t, ht⟩ := hpLine
  obtain ⟨s, hs⟩ := hxLine
  obtain ⟨w, hw⟩ := hzLine
  have hxp : (pointSmoothConformalEDist a y x p).toReal = q := by
    rw [hmetric x hxF p hpF, hF0, pointClassicalConeDist_apex, hxnorm]
  have hzp : (pointSmoothConformalEDist a y z p).toReal = q := by
    rw [hmetric z hzF p hpF, hF0, pointClassicalConeDist_apex, hznorm]
  have hsR : dist s t = q := by rw [← hd, hs, ht]; exact hxp
  have hwR : dist w t = q := by rw [← hd, hw, ht]; exact hzp
  have hsw : s ≠ w := by intro he; exact hneq (hs.symm.trans ((congrArg c he).trans hw))
  have hcone : pointClassicalConeDist a y p (F x) (F z) = ‖F x‖ + ‖F z‖ := by
    rw [← hmetric x hxF z hzF, hxnorm, hznorm, ← hs, ← hw, hd,
      real_dist_eq_twice_of_equal_dist hsw hsR hwR]
    ring
  have hturn := cone_equal_radius_minimizing_turns_nonpos hα
    (norm_ne_zero_iff.mp (hxnorm.trans_ne hq.ne'))
    (norm_ne_zero_iff.mp (hznorm.trans_ne hq.ne')) (hxnorm.trans hznorm.symm) hcone
  have hratio : F z / F x = (Circle.exp θ : ℂ) := by
    rw [hximage, hzimage, pointRadialSectorPoint_angle_zero]
    simp only [pointRadialSectorPoint]
    exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hq.ne')
  have hfull := cone_directed_sector_angles_eq_short_long hθ hθ2 hratio (α := α)
  rcases hfull with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · constructor <;> dsimp [α] at * <;> linarith [hturn.1, hturn.2]
  · constructor <;> dsimp [α] at * <;> linarith [hturn.1, hturn.2]

end RepulsiveCoulomb
