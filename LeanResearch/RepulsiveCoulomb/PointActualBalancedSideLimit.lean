module

public import LeanResearch.RepulsiveCoulomb.PointActualCapAtomicBalance
public import LeanResearch.RepulsiveCoulomb.PointLineCapFixedSideGerms
public import LeanResearch.RepulsiveCoulomb.PointLineCapFamilyExhaustion
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! Uncompiled records-only successor. Exact finite atom stability, actual
mixed GB and actual cap-turn limits now imply balance on a FIXED line side.
The boundary full angles come from a constructed reference cap and are proved
independent of all later caps. No mass or balance certificate is an input. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators Classical
namespace RepulsiveCoulomb

/-- Actual cap geometry plus the line's actual tail signs produces GB data
for every sufficiently large radius. There is no caller join certificate. -/
theorem exists_lineCap_family_GB_threshold
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {R₀ T : ℝ} (C : ∀ R : ℝ, R₀ < R → LineCapGeometry c R)
    (hpos : ∀ t, T < t → 0 < physicalRadialProjection (c t) (deriv c t))
    (hneg : ∀ t, t < -T → physicalRadialProjection (c t) (deriv c t) < 0) :
    ∃ S : ℝ, ∃ hS : R₀ < S, ∀ R (hR : S < R),
      (∀ j, ‖y j‖ < R) ∧
      Nonempty (PointActualCapGBData ha y c (C R (lt_trans hS hR))) := by
  obtain ⟨A, hA, hyA⟩ := lineCap_all_atoms_below_radius y
  let S := max R₀ (max ‖c T‖ (max ‖c (-T)‖ (2 * A))) + 1
  have hRS : R₀ < S := by dsimp [S]; linarith [le_max_left R₀ (max ‖c T‖ (max ‖c (-T)‖ (2 * A)))]
  have hTS : ‖c T‖ < S := by
    dsimp [S]
    linarith [(le_max_left ‖c T‖ (max ‖c (-T)‖ (2 * A))).trans (le_max_right R₀ _)]
  have hnTS : ‖c (-T)‖ < S := by
    dsimp [S]
    linarith [((le_max_left ‖c (-T)‖ (2 * A)).trans (le_max_right ‖c T‖ _)).trans (le_max_right R₀ _)]
  have hAS : 2 * A < S := by
    dsimp [S]
    linarith [((le_max_right ‖c (-T)‖ (2 * A)).trans (le_max_right ‖c T‖ _)).trans (le_max_right R₀ _)]
  refine ⟨S, hRS, ?_⟩
  intro R hR
  let D := C R (hRS.trans hR)
  have hy : ∀ j, 2 * ‖y j‖ ≤ R := by
    intro j
    have hj := hyA A le_rfl j
    linarith
  have hy' : ∀ j, ‖y j‖ < R := by intro j; linarith [hy j, D.radius_pos, norm_nonneg (y j)]
  have hp : T < D.plus := ((D.disk_preimage T).mp (hTS.trans hR)).2
  have hm : D.minus < -T := ((D.disk_preimage (-T)).mp (hnTS.trans hR)).1
  exact ⟨hy', exists_pointActualCapGBData ha y c hd D hy (hneg D.minus hm) (hpos D.plus hp)⟩

/-- The fixed-side balance identity with genuine full physical boundary
intervals. The reference cap and its data are constructed outputs. -/
theorem exists_pointMetricLine_actual_balanced_side
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    (hpositionP : Tendsto (fun t => c t / (‖c t‖ : ℂ)) atTop (𝓝 (1 : ℂ)))
    (hpositionM : Tendsto (fun t => c t / (‖c t‖ : ℂ)) atBot (𝓝 (-1 : ℂ)))
    {T : ℝ} (hT : 0 < T)
    (hpos : ∀ t, T < t → DifferentiableAt ℝ c t ∧ deriv c t ≠ 0 ∧
      0 < physicalRadialProjection (c t) (deriv c t))
    (hneg : ∀ t, t < -T → DifferentiableAt ℝ c t ∧ deriv c t ≠ 0 ∧
      physicalRadialProjection (c t) (deriv c t) < 0)
    (htangentP : Tendsto (fun t => deriv c t / (‖deriv c t‖ : ℂ) - c t / (‖c t‖ : ℂ)) atTop (𝓝 0))
    (htangentM : Tendsto (fun t => (-deriv c t) / (‖deriv c t‖ : ℂ) - c t / (‖c t‖ : ℂ)) atBot (𝓝 0)) :
    ∃ A B : Set ℂ, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = (range c)ᶜ ∧ frontier A = range c ∧ frontier B = range c ∧
      ∃ R : ℝ, ∃ D : LineCapGeometry c R, ∃ H : PointActualCapGBData ha y c D,
        D.inside ⊆ A ∧ (∀ j, ‖y j‖ < R) ∧
        (∑ j, if y j ∈ A then Real.pi * a j else 0) +
          (∑ p ∈ pointLinePositiveAtomLocations a y c,
            ((1 + coalescedPointExponent a y p / 2) * pointActualCapAngleAt H p - Real.pi)) =
          Real.pi * pointExteriorHalfMass a := by
  obtain ⟨R₀, s, hR₀, hsR, hds, hvs, ⟨C⟩⟩ :=
    exists_pointMetricLine_actual_cap_family ha y c hd hT hpos hneg
  obtain ⟨A, B, hA, hB, hAc, hBc, hAB, hcover, hfA, hfB, hside, hexhaust⟩ :=
    pointMetricLine_actual_cap_side_exhaustion ha y c hd hsR hds hvs C
  obtain ⟨S, hS, hGB⟩ := exists_lineCap_family_GB_threshold ha y c hd C
    (fun t ht => (hpos t ht).2.2) (fun t ht => (hneg t ht).2.2)
  let C' : ∀ R : ℝ, S < R → LineCapGeometry c R := fun R hR => C R (hS.trans hR)
  let D : (r : ℝ) → LineCapGeometry c (lineCapLargeRadius S r) := fun r => lineCapFamilyAt C' r
  have hdata (r : ℝ) : Nonempty (PointActualCapGBData ha y c (D r)) :=
    (hGB (lineCapLargeRadius S r) (lineCapLargeRadius_gt S r)).2
  let H : ∀ r : ℝ, PointActualCapGBData ha y c (D r) := fun r => Classical.choice (hdata r)
  have hy (r : ℝ) : ∀ j, ‖y j‖ < lineCapLargeRadius S r :=
    (hGB (lineCapLargeRadius S r) (lineCapLargeRadius_gt S r)).1
  have hboundary (r : ℝ) :
      (∑ p ∈ pointLinePositiveAtomLocations a y c,
        ((1 + coalescedPointExponent a y p / 2) * pointActualCapAngleAt (H r) p - Real.pi)) =
      ∑ p ∈ pointLinePositiveAtomLocations a y c,
        ((1 + coalescedPointExponent a y p / 2) * pointActualCapAngleAt (H 0) p - Real.pi) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [pointActualCapAngleAt_stable ha y c hd (H r) (H 0) (hy r) (hy 0) hp]
  choose Z hZ hmem using fun j : Fin m => hexhaust (y j)
  let M := ∑ j, max (Z j) 0
  have hZM (j : Fin m) : Z j ≤ M := (le_max_left _ _).trans
    (Finset.single_le_sum (fun i _ => le_max_right (Z i) 0) (Finset.mem_univ j))
  have hselector : ∀ᶠ r in atTop, ∀ j, y j ∈ (D r).inside ↔ y j ∈ A := by
    filter_upwards [(lineCapLargeRadius_tendsto S).eventually_gt_atTop M] with r hr j
    exact hmem j (lineCapLargeRadius S r) ((hZM j).trans_lt hr)
  let V := (∑ j, if y j ∈ A then Real.pi * a j else 0) +
    ∑ p ∈ pointLinePositiveAtomLocations a y c,
      ((1 + coalescedPointExponent a y p / 2) * pointActualCapAngleAt (H 0) p - Real.pi)
  have heq : (fun r => pointLineCapTurnDefect a y (D r)) =ᶠ[atTop] (fun _ => V) := by
    filter_upwards [hselector] with r hr
    have hbal := (H r).atomic_cap_balance hd (hy r)
    have hinterior : (∑ j, if y j ∈ (D r).inside then Real.pi * a j else 0) =
        ∑ j, if y j ∈ A then Real.pi * a j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hr j]
    rw [hinterior, hboundary r] at hbal
    exact hbal.symm
  have hlim : Tendsto (fun r => pointLineCapTurnDefect a y (D r)) atTop
      (𝓝 (Real.pi * pointExteriorHalfMass a)) :=
    lineCapFamilyAt_turn_defect_tendsto ha y C' hpositionP hpositionM htangentP htangentM
  have hconst : Tendsto (fun r => pointLineCapTurnDefect a y (D r)) atTop (𝓝 V) :=
    tendsto_const_nhds.congr' heq.symm
  have hV : V = Real.pi * pointExteriorHalfMass a := tendsto_nhds_unique hconst hlim
  exact ⟨A, B, hA, hB, hAc, hBc, hAB, hcover, hfA, hfB,
    lineCapLargeRadius S 0, D 0, H 0,
    hside _ (hS.trans (lineCapLargeRadius_gt S 0)), hy 0, hV⟩

/-- The original positive-mass configuration supplies every analytic and
geometric input. The boundary sum uses actual full cap/fixed-side intervals. -/
theorem exists_pointConformal_actual_balanced_line_side
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hB : 0 < pointExteriorHalfMass a) :
    ∃ c : ℝ → ℂ, Continuous c ∧
      (∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t) ∧
      ∃ A B : Set ℂ, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
        Disjoint A B ∧ A ∪ B = (range c)ᶜ ∧ frontier A = range c ∧ frontier B = range c ∧
        ∃ R : ℝ, ∃ D : LineCapGeometry c R, ∃ H : PointActualCapGBData ha y c D,
          D.inside ⊆ A ∧ (∀ j, ‖y j‖ < R) ∧
          (∑ j, if y j ∈ A then Real.pi * a j else 0) +
            (∑ p ∈ pointLinePositiveAtomLocations a y c,
              ((1 + coalescedPointExponent a y p / 2) * pointActualCapAngleAt H p - Real.pi)) =
            Real.pi * pointExteriorHalfMass a := by
  obtain ⟨c, hc, hd, hp, hm, T, hT, hpos, hneg, htp, htm⟩ :=
    exists_pointConformal_complete_line_with_actual_radial_tails ha y hB
  exact ⟨c, hc, hd, exists_pointMetricLine_actual_balanced_side ha y c hd hp hm hT hpos hneg htp htm⟩

end RepulsiveCoulomb
