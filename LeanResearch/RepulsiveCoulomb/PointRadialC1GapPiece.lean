import LeanResearch.RepulsiveCoulomb.PointRadialC1ArcChain

/-! Package the actually constructed gap macro-arc while retaining its
literal chosen-chart vectors, their nonzeroness, and its source interval. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_pointRadialC1ArcPiece_of_puncture_gap {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p q : ℂ} (hpq : p ≠ q)
    (γ : Icc (0 : ℝ) 1 → ℂ)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y p q).toReal)
    (s t : Icc (0 : ℝ) 1) (hst : s < t)
    (hgap : ∀ u ∈ Ioo s t, γ u ∉ pointPunctures a y) :
    ∃ e : PointRadialC1ArcPiece ha y γ, e.start = s ∧ e.finish = t := by
  obtain ⟨l, r, _, _, _, η, hη, hηi, hηr, hη0, hη1, hηimage, hηL, hηR⟩ :=
    exists_pointConformal_chosen_radial_C1_gap ha y hpq γ hd s t hst hgap
  let u := (3 : ℝ) • (pointChosenSmoothRadialChart ha y (γ s)) (γ l)
  let v := (3 : ℝ) • (pointChosenSmoothRadialChart ha y (γ t)) (γ r)
  have hL : η =ᶠ[𝓝 (0 : ℝ)] (fun x : ℝ =>
      (pointChosenSmoothRadialChart ha y (γ s)).symm (x • u)) := by
    filter_upwards [hηL] with x hx
    rw [hx]
    congr 1
    dsimp [u]
    push_cast
    ring
  have hR : η =ᶠ[𝓝 (1 : ℝ)] (fun x : ℝ =>
      (pointChosenSmoothRadialChart ha y (γ t)).symm ((1 - x) • v)) := by
    filter_upwards [hηR] with x hx
    rw [hx]
    congr 1
    dsimp [v]
    push_cast
    ring
  have hu : u ≠ 0 := by
    intro he
    have hzero : deriv η 0 = 0 := by
      simpa only [he, smul_zero, deriv_const] using hL.deriv_eq
    exact hηr 0 (by norm_num) hzero
  have hv : v ≠ 0 := by
    intro he
    have hzero : deriv η 1 = 0 := by
      simpa only [he, smul_zero, deriv_const] using hR.deriv_eq
    exact hηr 1 (by norm_num) hzero
  exact ⟨⟨s, t, hst, η, hη, hηi, hηr, hη0, hη1, hηimage,
    u, v, hu, hv, hL, hR, hgap⟩, rfl, rfl⟩

end RepulsiveCoulomb
