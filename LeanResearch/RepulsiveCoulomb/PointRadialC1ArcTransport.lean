import LeanResearch.RepulsiveCoulomb.PointGeodesicArgumentTurn
import LeanResearch.RepulsiveCoulomb.PointRadialC1ArcChain

/-! Install the proved source-clock and weighted argument transport on the
actual puncture-gap macro-arcs constructed from the original geodesic. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb
namespace PointRadialC1ArcPiece

variable {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
  {γ : Icc (0 : ℝ) 1 → ℂ}

theorem interior_image (e : PointRadialC1ArcPiece ha y γ) (hγ : Function.Injective γ) :
    e.curve '' Ioo (0 : ℝ) 1 = γ '' Ioo e.start e.finish := by
  apply Subset.antisymm
  · rintro z ⟨u, hu, rfl⟩
    have hmem : e.curve u ∈ e.curve '' Icc (0 : ℝ) 1 := ⟨u, ⟨hu.1.le, hu.2.le⟩, rfl⟩
    rw [e.image] at hmem
    obtain ⟨v, hv, hvu⟩ := hmem
    have hvs : v ≠ e.start := by
      intro he
      have hu0 := e.injective ⟨hu.1.le, hu.2.le⟩ (by norm_num)
        (hvu.symm.trans ((congrArg γ he).trans e.at_zero.symm))
      exact hu.1.ne' hu0
    have hvf : v ≠ e.finish := by
      intro he
      have hu1 := e.injective ⟨hu.1.le, hu.2.le⟩ (by norm_num)
        (hvu.symm.trans ((congrArg γ he).trans e.at_one.symm))
      exact hu.2.ne hu1
    exact ⟨v, ⟨lt_of_le_of_ne hv.1 (Ne.symm hvs), lt_of_le_of_ne hv.2 hvf⟩, hvu⟩
  · rintro z ⟨v, hv, rfl⟩
    have hmem : γ v ∈ e.curve '' Icc (0 : ℝ) 1 := by
      rw [e.image]
      exact ⟨v, ⟨hv.1.le, hv.2.le⟩, rfl⟩
    obtain ⟨u, hu, huv⟩ := hmem
    have hu0 : u ≠ 0 := by
      intro he
      rw [he, e.at_zero] at huv
      exact hv.1.ne (hγ huv)
    have hu1 : u ≠ 1 := by
      intro he
      rw [he, e.at_one] at huv
      exact hv.2.ne (hγ huv).symm
    exact ⟨u, ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_ne hu.2 hu1⟩, huv⟩


theorem curve_no_interior_puncture (e : PointRadialC1ArcPiece ha y γ)
    (hγ : Function.Injective γ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    e.curve u ∉ pointPunctures a y := by
  have hmem : e.curve u ∈ e.curve '' Ioo (0 : ℝ) 1 := ⟨u, hu, rfl⟩
  rw [e.interior_image hγ] at hmem
  obtain ⟨v, hv, heq⟩ := hmem
  rw [← heq]
  exact e.no_interior_puncture v hv

/-- The actual constructed macro-piece has a full smooth-edge turn/argument
identity, including endpoint limits at its possible boundary punctures. -/
theorem exists_argument_turn (e : PointRadialC1ArcPiece ha y γ)
    {p q : ℂ} (hpq : p ≠ q) (h0 : γ ⟨0, by norm_num⟩ = p)
    (hd : ∀ v w, (pointSmoothConformalEDist a y (γ v) (γ w)).toReal =
      |w.1 - v.1| * (pointSmoothConformalEDist a y p q).toReal) :
    ∃ θ : Icc (0 : ℝ) 1 → ℝ, ∃ ψ : Fin m → Icc (0 : ℝ) 1 → ℝ,
      Continuous θ ∧ (∀ j, Continuous (ψ j)) ∧
      (∀ u, Complex.exp ((θ u : ℂ) * Complex.I) =
        deriv e.curve u / (‖deriv e.curve u‖ : ℂ)) ∧
      (∀ j, a j ≠ 0 → ∀ u : Icc (0 : ℝ) 1, u.1 ∈ Ioo (0 : ℝ) 1 →
        Complex.exp ((ψ j u : ℂ) * Complex.I) =
          (e.curve u - y j) / (‖e.curve u - y j‖ : ℂ)) ∧
      θ 1 - θ 0 = -(∑ j, (a j / 2) * (ψ j 1 - ψ j 0)) := by
  exact exists_pointConformal_equal_image_argument_turn ha y hpq γ h0 hd
    e.start e.finish e.increasing e.smooth e.injective e.regular e.at_zero e.at_one e.image
    (fun u hu => e.curve_no_interior_puncture
      (pointConformal_geodesic_injective ha y hpq γ hd) hu)

end PointRadialC1ArcPiece
end RepulsiveCoulomb
