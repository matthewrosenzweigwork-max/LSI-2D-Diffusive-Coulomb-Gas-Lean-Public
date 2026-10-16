module

public import LeanResearch.RepulsiveCoulomb.PointRadialC1ChainHalfOpen
public import Mathlib.Analysis.Calculus.Deriv.Shift

@[expose] public section

/-! Oriented C1 plane macro-arcs retaining the same physical-vertex chart
at each endpoint. Reversal swaps the two actual outward radial vectors. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

structure PointRadialC1PlaneArc {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) where
  curve : ℝ → ℂ
  smooth : ContDiff ℝ 1 curve
  injective : InjOn curve (Icc (0 : ℝ) 1)
  regular : ∀ u ∈ Icc (0 : ℝ) 1, deriv curve u ≠ 0
  leftVector : ℂ
  rightVector : ℂ
  leftVector_ne : leftVector ≠ 0
  rightVector_ne : rightVector ≠ 0
  left_radial : curve =ᶠ[𝓝 (0 : ℝ)] (fun u : ℝ =>
    (pointChosenSmoothRadialChart ha y (curve 0)).symm (u • leftVector))
  right_radial : curve =ᶠ[𝓝 (1 : ℝ)] (fun u : ℝ =>
    (pointChosenSmoothRadialChart ha y (curve 1)).symm ((1 - u) • rightVector))

def PointRadialC1PlaneArc.start {m : ℕ} {a : Fin m → ℝ}
    {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ} (e : PointRadialC1PlaneArc ha y) : ℂ := e.curve 0

def PointRadialC1PlaneArc.finish {m : ℕ} {a : Fin m → ℝ}
    {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ} (e : PointRadialC1PlaneArc ha y) : ℂ := e.curve 1

def PointRadialC1ArcPiece.toPlane {m : ℕ} {a : Fin m → ℝ}
    {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ} {γ : Icc (0 : ℝ) 1 → ℂ}
    (e : PointRadialC1ArcPiece ha y γ) : PointRadialC1PlaneArc ha y where
  curve := e.curve
  smooth := e.smooth
  injective := e.injective
  regular := e.regular
  leftVector := e.leftVector
  rightVector := e.rightVector
  leftVector_ne := e.leftVector_ne
  rightVector_ne := e.rightVector_ne
  left_radial := by simpa only [e.at_zero] using e.left_radial
  right_radial := by simpa only [e.at_one] using e.right_radial

def PointRadialC1PlaneArc.reverse {m : ℕ} {a : Fin m → ℝ}
    {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    (e : PointRadialC1PlaneArc ha y) : PointRadialC1PlaneArc ha y where
  curve := fun t => e.curve (1 - t)
  smooth := e.smooth.comp (contDiff_const.sub contDiff_id)
  injective := by
    intro s hs t ht he
    have h := e.injective
      (show 1 - s ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hs.1, hs.2])
      (show 1 - t ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [ht.1, ht.2]) he
    linarith
  regular := by
    intro t ht
    rw [deriv_comp_const_sub]
    exact neg_ne_zero.mpr (e.regular _ (by constructor <;> linarith [ht.1, ht.2]))
  leftVector := e.rightVector
  rightVector := e.leftVector
  leftVector_ne := e.rightVector_ne
  rightVector_ne := e.leftVector_ne
  left_radial := by
    have ht : Tendsto (fun t : ℝ => 1 - t) (𝓝 0) (𝓝 1) := by
      have h : Continuous (fun t : ℝ => 1 - t) := by fun_prop
      simpa only [sub_zero] using h.tendsto 0
    simpa only [Function.comp_def, sub_sub_cancel, sub_zero] using e.right_radial.comp_tendsto ht
  right_radial := by
    have ht : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 0) := by
      have h : Continuous (fun t : ℝ => 1 - t) := by fun_prop
      simpa only [sub_self] using h.tendsto 1
    simpa only [Function.comp_def, sub_self] using e.left_radial.comp_tendsto ht

namespace PointRadialC1PlaneArc
variable {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}

@[simp] theorem reverse_start (e : PointRadialC1PlaneArc ha y) : e.reverse.start = e.finish := by
  simp only [reverse, start, finish, sub_zero]

@[simp] theorem reverse_finish (e : PointRadialC1PlaneArc ha y) : e.reverse.finish = e.start := by
  simp only [reverse, start, finish, sub_self]

theorem reverse_image (e : PointRadialC1PlaneArc ha y) :
    e.reverse.curve '' Icc (0 : ℝ) 1 = e.curve '' Icc (0 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨t, ht, htz⟩
    exact ⟨1 - t, by constructor <;> linarith [ht.1, ht.2], htz⟩
  · rintro ⟨t, ht, htz⟩
    refine ⟨1 - t, by constructor <;> linarith [ht.1, ht.2], ?_⟩
    simpa only [reverse, sub_sub_cancel] using htz

theorem reverse_halfOpen_image (e : PointRadialC1PlaneArc ha y) :
    e.reverse.curve '' Ico (0 : ℝ) 1 = e.curve '' Ioc (0 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨t, ht, htz⟩
    exact ⟨1 - t, by constructor <;> linarith [ht.1, ht.2], htz⟩
  · rintro ⟨t, ht, htz⟩
    refine ⟨1 - t, by constructor <;> linarith [ht.1, ht.2], ?_⟩
    simpa only [reverse, sub_sub_cancel] using htz

end PointRadialC1PlaneArc
end RepulsiveCoulomb
