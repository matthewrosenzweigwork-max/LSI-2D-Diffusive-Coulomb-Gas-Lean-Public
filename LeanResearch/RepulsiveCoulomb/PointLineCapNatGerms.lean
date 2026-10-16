import LeanResearch.RepulsiveCoulomb.PointLineCapNatFamily
import LeanResearch.RepulsiveCoulomb.PointRadialC1ArcTransport
import LeanResearch.RepulsiveCoulomb.PointRadialC1HalfOpenCorners
import LeanResearch.RepulsiveCoulomb.PointPolyhedralCurvature
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order

/-! Records-only, uncompiled. Preserve the actual original positive-atom
radial germs in the natural-index family. All open edges avoid active atoms,
and every non-circle join is noncuspidal from genuine half-open simplicity.
The two ordinary circle joins are deliberately not assigned a radial endpoint germ. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem lineCap_not_puncture_of_enclosed_atoms
    {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) {R : ℝ}
    (hy : ∀ j, ‖y j‖ < R) {z : ℂ} (hz : R ≤ ‖z‖) : z ∉ pointPunctures a y := by
  rintro ⟨j, _, rfl⟩
  exact (not_lt_of_ge hz) (hy j)

theorem lineCap_exponent_zero_of_enclosed_atoms
    {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) {R : ℝ}
    (hy : ∀ j, ‖y j‖ < R) {z : ℂ} (hz : R ≤ ‖z‖) :
    coalescedPointExponent a y z = 0 := by
  apply coalescedPointExponent_eq_zero_of_not_mem
  intro h
  obtain ⟨j, _, hj⟩ := (mem_positivePointLocations a y z).mp h
  rw [← hj] at hz
  exact (not_lt_of_ge hz) (hy j)

/-- Index transport requires only identities to the original pieces and the
actual joins, all supplied by `exists_pointMetricLine_cap_nat_family`. -/
theorem lineCap_nat_original_germs
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {γ : Icc (0 : ℝ) 1 → ℂ} (hγ : Function.Injective γ)
    (es : List (PointRadialC1ArcPiece ha y γ)) (f : ℕ → ℝ → ℂ)
    (hn : 0 < es.length)
    (hpieces : ∀ k (hk : k < es.length), f k = (es.get ⟨k, hk⟩).curve)
    {R α β : ℝ} (hR : 0 < R) (hy : ∀ j, ‖y j‖ < R)
    (hcircle : f es.length = pointCircleCapArc R α β)
    (hv : ∀ k < es.length, f k 1 = f (k + 1) 0)
    (hclose : f es.length 1 = f 0 0)
    (hinj : ∀ i j, i ≤ es.length → j ≤ es.length → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t) :
    (∀ k ≤ es.length, ∀ t ∈ Ioo (0 : ℝ) 1, f k t ∉ pointPunctures a y) ∧
    (∀ k ≤ es.length, 0 < coalescedPointExponent a y (f k 0) →
      ∃ u v : ℂ, u ≠ 0 ∧ v ≠ 0 ∧
        f k =ᶠ[𝓝 (0 : ℝ)]
          (fun t => (pointChosenSmoothRadialChart ha y (f k 0)).symm (t • v)) ∧
        f (if k = 0 then es.length else k - 1) =ᶠ[𝓝 (1 : ℝ)]
          (fun t => (pointChosenSmoothRadialChart ha y (f k 0)).symm ((1 - t) • u))) ∧
    (∀ k, 0 < k → k < es.length →
      deriv (f k) 0 / deriv (f (k - 1)) 1 ∈ Complex.slitPlane) := by
  have hfirst : coalescedPointExponent a y (f 0 0) = 0 := by
    rw [← hclose, hcircle]
    exact lineCap_exponent_zero_of_enclosed_atoms a y hy
      (by rw [pointCircleCapArc_norm hR.le])
  have hlast : coalescedPointExponent a y (f es.length 0) = 0 := by
    rw [hcircle]
    exact lineCap_exponent_zero_of_enclosed_atoms a y hy
      (by rw [pointCircleCapArc_norm hR.le])
  have hradial (k : ℕ) (hk0 : 0 < k) (hkn : k < es.length) :
      ∃ u v : ℂ, u ≠ 0 ∧ v ≠ 0 ∧
        f k =ᶠ[𝓝 (0 : ℝ)]
          (fun t => (pointChosenSmoothRadialChart ha y (f k 0)).symm (t • v)) ∧
        f (k - 1) =ᶠ[𝓝 (1 : ℝ)]
          (fun t => (pointChosenSmoothRadialChart ha y (f k 0)).symm ((1 - t) • u)) := by
    let e := es.get ⟨k, hkn⟩
    let d := es.get ⟨k - 1, by omega⟩
    have he : f k = e.curve := hpieces k hkn
    have hd : f (k - 1) = d.curve := hpieces (k - 1) (by omega)
    have hjoin : f (k - 1) 1 = f k 0 := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hv (k - 1) (by omega)
    have hleft := e.left_radial
    rw [← e.at_zero, ← he] at hleft
    have hright := d.right_radial
    rw [← d.at_one, ← hd, hjoin] at hright
    exact ⟨d.rightVector, e.leftVector, d.rightVector_ne, e.leftVector_ne, hleft, hright⟩
  refine ⟨?_, ?_, ?_⟩
  · intro k hk t ht
    by_cases hkn : k < es.length
    · rw [hpieces k hkn]
      exact (es.get ⟨k, hkn⟩).curve_no_interior_puncture hγ ht
    · have hkEq : k = es.length := by omega
      rw [hkEq, hcircle]
      exact lineCap_not_puncture_of_enclosed_atoms a y hy
        (by rw [pointCircleCapArc_norm hR.le])
  · intro k hk hκ
    have hk0 : k ≠ 0 := by intro he; rw [he, hfirst] at hκ; exact lt_irrefl _ hκ
    have hkn : k ≠ es.length := by intro he; rw [he, hlast] at hκ; exact lt_irrefl _ hκ
    simpa only [if_neg hk0] using hradial k (by omega) (by omega)
  · intro k hk0 hkn
    let e := es.get ⟨k, hkn⟩
    let d := es.get ⟨k - 1, by omega⟩
    have he : f k = e.curve := hpieces k hkn
    have hd : f (k - 1) = d.curve := hpieces (k - 1) (by omega)
    have hjoin : d.curve 1 = e.curve 0 := by
      rw [← hd, ← he]
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hv (k - 1) (by omega)
    have hdisj : Disjoint (d.curve '' Ico (0 : ℝ) 1) (e.curve '' Ico (0 : ℝ) 1) := by
      apply disjoint_left.mpr
      rintro z ⟨s, hs, hsz⟩ ⟨t, ht, htz⟩
      have hsame : f (k - 1) s = f k t := by rw [hd, he]; exact hsz.trans htz.symm
      have hindices := (hinj (k - 1) k (by omega) hkn.le s t hs ht hsame).1
      omega
    rw [he, hd]
    exact d.toPlane.corner_ratio_mem_slitPlane e.toPlane hjoin hdisj

end RepulsiveCoulomb
