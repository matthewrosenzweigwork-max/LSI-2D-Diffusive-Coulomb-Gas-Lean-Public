module

public import LeanResearch.RepulsiveCoulomb.PointInteriorZeroExponentFlatChart
public import LeanResearch.RepulsiveCoulomb.ComplexBoundarySideRigidity
public import LeanResearch.RepulsiveCoulomb.FullNormalStripSourceGeometry

@[expose] public section

/-! NEW post-loss full-line stage geometry. Return exclusion is derived from
two actual bottom distances; interior membership and zero exponent then follow
from the actual whole frontier and the supplied geometric marked clearance. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem pointFlatStage_no_full_line_return
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P K : Set ℂ}
    (line : ℝ → ℂ)
    (hline : ∀ r t, (pointSmoothConformalEDist a y (line r) (line t)).toReal = dist r t)
    (F : K → P)
    (hF : ∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z)
    {s t : ℝ} (hst : s ≠ t) (hs : (s : ℂ) ∈ K) (ht : (t : ℂ) ∈ K)
    (hFs : (F ⟨(s : ℂ), hs⟩).1 = line s)
    (hFt : (F ⟨(t : ℂ), ht⟩).1 = line t)
    (z : K) (hz : 0 < z.1.im) : (F z).1 ∉ range line := by
  rintro ⟨q, hq⟩
  have hreal (r : ℝ) : dist (q : ℂ) (r : ℂ) = dist q r := by
    simp only [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, Real.dist_eq]
  have hsDist : dist z.1 (s : ℂ) = dist (q : ℂ) (s : ℂ) := by
    have h := hF z ⟨(s : ℂ), hs⟩
    rw [hFs, ← hq, hline] at h
    change dist q s = dist z.1 (s : ℂ) at h
    exact h.symm.trans (hreal s).symm
  have htDist : dist z.1 (t : ℂ) = dist (q : ℂ) (t : ℂ) := by
    have h := hF z ⟨(t : ℂ), ht⟩
    rw [hFt, ← hq, hline] at h
    change dist q t = dist z.1 (t : ℂ) at h
    exact h.symm.trans (hreal t).symm
  rcases complex_eq_or_conj_of_two_real_dist_eq hst hsDist htDist with he | he
  · have him : z.1.im = 0 := by simpa only [Complex.ofReal_im] using congrArg Complex.im he
    linarith
  · have him : z.1.im = 0 := by
      simpa only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_im] using congrArg Complex.im he
    linarith

theorem pointFullLine_normalStage_flatChart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P S : Set ℂ} (line : ℝ → ℂ)
    (hline : ∀ r t, (pointSmoothConformalEDist a y (line r) (line t)).toReal = dist r t)
    (hboundary : frontier P = range line)
    (hmarks : ∀ p ∈ interior P, coalescedPointExponent a y p ≠ 0 → p ∈ S)
    {R s delta c : ℝ} (hR : 0 < R) (hs : 0 ≤ s) (hsdelta : s ≤ delta)
    (hclear : ∀ p ∈ S, ∀ r : ℝ, delta < (pointSmoothConformalEDist a y p (line r)).toReal)
    (F : flatShearedRectangle Complex.I R s → P)
    (hF : ∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z)
    (hbottom : ∀ r : Icc (0 : ℝ) R,
      (F (normalRectangleBottom r.2 hs)).1 = line (c + r.1)) :
    ∀ z, 0 < z.1.im →
      Nonempty (@MetricFlatDiskChart P (pointRegionMetricSpace ha y P) (F z)) := by
  have hshift : ∀ r t,
      (pointSmoothConformalEDist a y (line (c + r)) (line (c + t))).toReal = dist r t := by
    intro r t
    rw [hline]
    change |(c + r) - (c + t)| = |r - t|
    congr 1
    ring
  have h0 : (0 : ℂ) ∈ flatShearedRectangle Complex.I R s :=
    (normalRectangleBottom (R := R) (s := s) (r := 0) ⟨le_rfl, hR.le⟩ hs).2
  have hRR : (R : ℂ) ∈ flatShearedRectangle Complex.I R s :=
    (normalRectangleBottom (R := R) (s := s) (r := R) ⟨hR.le, le_rfl⟩ hs).2
  have hF0 : (F ⟨0, h0⟩).1 = line (c + 0) := hbottom ⟨0, le_rfl, hR.le⟩
  have hFR : (F ⟨(R : ℂ), hRR⟩).1 = line (c + R) := hbottom ⟨R, hR.le, le_rfl⟩
  intro z hz
  have hnoshift := pointFlatStage_no_full_line_return (fun r ↦ line (c + r)) hshift
    F hF (ne_of_lt hR) h0 hRR hF0 hFR z hz
  have hnoline : (F z).1 ∉ range line := by
    rintro ⟨q, hq⟩
    apply hnoshift
    refine ⟨q - c, ?_⟩
    change line (c + (q - c)) = (F z).1
    rw [show c + (q - c) = q by ring]
    exact hq
  have hinterior : (F z).1 ∈ interior P := by
    by_contra hn
    have hfront : (F z).1 ∈ frontier P := ⟨subset_closure (F z).2, hn⟩
    exact hnoline (hboundary ▸ hfront)
  have hcoords := mem_flatShearedRectangle_I_iff.mp z.2
  have hfoot := hbottom (⟨z.1.re, hcoords.1⟩ : Icc (0 : ℝ) R)
  have htrans : dist z (normalRectangleBottom hcoords.1 hs) = z.1.im := by
    change dist z.1 (z.1.re : ℂ) = z.1.im
    rw [Complex.dist_of_re_eq (by simp), Real.dist_eq, Complex.ofReal_im, sub_zero,
      abs_of_nonneg hcoords.2.1]
  have hd := hF z (normalRectangleBottom hcoords.1 hs)
  rw [hfoot] at hd
  have hdistle : (pointSmoothConformalEDist a y (F z).1 (line (c + z.1.re))).toReal ≤ delta :=
    (hd.trans htrans).le.trans (hcoords.2.2.trans hsdelta)
  have hnotmarked : (F z).1 ∉ S := by
    intro hmarked
    exact (not_lt_of_ge hdistle) (hclear (F z).1 hmarked (c + z.1.re))
  have hzero : coalescedPointExponent a y (F z).1 = 0 := by
    by_contra hn
    exact hnotmarked (hmarks (F z).1 hinterior hn)
  exact exists_pointInterior_zeroExponent_flatDiskChart ha y hinterior hzero

end RepulsiveCoulomb
