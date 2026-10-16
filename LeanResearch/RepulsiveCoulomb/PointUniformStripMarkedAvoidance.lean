module

public import LeanResearch.RepulsiveCoulomb.ShearedRectangleGeometry
public import LeanResearch.RepulsiveCoulomb.FullNormalStripSourceGeometry

@[expose] public section

/-! NEW proofs for the retained marked-avoidance interfaces. The original
uniform geometric clearance and actual transverse distances exclude marks
on the entire closed source, including its completed top boundary. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem pointShearedStrip_avoids_marked
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P S : Set ℂ}
    {v : ℂ} (hv : ‖v‖ = 1) {delta : ℝ} (hdelta : 0 ≤ delta)
    (rho : NNReal → ℂ)
    (hclear : ∀ p ∈ S \ {rho 0}, ∀ r : NNReal,
      delta < (pointSmoothConformalEDist a y p (rho r)).toReal)
    (F : flatShearedStrip v delta → P)
    (hF : ∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z)
    (hbottom : ∀ r : NNReal, ∀ hr : (r : ℂ) ∈ flatShearedStrip v delta,
      (F ⟨(r : ℂ), hr⟩).1 = rho r) :
    ∀ z, (F z).1 ∉ S \ {rho 0} := by
  intro z hmarked
  obtain ⟨r, hr, u, hu, he⟩ := z.2
  let q : NNReal := ⟨r, hr⟩
  have hb : (q : ℂ) ∈ flatShearedStrip v delta :=
    ⟨r, hr, 0, ⟨le_rfl, hdelta⟩, (flatShearedPoint_zero v r).symm⟩
  have htrans : dist z (⟨(q : ℂ), hb⟩ : flatShearedStrip v delta) = u := by
    change dist z.1 (r : ℂ) = u
    rw [he, ← flatShearedPoint_zero v r]
    exact flatShearedPoint_dist_bottom hv r hu.1
  have hd := hF z ⟨(q : ℂ), hb⟩
  rw [hbottom q hb] at hd
  have hle : (pointSmoothConformalEDist a y (F z).1 (rho q)).toReal ≤ delta :=
    (hd.trans htrans).le.trans hu.2
  exact (not_lt_of_ge hle) (hclear (F z).1 hmarked q)

theorem pointFullNormalStrip_avoids_marked
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P S : Set ℂ}
    {delta : ℝ} (hdelta : 0 ≤ delta) (line : ℝ → ℂ)
    (hclear : ∀ p ∈ S, ∀ r : ℝ,
      delta < (pointSmoothConformalEDist a y p (line r)).toReal)
    (F : flatFullNormalStrip delta → P)
    (hF : ∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z)
    (hbottom : ∀ r : ℝ, ∀ hr : (r : ℂ) ∈ flatFullNormalStrip delta,
      (F ⟨(r : ℂ), hr⟩).1 = line r) :
    ∀ z, (F z).1 ∉ S := by
  intro z hmarked
  have hb : (z.1.re : ℂ) ∈ flatFullNormalStrip delta := by
    change (z.1.re : ℂ).im ∈ Icc (0 : ℝ) delta
    simpa only [Complex.ofReal_im, Set.mem_Icc] using And.intro (le_refl (0 : ℝ)) hdelta
  have htrans : dist z (⟨(z.1.re : ℂ), hb⟩ : flatFullNormalStrip delta) = z.1.im := by
    change dist z.1 (z.1.re : ℂ) = z.1.im
    rw [Complex.dist_of_re_eq (by simp), Real.dist_eq, Complex.ofReal_im, sub_zero,
      abs_of_nonneg z.2.1]
  have hd := hF z ⟨(z.1.re : ℂ), hb⟩
  rw [hbottom z.1.re hb] at hd
  have hle : (pointSmoothConformalEDist a y (F z).1 (line z.1.re)).toReal ≤ delta :=
    (hd.trans htrans).le.trans z.2.2
  exact (not_lt_of_ge hle) (hclear (F z).1 hmarked z.1.re)

end RepulsiveCoulomb
