module

public import LeanResearch.RepulsiveCoulomb.JordanFiniteCornerPositiveBoundaryAtom
public import LeanResearch.RepulsiveCoulomb.PointPositiveLoopFullSide
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Uncompiled records-only successor. Preserve the actual full side sets of
an original finite family rather than discarding them after point-flux accounting. -/
noncomputable section
open Set Metric Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem exists_finite_corner_positive_full_radial_side
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hdisj : Disjoint U V)
    (hK : IsCompact (closure U))
    (hcover : U ∪ V = (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)ᶜ)
    (hpU : f 0 0 ∈ closure U) (hpV : f 0 0 ∈ closure V)
    {w : ℂ} (hw : w ∈ U)
    (ξ : ℕ → Icc (0 : ℝ) 1 → ℝ) (hξ : ∀ k ≤ n, Continuous (ξ k))
    (hξlift : ∀ k ≤ n, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ξ k t : ℂ) * Complex.I) = (f k t - w) / (‖f k t - w‖ : ℂ))
    (hξturn : (∑ k ∈ Finset.range (n + 1), (ξ k 1 - ξ k 0)) = 2 * Real.pi)
    (e : OpenPartialHomeomorph ℂ ℂ) (hp : f 0 0 ∈ e.source) (hep : e (f 0 0) = 0)
    (he : ∀ z ∈ e.source, AnalyticAt ℂ e z)
    (hinv : AnalyticOnNhd ℂ e.symm e.target) (hinvn : deriv e.symm 0 ≠ 0)
    {δ cL cR R θ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hcL : 0 < cL) (hcR : 0 < cR) (hR : 0 < R)
    (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (hball : ball (0 : ℂ) R ⊆ e.target)
    (hLrad : cL * δ < R) (hRrad : cR * δ < R)
    (hleft : ∀ s ∈ Icc (0 : ℝ) 1, s ≤ δ →
      f 0 s = e.symm (pointRadialSectorPoint (cL * s) 0))
    (hright : ∀ s ∈ Icc (0 : ℝ) 1, 1 - δ ≤ s →
      f n s = e.symm (pointRadialSectorPoint (cR * (1 - s)) θ))
    : ∃ δ' : ℝ, 0 < δ' ∧ ball (0 : ℂ) δ' ⊆ e.target ∧
      (∀ z ∈ ball (0 : ℂ) δ',
        e.symm z ∈ (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1) ↔
          z ∈ pointDiskRay δ' 0 ∪ pointDiskRay δ' θ) ∧
      MapsTo e.symm (pointOpenRadialSector δ' 0 θ) U ∧
      MapsTo e.symm (pointOpenRadialSector δ' θ (2 * Real.pi)) V := by
  let P := pointContinuousPeriodize (euclideanFiniteCornerArc f n)
  obtain ⟨hP, hpP, hiP, hP0, himage⟩ := euclideanFiniteCornerPeriodize_properties f n hf hv hclose hinj
  change P '' Icc (0 : ℝ) 1 = (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1) at himage
  have hbase : P 0 = f 0 0 := hP0
  have hcoverP : U ∪ V = (P '' Icc (0 : ℝ) 1)ᶜ := by rwa [himage]
  have hwC : w ∉ ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 := by
    have hwUV : w ∈ U ∪ V := Or.inl hw
    rw [hcover] at hwUV
    exact hwUV
  obtain ⟨Ξ, hΞ, hΞlift, hΞturn⟩ := exists_finite_corner_positive_periodic_point_argument
    f n hf hv hclose hwC ξ hξ hξlift hξturn
  obtain ⟨hl, hlr, hr, hcL', hcR', hleft', hright'⟩ :=
    euclideanFiniteCornerPeriodize_radial_collars f n hf hv hclose e.symm θ hδ hδhalf
      hcL hcR hleft hright
  have hm : (n + 1 : ℝ) ≠ 0 := by positivity
  have hLrad' : ((n + 1 : ℝ) * cL) * (δ / (n + 1 : ℝ)) < R := by
    have heq : ((n + 1 : ℝ) * cL) * (δ / (n + 1 : ℝ)) = cL * δ := by
      field_simp [hm] <;> ring
    rw [heq]
    exact hLrad
  have hRrad' : ((n + 1 : ℝ) * cR) * (1 - (1 - δ / (n + 1 : ℝ))) < R := by
    have heq : ((n + 1 : ℝ) * cR) * (1 - (1 - δ / (n + 1 : ℝ))) = cR * δ := by
      field_simp [hm] <;> ring
    rw [heq]
    exact hRrad
  have hleftP : ∀ t ∈ Icc (0 : ℝ) (δ / (n + 1 : ℝ)),
      P t = e.symm (pointRadialSectorPoint (((n + 1 : ℝ) * cL) * t) 0) := by
    intro t ht
    exact hleft' ⟨t, ⟨ht.1, ht.2.trans (hlr.trans hr).le⟩⟩ ht.2
  have hrightP : ∀ t ∈ Icc (1 - δ / (n + 1 : ℝ)) (1 : ℝ),
      P t = e.symm (pointRadialSectorPoint (((n + 1 : ℝ) * cR) * (1 - t)) θ) := by
    intro t ht
    exact hright' ⟨t, ⟨(hl.trans hlr).le.trans ht.1, ht.2⟩⟩ ht.1
  obtain ⟨δ', hδ', hδball, hboundary, hinside, houtside⟩ := exists_positive_loop_full_radial_side
    P hP hpP hiP hU hUc hV hVc hdisj hK hcoverP
    (by rwa [hbase]) (by rwa [hbase]) hw Ξ hΞ hΞlift hΞturn
    e (by rwa [hbase]) (by rwa [hbase]) he hinv hinvn hl hlr hr hcL' hcR' hR
    hθ0 hθ2 hball hLrad' hRrad' hleftP hrightP
  exact ⟨δ', hδ', hδball, by simpa only [himage] using hboundary, hinside, houtside⟩

end RepulsiveCoulomb
