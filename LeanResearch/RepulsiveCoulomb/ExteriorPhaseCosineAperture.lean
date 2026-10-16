module

public import LeanResearch.RepulsiveCoulomb.ExteriorPhaseAperture
public import LeanResearch.RepulsiveCoulomb.ContinuousCosineBranches
public import Mathlib.Tactic

@[expose] public section

/-! Uncompiled additive successor. Normalizes scalar angle data without
reversing the geodesic or changing its parameter. The positive speed factor is
retained. No continuously branching family of rays is used. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exterior_phase_aperture_of_sin_one
    {a m b p C ε : ℝ} {φ ψ δ w : ℝ → ℝ}
    (ham : a < m) (hmb : m < b) (hp : 0 < p)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hphase : ∀ t ∈ Icc a b, p * φ t + ψ t + δ t = C)
    (hδ : ∀ t ∈ Icc a b, |δ t| ≤ ε)
    (hzero : Real.cos (ψ m) = 0) (hone : Real.sin (ψ m) = 1)
    (hleft : ∀ t ∈ Ico a m, Real.cos (ψ t) < 0)
    (hright : ∀ t ∈ Ioc m b, 0 < Real.cos (ψ t))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt φ (w t * Real.sin (ψ t)) t)
    (hw : ∀ t ∈ Ioo a b, 0 < w t)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    |φ t - φ s| ≤ (Real.pi + 2 * ε) / p := by
  let χ : ℝ → ℝ := fun v => ψ v - ψ m + Real.pi / 2
  have hχ : Continuous χ := (hψ.sub continuous_const).add continuous_const
  have hχm : χ m = Real.pi / 2 := by dsimp [χ]; ring
  have hsin (v : ℝ) : Real.sin (χ v) = Real.sin (ψ v) := by
    simp [χ, Real.sin_add, Real.sin_sub, Real.cos_sub, hzero, hone]
  have hcos (v : ℝ) : Real.cos (χ v) = Real.cos (ψ v) := by
    simp [χ, Real.cos_add, Real.sin_sub, Real.cos_sub, hzero, hone]
  have hphase' : ∀ v ∈ Icc a b,
      p * φ v + χ v + δ v = C - ψ m + Real.pi / 2 := by
    intro v hv
    have h := hphase v hv
    dsimp [χ]
    linarith
  have hleft' : ∀ v ∈ Ico a m, Real.pi / 2 < χ v ∧ χ v < 3 * Real.pi / 2 :=
    continuous_negative_cosine_branch_left hχ hχm (fun v hv => by rw [hcos]; exact hleft v hv)
  have hright' : ∀ v ∈ Ioc m b, -Real.pi / 2 < χ v ∧ χ v < Real.pi / 2 :=
    continuous_positive_cosine_branch_right hχ hχm (fun v hv => by rw [hcos]; exact hright v hv)
  apply exterior_phase_aperture_le ham hmb hp hφ hphase' hδ hχm hleft' hright' ?_ hw hs ht
  intro v hv
  rw [hsin]
  exact (hderiv v hv).deriv

theorem exterior_phase_aperture_of_cosine_signs
    {a m b p C ε : ℝ} {φ ψ δ w : ℝ → ℝ}
    (ham : a < m) (hmb : m < b) (hp : 0 < p)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hphase : ∀ t ∈ Icc a b, p * φ t + ψ t + δ t = C)
    (hδ : ∀ t ∈ Icc a b, |δ t| ≤ ε)
    (hzero : Real.cos (ψ m) = 0)
    (hleft : ∀ t ∈ Ico a m, Real.cos (ψ t) < 0)
    (hright : ∀ t ∈ Ioc m b, 0 < Real.cos (ψ t))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt φ (w t * Real.sin (ψ t)) t)
    (hw : ∀ t ∈ Ioo a b, 0 < w t)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    |φ t - φ s| ≤ (Real.pi + 2 * ε) / p := by
  rcases Real.cos_eq_zero_iff_sin_eq.mp hzero with hone | hnegone
  · exact exterior_phase_aperture_of_sin_one ham hmb hp hφ hψ hphase hδ hzero hone
      hleft hright hderiv hw hs ht
  · have hphase' : ∀ v ∈ Icc a b, p * (-φ v) + (-ψ v) + (-δ v) = -C := by
      intro v hv
      have h := hphase v hv
      linarith
    have hδ' : ∀ v ∈ Icc a b, |-δ v| ≤ ε := by
      intro v hv
      simpa only [abs_neg] using hδ v hv
    have hzero' : Real.cos (-ψ m) = 0 := by simpa only [Real.cos_neg] using hzero
    have hone' : Real.sin (-ψ m) = 1 := by rw [Real.sin_neg, hnegone]; norm_num
    have hleft' : ∀ v ∈ Ico a m, Real.cos (-ψ v) < 0 := by
      intro v hv
      simpa only [Real.cos_neg] using hleft v hv
    have hright' : ∀ v ∈ Ioc m b, 0 < Real.cos (-ψ v) := by
      intro v hv
      simpa only [Real.cos_neg] using hright v hv
    have hderiv' : ∀ v ∈ Ioo a b,
        HasDerivAt (fun x => -φ x) (w v * Real.sin (-ψ v)) v := by
      intro v hv
      convert! (hderiv v hv).neg using 1 <;> simp [Real.sin_neg] <;> ring
    have h := exterior_phase_aperture_of_sin_one ham hmb hp hφ.neg hψ.neg hphase' hδ'
      hzero' hone' hleft' hright' hderiv' hw hs ht
    change |-φ t - -φ s| ≤ (Real.pi + 2 * ε) / p at h
    simpa only [neg_sub_neg, abs_sub_comm] using h

end RepulsiveCoulomb
