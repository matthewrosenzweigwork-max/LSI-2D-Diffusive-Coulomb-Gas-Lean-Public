/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; see Imported/TauCeti/LICENSE.
Authors of the original covering argument: The Tau Ceti contributors

The covering-proof organization is adapted from the attributed
Imported/TauCeti/MeasureTheory/Integral/MaximalFunction.lean and the new
GenericDoublingSobolevMaximal.lean. Here the two measures are deliberately
different: planar volume measures the covering, while an arbitrary Borel
measure supplies the mass. In particular no density or null-sphere hypothesis
is imposed on the source measure.
-/
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

/-! The actual centered maximal density of an arbitrary finite planar Borel
measure, including atoms, and its weak (1,1) bound by fourfold open-ball Vitali
selection. The first covering lemma does not even need source finiteness. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb.PaperRoute

/-- The paper's centered maximal function, normalized by literal planar area. -/
def planarMeasureMaximal (η : Measure ℂ) (x : ℂ) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), η (ball x r) / volume (ball x r)

theorem planar_ball_volume_eq (x : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume (ball x r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [Complex.volume_ball, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (sq_nonneg r)]
  congr 1
  simp only [NNReal.coe_real_pi]
  ring

theorem planar_ball_four_volume (x : ℂ) (r : ℝ) :
    volume (ball x (4 * r)) = 16 * volume (ball x r) := by
  simp only [Complex.volume_ball, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    mul_pow]
  norm_num
  ring

/-- Actual two-measure Vitali estimate. Source atoms and nonmeasurable S are allowed. -/
theorem planar_vitali_two_measure_bound (η : Measure ℂ)
    {S : Set ℂ} {R : ℝ} {t : ℝ≥0∞}
    (hS : ∀ x ∈ S, ∃ r ∈ Ioc (0 : ℝ) R,
      t * volume (ball x r) ≤ η (ball x r)) :
    t * volume S ≤ 16 * η univ := by
  classical
  choose! r hr hle using hS
  obtain ⟨u, hu, hdisj, hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball S id r R
      (fun x hx => (hr x hx).2) 4 (by norm_num)
  simp only [id_eq] at hdisj hcov
  have hcount : u.Countable := hdisj.countable_of_isOpen
    (fun _ _ => isOpen_ball)
    (fun x hx => ⟨x, mem_ball_self (hr x (hu hx)).1⟩)
  let : Countable u := hcount.to_subtype
  have hsub : S ⊆ ⋃ b ∈ u, ball b (4 * r b) := fun x hx => by
    obtain ⟨b, hb, hball⟩ := hcov x hx
    exact mem_biUnion hb (hball (mem_ball_self (hr x hx).1))
  have hdisj' : Pairwise (Function.onFun Disjoint fun b : u => ball (b : ℂ) (r b)) :=
    fun b b' hbb' => hdisj b.2 b'.2 (Subtype.coe_injective.ne hbb')
  calc
    t * volume S ≤ t * ∑' b : u, volume (ball (b : ℂ) (4 * r b)) := by
      apply mul_le_mul' le_rfl
      exact (measure_mono hsub).trans (measure_biUnion_le volume hcount _)
    _ = ∑' b : u, t * volume (ball (b : ℂ) (4 * r b)) := ENNReal.tsum_mul_left.symm
    _ ≤ ∑' b : u, 16 * η (ball (b : ℂ) (r b)) := by
      apply ENNReal.tsum_le_tsum
      intro b
      rw [planar_ball_four_volume]
      calc
        t * (16 * volume (ball (b : ℂ) (r b))) =
            16 * (t * volume (ball (b : ℂ) (r b))) := by ac_rfl
        _ ≤ _ := mul_le_mul' le_rfl (hle b (hu b.2))
    _ = 16 * ∑' b : u, η (ball (b : ℂ) (r b)) := ENNReal.tsum_mul_left
    _ = 16 * η (⋃ b : u, ball (b : ℂ) (r b)) := by
      rw [measure_iUnion hdisj' (fun _ => measurableSet_ball)]
    _ ≤ 16 * η univ := mul_le_mul' le_rfl (measure_mono (subset_univ _))

/-- Every ball quotient lies below the actual maximal function. -/
theorem planarMeasureMaximal_ball_le (η : Measure ℂ) (x : ℂ)
    {r : ℝ} (hr : 0 < r) :
    η (ball x r) / volume (ball x r) ≤ planarMeasureMaximal η x :=
  le_iSup_of_le r (le_iSup_of_le hr le_rfl)

/-- A finite bound on the maximal function gives actual ball growth, even at atoms. -/
theorem planarMeasureMaximal_ball_growth (η : Measure ℂ) (x : ℂ)
    {b r : ℝ} (hr : 0 < r) (hb : planarMeasureMaximal η x ≤ ENNReal.ofReal b) :
    η (ball x r) ≤ ENNReal.ofReal b * volume (ball x r) := by
  have h := (planarMeasureMaximal_ball_le η x hr).trans hb
  have hzero : volume (ball x r) ≠ 0 := (measure_ball_pos volume x hr).ne'
  have htop : volume (ball x r) ≠ ⊤ := measure_ball_lt_top.ne
  exact (ENNReal.div_le_iff hzero htop).mp h

/-- Weak (1,1) for arbitrary finite source measure against planar Lebesgue volume. -/
theorem planarMeasureMaximal_weak_bound (η : Measure ℂ) [IsFiniteMeasure η]
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal t * volume {x | ENNReal.ofReal t < planarMeasureMaximal η x} ≤
      16 * η univ := by
  apply planar_vitali_two_measure_bound η (R := 1 + (η univ).toReal / (Real.pi * t))
  intro x hx
  change ENNReal.ofReal t < ⨆ (r : ℝ) (_ : 0 < r), η (ball x r) / volume (ball x r) at hx
  obtain ⟨r, hr⟩ := lt_iSup_iff.mp hx
  obtain ⟨hrpos, hquot⟩ := lt_iSup_iff.mp hr
  have hmass : ENNReal.ofReal t * volume (ball x r) ≤ η univ :=
    (ENNReal.mul_lt_of_lt_div hquot).le.trans (measure_mono (subset_univ _))
  have hreal := ENNReal.toReal_mono (measure_ne_top η univ) hmass
  rw [planar_ball_volume_eq x hrpos.le, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ht.le, ENNReal.toReal_ofReal (by positivity)] at hreal
  have hsq : r ^ 2 ≤ (η univ).toReal / (Real.pi * t) := by
    apply (le_div_iff₀ (mul_pos Real.pi_pos ht)).mpr
    nlinarith [hreal]
  have hrbound : r ≤ 1 + (η univ).toReal / (Real.pi * t) := by
    nlinarith [sq_nonneg (r - 1)]
  exact ⟨r, ⟨hrpos, hrbound⟩, (ENNReal.mul_lt_of_lt_div hquot).le⟩

/-- Divided form of the actual finite-measure maximal weak estimate. -/
theorem planarMeasureMaximal_weak_measure (η : Measure ℂ) [IsFiniteMeasure η]
    {t : ℝ} (ht : 0 < t) :
    volume {x | ENNReal.ofReal t < planarMeasureMaximal η x} ≤
      (16 * η univ) / ENNReal.ofReal t := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr ht).ne')
    (Or.inl ENNReal.ofReal_ne_top)).mpr
  simpa only [mul_comm] using planarMeasureMaximal_weak_bound η ht

end RepulsiveCoulomb.PaperRoute
