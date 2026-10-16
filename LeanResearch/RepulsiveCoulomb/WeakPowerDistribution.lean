import LeanResearch.RepulsiveCoulomb.PointHedbergOscillation

/-! A genuine weak distribution bound obtained from a pointwise power estimate
and a genuine weak(1,1) bound. This abstract scalar step does not assert either
analytic input by itself. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem weak_distribution_of_power_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (u : X → ℝ) (M : X → ℝ≥0∞)
    {K α q : ℝ} (hK : 0 < K) (hq : 0 < q) (hαq : α * q = 1)
    (hfinite : ∀ x ∈ S, M x ≠ ⊤)
    (hpoint : ∀ x ∈ S, u x ≤ K * (M x).toReal ^ α)
    {C : ℝ≥0∞} (hweak : ∀ t : ℝ≥0∞, t * μ {x | t < M x} ≤ C)
    {L : ℝ} (hL : 0 < L) :
    ENNReal.ofReal (L ^ q) * μ {x | x ∈ S ∧ L < u x} ≤ ENNReal.ofReal (K ^ q) * C := by
  let t : ℝ := (L / K) ^ q
  have ht : 0 < t := Real.rpow_pos_of_pos (div_pos hL hK) q
  have hsub : {x | x ∈ S ∧ L < u x} ⊆ {x | ENNReal.ofReal t < M x} := by
    intro x hx
    apply (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hfinite x hx.1)).mpr
    have hlt : L / K < (M x).toReal ^ α := (div_lt_iff₀ hK).mpr (by
      simpa only [mul_comm] using hx.2.trans_le (hpoint x hx.1))
    have h := Real.rpow_lt_rpow (div_nonneg hL.le hK.le) hlt hq
    rw [← Real.rpow_mul ENNReal.toReal_nonneg, hαq, Real.rpow_one] at h
    exact h
  have hw : ENNReal.ofReal t * μ {x | x ∈ S ∧ L < u x} ≤ C :=
    (mul_le_mul' le_rfl (measure_mono hsub)).trans (hweak (ENNReal.ofReal t))
  have he : ENNReal.ofReal (K ^ q) * ENNReal.ofReal t = ENNReal.ofReal (L ^ q) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hK.le _)]
    congr 1
    dsimp [t]
    rw [Real.div_rpow hL.le hK.le, mul_div_cancel₀ _ (Real.rpow_pos_of_pos hK q).ne']
  have h := mul_le_mul' (le_refl (ENNReal.ofReal (K ^ q))) hw
  rwa [← mul_assoc, he] at h

end RepulsiveCoulomb
