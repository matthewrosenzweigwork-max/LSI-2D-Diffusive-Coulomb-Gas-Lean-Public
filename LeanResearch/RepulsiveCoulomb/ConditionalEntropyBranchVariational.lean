import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyMeasurableSup

/-!
Finite-KL variational and moment interfaces with actual integrability proofs.
The unbounded extension is proved directly by the scalar Fenchel bound and RN
integration; it does not assume a Donsker--Varadhan or tensorization theorem.
This route also proves competitor-moment integrability without presupposing
the integrability that the variational inequality is intended to establish.

Records-only draft; no Lean execution or staging has been performed.
-/
noncomputable section
open MeasureTheory InformationTheory Real Filter
open scoped ENNReal
namespace RepulsiveCoulomb

variable {α : Type*} [MeasurableSpace α]

/-- Unbounded affine dual tests are legitimate when their two actual signed
integrals exist. Finiteness of KL supplies the integrable Fenchel majorant. -/
theorem conditionalEntropyBranch_integrable_dual_le {Q P : Measure α}
    [IsFiniteMeasure Q] [IsFiniteMeasure P] (hKL : klDiv Q P ≠ ∞)
    {G : α → ℝ} (hG : Integrable G Q)
    (he : Integrable (fun x => Real.exp (G x)) P) :
    equilibriumEntropyMeasureDual Q P G ≤ (klDiv Q P).toReal := by
  obtain ⟨hac, hllr⟩ := klDiv_ne_top_iff.mp hKL
  have hmul := (integrable_toReal_rnDeriv_mul_iff hac).mpr hG
  have hd : Integrable (fun x => equilibriumEntropyDual (Q.rnDeriv P x).toReal (G x)) P :=
    (hmul.sub he).add (integrable_const 1)
  have hk : Integrable (fun x => klFun (Q.rnDeriv P x).toReal) P :=
    (integrable_klFun_rnDeriv_iff hac).mpr hllr
  have h := integral_mono hd hk
    (fun x => equilibriumEntropyDual_le ENNReal.toReal_nonneg (G x))
  rw [integral_equilibriumEntropyDual_rnDeriv hac hG he,
    ← toReal_klDiv_eq_integral_klFun hac] at h
  exact h

/-- The actual exponential normalizer is strictly positive. The shifted test
is integrated only after its integrability has been established. -/
theorem conditionalEntropyBranch_variational {Q P : Measure α}
    [IsProbabilityMeasure Q] [IsProbabilityMeasure P] (hKL : klDiv Q P ≠ ∞)
    {G : α → ℝ} (hG : Integrable G Q)
    (he : Integrable (fun x => Real.exp (G x)) P) :
    (∫ x, G x ∂Q) ≤ (klDiv Q P).toReal + Real.log (∫ x, Real.exp (G x) ∂P) := by
  let Z : ℝ := ∫ x, Real.exp (G x) ∂P
  have hZ : 0 < Z := integral_exp_pos he
  have hshift : Integrable (fun x => G x - Real.log Z) Q :=
    hG.sub (integrable_const _)
  have hexp (x : α) : Real.exp (G x - Real.log Z) = Real.exp (G x) / Z := by
    rw [Real.exp_sub, Real.exp_log hZ]
  have heshift : Integrable (fun x => Real.exp (G x - Real.log Z)) P := by
    simpa only [hexp] using he.div_const Z
  have hnorm : (∫ x, Real.exp (G x - Real.log Z) ∂P) = 1 := by
    simp_rw [hexp]
    rw [integral_div]
    exact div_self hZ.ne'
  have h := conditionalEntropyBranch_integrable_dual_le hKL hshift heshift
  rw [equilibriumEntropyMeasureDual, integral_sub hG (integrable_const _), hnorm] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  dsimp only [Z] at h
  linarith

/-- The bounded measurable form has all integrability hypotheses discharged. -/
theorem conditionalEntropyBranch_variational_bounded {Q P : Measure α}
    [IsProbabilityMeasure Q] [IsProbabilityMeasure P] (hKL : klDiv Q P ≠ ∞)
    {G : α → ℝ} (hGm : Measurable G) {M : ℝ} (hGb : ∀ x, |G x| ≤ M) :
    (∫ x, G x ∂Q) ≤ (klDiv Q P).toReal + Real.log (∫ x, Real.exp (G x) ∂P) := by
  have hG : Integrable G Q := Integrable.of_bound hGm.aestronglyMeasurable M
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hGb x))
  have he : Integrable (fun x => Real.exp (G x)) P :=
    PeriodicAttractiveLogGas.Rothaus.integrable_continuous_comp_bounded
      hGm hGb Real.continuous_exp
  exact conditionalEntropyBranch_variational hKL hG he

/-- A finite-KL competitor inherits a nonnegative exponential moment's first
moment. This is not a formal application of the unbounded variational bound:
the RN-weighted observable is first dominated by two genuinely integrable
functions, using the pointwise Fenchel inequality. -/
theorem conditionalEntropyBranch_integrable_of_exponential {Q P : Measure α}
    [IsFiniteMeasure Q] [IsFiniteMeasure P] (hKL : klDiv Q P ≠ ∞)
    {F : α → ℝ} (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (he : Integrable (fun x => Real.exp (F x)) P) : Integrable F Q := by
  obtain ⟨hac, hllr⟩ := klDiv_ne_top_iff.mp hKL
  have hk : Integrable (fun x => klFun (Q.rnDeriv P x).toReal) P :=
    (integrable_klFun_rnDeriv_iff hac).mpr hllr
  have hm : Integrable (fun x => (Q.rnDeriv P x).toReal * F x) P := by
    apply (hk.add he).mono_nonneg
      (((Measure.measurable_rnDeriv Q P).ennreal_toReal.mul hFm).aestronglyMeasurable)
    · exact Eventually.of_forall (fun x => mul_nonneg ENNReal.toReal_nonneg (hF0 x))
    · apply Eventually.of_forall
      intro x
      have h := equilibriumEntropyDual_le (q := (Q.rnDeriv P x).toReal)
        ENNReal.toReal_nonneg (F x)
      unfold equilibriumEntropyDual at h
      dsimp only [Pi.add_apply, Pi.mul_apply]
      linarith
  exact (integrable_toReal_rnDeriv_mul_iff hac).mp hm

/-- Exact positive-scale moment transfer, ready for the actual Gibbs Gaussian
exponential moment. Neither that model-specific moment nor thermal growth is
assumed to have already been proved here. -/
theorem conditionalEntropyBranch_scaled_moment {Q P : Measure α}
    [IsProbabilityMeasure Q] [IsProbabilityMeasure P] (hKL : klDiv Q P ≠ ∞)
    {F : α → ℝ} (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    {c : ℝ} (hc : 0 < c) (he : Integrable (fun x => Real.exp (c * F x)) P) :
    Integrable F Q ∧
      c * (∫ x, F x ∂Q) ≤ (klDiv Q P).toReal +
        Real.log (∫ x, Real.exp (c * F x) ∂P) := by
  have hi : Integrable (fun x => c * F x) Q :=
    conditionalEntropyBranch_integrable_of_exponential hKL (hFm.const_mul c)
      (fun x => mul_nonneg hc.le (hF0 x)) he
  have hF : Integrable F Q := by
    convert hi.div_const c using 1
    funext x
    exact (mul_div_cancel_left₀ (F x) hc.ne').symm
  refine ⟨hF, ?_⟩
  simpa only [integral_const_mul] using conditionalEntropyBranch_variational hKL hi he

/-- The signed test needed for the manuscript's defect bound. All appearances
of the KL real value are guarded by finite KL; B-integrability is explicit. -/
theorem conditionalEntropyBranch_negative_test {Q P : Measure α}
    [IsProbabilityMeasure Q] [IsProbabilityMeasure P] (hKL : klDiv Q P ≠ ∞)
    {B : α → ℝ} (hB : Integrable B Q) {ell β : ℝ} (hell : 0 < ell)
    (he : Integrable (fun x => Real.exp (-ell * β * B x)) P) :
    -(klDiv Q P).toReal / ell -
        Real.log (∫ x, Real.exp (-ell * β * B x) ∂P) / ell ≤ β * (∫ x, B x ∂Q) := by
  have h := conditionalEntropyBranch_variational hKL (hB.const_mul (-ell * β)) he
  rw [integral_const_mul] at h
  have hmul : -(klDiv Q P).toReal -
      Real.log (∫ x, Real.exp (-ell * β * B x) ∂P) ≤ (β * ∫ x, B x ∂Q) * ell := by
    nlinarith
  have hd := (div_le_iff₀ hell).mpr hmul
  simpa only [sub_div, neg_div] using hd

end RepulsiveCoulomb
