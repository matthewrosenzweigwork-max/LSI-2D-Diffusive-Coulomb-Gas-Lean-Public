module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchTilt
public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchKernelIntegral
public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchConditionalMean

@[expose] public section

/-!
Genuine integrated conditional tilt inequality. Every conditional divergence
and signed expectation is proved integrable before applying integral order.
The arbitrary-Q conditional is the constructed standard-Borel disintegration.
This is a scalar tilt/Jensen integration lemma, not an assumed tensorization
or entropy-factorization result. Records-only draft, not checked.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem conditionalEntropyBranch_integrated_tilt_lower
    {α δ : Type*} [MeasurableSpace α] [MeasurableSpace δ]
    [StandardBorelSpace δ] [Nonempty δ]
    (Q : Measure (α × δ)) [IsProbabilityMeasure Q]
    (ν : Measure δ) [IsProbabilityMeasure ν] (η : Kernel α δ) [IsMarkovKernel η]
    (b : ℝ) (Φ : α × δ → ℝ) (hΦQ : Integrable Φ Q)
    (hΦν : ∀ a, Integrable (fun x => Φ (a, x)) ν)
    (hExp : ∀ a, Integrable (fun x => Real.exp (-b * Φ (a, x))) ν)
    (hMean : Integrable (fun a => ∫ x, Φ (a, x) ∂ν) Q.fst)
    (hη : ∀ a, η a = ν.tilted (fun x => -b * Φ (a, x)))
    (hBase : conditionalEntropyBranchCost Q ν ≠ ∞)
    (hTilt : klDiv Q (Q.fst ⊗ₘ η) ≠ ∞) :
    (conditionalEntropyBranchCost Q ν).toReal +
      b * ((∫ p, Φ p ∂Q) - ∫ a, ∫ x, Φ (a, x) ∂ν ∂Q.fst) ≤
        (klDiv Q (Q.fst ⊗ₘ η)).toReal := by
  let q := conditionalEntropyBranchKernel Q
  have hBase' : klDiv (Q.fst ⊗ₘ q) (Q.fst ⊗ₘ Kernel.const α ν) ≠ ∞ := by
    simpa only [q, conditionalEntropyBranch_disintegration, Measure.compProd_const,
      conditionalEntropyBranchCost] using hBase
  have hTilt' : klDiv (Q.fst ⊗ₘ q) (Q.fst ⊗ₘ η) ≠ ∞ := by
    simpa only [q, conditionalEntropyBranch_disintegration] using hTilt
  have hb := conditionalEntropyBranch_compProd_kl_finite q (Kernel.const α ν) Q.fst hBase'
  have ht := conditionalEntropyBranch_compProd_kl_finite q η Q.fst hTilt'
  have hbInt : Integrable (fun a => (klDiv (q a) ν).toReal) Q.fst := by
    simpa only [Kernel.const_apply] using hb.2
  have hbFin : ∀ᵐ a ∂Q.fst, klDiv (q a) ν < ∞ := by
    simpa only [Kernel.const_apply] using hb.1
  have hΦCond := conditionalEntropyBranch_conditional_integrable Q hΦQ
  have hΦMean := conditionalEntropyBranch_conditional_mean_integrable Q hΦQ
  have hpoint :
      (fun a => (klDiv (q a) ν).toReal +
        b * ((∫ x, Φ (a, x) ∂q a) - ∫ x, Φ (a, x) ∂ν)) ≤ᵐ[Q.fst]
      (fun a => (klDiv (q a) (η a)).toReal) := by
    filter_upwards [hbFin, hΦCond] with a ha hφa
    have h := conditionalEntropyBranch_tilt_potential_lower b hφa (hΦν a) (hExp a) ha.ne
    rwa [← hη a] at h
  have hDiff : Integrable (fun a =>
      (∫ x, Φ (a, x) ∂conditionalEntropyBranchKernel Q a) - ∫ x, Φ (a, x) ∂ν) Q.fst :=
    hΦMean.sub hMean
  have hScaled : Integrable (fun a => b *
      ((∫ x, Φ (a, x) ∂conditionalEntropyBranchKernel Q a) - ∫ x, Φ (a, x) ∂ν)) Q.fst :=
    hDiff.const_mul b
  have hSum : Integrable (fun a => (klDiv (q a) ν).toReal + b *
      ((∫ x, Φ (a, x) ∂conditionalEntropyBranchKernel Q a) - ∫ x, Φ (a, x) ∂ν)) Q.fst :=
    hbInt.add hScaled
  have hi := integral_mono_ae hSum ht.2 hpoint
  rw [integral_add hbInt hScaled, integral_const_mul,
    integral_sub hΦMean hMean, conditionalEntropyBranch_conditional_mean_tower Q hΦQ] at hi
  have hbEq : (conditionalEntropyBranchCost Q ν).toReal = ∫ a, (klDiv (q a) ν).toReal ∂Q.fst := by
    simpa only [q, conditionalEntropyBranch_disintegration, Measure.compProd_const,
      Kernel.const_apply, conditionalEntropyBranchCost] using
      conditionalEntropyBranch_compProd_kl_integral_real q (Kernel.const α ν) Q.fst hBase'
  have htEq : (klDiv Q (Q.fst ⊗ₘ η)).toReal = ∫ a, (klDiv (q a) (η a)).toReal ∂Q.fst := by
    simpa only [q, conditionalEntropyBranch_disintegration] using
      conditionalEntropyBranch_compProd_kl_integral_real q η Q.fst hTilt'
  rw [← hbEq, ← htEq] at hi
  exact hi

end RepulsiveCoulomb
