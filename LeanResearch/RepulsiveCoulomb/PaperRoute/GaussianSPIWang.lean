import LeanResearch.RepulsiveCoulomb.PointCoreNormalizedEntropy
import LeanResearch.RepulsiveCoulomb.EntropySquareScaling

/-! Additive experimental source. Verification status is recorded separately in evidence. The needed conditional Gaussian SPI-to-defective-LSI specialization and exact denormalization. -/
noncomputable section
open Set MeasureTheory Filter
open PeriodicAttractiveLogGas
open scoped Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem denormalize_square_entropy {M c S C D E : ℝ} (hM : 0 ≤ M)
    (hc : c ^ 2 * M = 1) (h : c ^ 2 * S ≤ C * (c ^ 2 * E) + D) :
    S ≤ C * E + D * M := by
  have hm := mul_le_mul_of_nonneg_right h hM
  have hleft : c ^ 2 * S * M = S := by calc
    _ = (c ^ 2 * M) * S := by ring
    _ = S := by rw [hc, one_mul]
  have hright : (C * (c ^ 2 * E) + D) * M = C * E + D * M := by calc
    _ = C * E * (c ^ 2 * M) + D * M := by ring
    _ = _ := by rw [hc, mul_one]
  rwa [hleft, hright] at hm

/-- The concrete Gaussian-rate implication needed for the Wang application.
It consumes the supplied SPI on the same original core, measure, and physical
energy. It does not select an unconditional SPI theorem or assert an abstract
Markov/normal-contraction certificate. -/
theorem core_defective_lsi_of_gaussian_spi {m : ℕ} {γ A B K : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hA : 0 < A) (hB : 0 < B) (hK : 0 < K)
    (hKb : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ K)
    (hSPI : ∀ s : ℝ, 0 < s → ∀ ψ : TestFunction (pointDomain a y) ℝ ⊤,
      (∫ x, ψ x ^ 2 ∂pointMeasure γ a y) ≤
        s * (∫ x, ‖gradient (ψ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        A * Real.exp (B / s) * (∫ x, |ψ x| ∂pointMeasure γ a y) ^ 2)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    entropy (pointMeasure γ a y) (fun x => φ x ^ 2) ≤
      (((192 * B * K ^ 2) * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        ((4 + 384 * A) * Real.log 2) * (∫ x, φ x ^ 2 ∂pointMeasure γ a y) : ℝ) : EReal) := by
  let C := 192 * B * K ^ 2
  let D := (4 + 384 * A) * Real.log 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hD : 0 < D := mul_pos (by linarith) (Real.log_pos (by norm_num))
  let _ := pointMeasure_isProbability hγ ha y
  let μ := pointMeasure γ a y
  let M := ∫ x, φ x ^ 2 ∂μ
  have hM : 0 ≤ M := integral_nonneg (fun _ => sq_nonneg _)
  obtain ⟨b, hb⟩ := testFunction_bounded (pointDomain a y) φ
  by_cases hzero : M = 0
  · have hz := (Rothaus.entropy_sq_and_shift_zero φ.continuous.measurable ⟨b, hb⟩ hzero).1
    rw [hz]
    exact_mod_cast (show 0 ≤ C * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂μ) + D * M from
      add_nonneg (mul_nonneg hC.le (integral_nonneg (fun _ => sq_nonneg _))) (mul_nonneg hD.le hM))
  · have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
    let c := (Real.sqrt M)⁻¹
    let ψ : TestFunction (pointDomain a y) ℝ ⊤ := c • φ
    have hc : c ^ 2 * M = 1 := by
      dsimp [c]
      rw [inv_pow, Real.sq_sqrt hM, inv_mul_cancel₀ hzero]
    have hψ : (∫ x, ψ x ^ 2 ∂μ) = 1 := by
      rw [testFunction_smul_mass]
      exact hc
    have hn := pointCore_normalized_entropy_of_spi hγ ha y hA hB hK.le hKb hSPI ψ hψ
    have hs : Rothaus.squareEntropy μ (ψ : ℂ → ℝ) ≤
        C * (∫ x, ‖gradient (ψ : ℂ → ℝ) x‖ ^ 2 ∂μ) + D := by
      unfold Rothaus.squareEntropy
      rw [hψ, Real.log_one, mul_zero, sub_zero]
      exact hn
    have hscale := bounded_squareEntropy_smul μ φ.continuous.measurable hb c
    change Rothaus.squareEntropy μ (ψ : ℂ → ℝ) = c ^ 2 * Rothaus.squareEntropy μ (φ : ℂ → ℝ) at hscale
    rw [hscale, testFunction_smul_energy] at hs
    have hfinal := denormalize_square_entropy hM hc hs
    rw [Rothaus.entropy_sq_eq φ.continuous.measurable hb]
    exact_mod_cast hfinal

end RepulsiveCoulomb.PaperRoute
