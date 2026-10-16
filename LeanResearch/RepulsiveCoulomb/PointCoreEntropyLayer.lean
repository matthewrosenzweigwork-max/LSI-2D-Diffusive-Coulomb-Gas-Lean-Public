import LeanResearch.RepulsiveCoulomb.TruncationSPISum
import LeanResearch.RepulsiveCoulomb.FiniteDyadicEntropyLayer
import LeanResearch.RepulsiveCoulomb.RothausTightening

/-! Integrating the finite smooth entropy-layer bound on the actual core. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointCore_entropy_layer_integral {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) (N : ℕ)
    (hb : ∀ x, |φ x| ≤ (2 : ℝ) ^ (N + 2)) :
    (∫ x, φ x ^ 2 * Real.log (φ x ^ 2) ∂pointMeasure γ a y) ≤
      4 * Real.log 2 * (∫ x, φ x ^ 2 ∂pointMeasure γ a y) + 96 * Real.log 2 *
      ∑ k ∈ Finset.range N, ((k : ℝ) + 1) *
        ((∫ x, (pointCoreSmoothTruncation ((2 : ℝ) ^ (k + 1)) (by positivity) φ x) ^ 2 ∂pointMeasure γ a y) +
          (∫ x, (pointCoreSmoothTruncation ((2 : ℝ) ^ (k + 1)) (by positivity) (-φ) x) ^ 2 ∂pointMeasure γ a y)) := by
  let _ := pointMeasure_isProbability hγ ha y
  let μ := pointMeasure γ a y
  let p (k : ℕ) := pointCoreSmoothTruncation ((2 : ℝ) ^ (k + 1)) (by positivity) φ
  let n (k : ℕ) := pointCoreSmoothTruncation ((2 : ℝ) ^ (k + 1)) (by positivity) (-φ)
  have hi (ψ : TestFunction (pointDomain a y) ℝ ⊤) : Integrable (fun x : ℂ => ψ x ^ 2) μ := by
    have hs : HasCompactSupport (fun x : ℂ => ψ x ^ 2) :=
      ψ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact (ψ.continuous.pow 2).integrable_of_hasCompactSupport hs
  have hl : Integrable (fun x : ℂ => φ x ^ 2 * Real.log (φ x ^ 2)) μ :=
    PeriodicAttractiveLogGas.Rothaus.integrable_continuous_comp_bounded φ.continuous.measurable hb
      (Real.continuous_mul_log.comp (continuous_id.pow 2))
  have ht (k : ℕ) : Integrable (fun x : ℂ => ((k : ℝ) + 1) * ((p k x) ^ 2 + (n k x) ^ 2)) μ :=
    ((hi (p k)).add (hi (n k))).const_mul _
  have hsum := integrable_finsetSum (Finset.range N) (fun k _ => ht k)
  have h := integral_mono hl (((hi φ).const_mul (4 * Real.log 2)).add (hsum.const_mul (96 * Real.log 2)))
    (fun x => finite_dyadic_entropy_layer N (φ x) (hb x))
  dsimp only [Pi.add_apply] at h
  rw [integral_add ((hi φ).const_mul (4 * Real.log 2)) (hsum.const_mul (96 * Real.log 2)),
    integral_const_mul, integral_const_mul, integral_finsetSum (Finset.range N) (fun k _ => ht k)] at h
  have he (k : ℕ) : (∫ x, ((k : ℝ) + 1) * ((p k x) ^ 2 + (n k x) ^ 2) ∂μ) =
      ((k : ℝ) + 1) * ((∫ x, (p k x) ^ 2 ∂μ) + ∫ x, (n k x) ^ 2 ∂μ) := by
    rw [integral_const_mul, integral_add (hi (p k)) (hi (n k))]
  simp_rw [he] at h
  exact h

theorem testFunction_dyadic_bound (Ω : TopologicalSpace.Opens ℂ)
    (φ : TestFunction Ω ℝ ⊤) : ∃ N : ℕ, ∀ x, |φ x| ≤ (2 : ℝ) ^ (N + 2) := by
  obtain ⟨M, hM⟩ := testFunction_bounded Ω φ
  have ht := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually
    (eventually_ge_atTop M)
  obtain ⟨N, hN⟩ := ht.exists
  refine ⟨N, fun x => (hM x).trans (hN.trans ?_)⟩
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)

end RepulsiveCoulomb
