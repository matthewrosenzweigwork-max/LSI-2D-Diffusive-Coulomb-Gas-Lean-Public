import LeanResearch.RepulsiveCoulomb.CoulombCoreSlice

/-! Uniform conditional inequalities for the actual labeled smooth core.
The energy is the first component of the full real Euclidean gradient. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open PeriodicAttractiveLogGas
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulomb_core_one_site_inequalities {β : ℝ} (hβ : 0 < β) :
    ∃ P K : ℝ, 0 < P ∧ 0 < K ∧ ∀ (N : ℕ) (y : CoulombConfig N)
      (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤),
    variance (fun w : ℂ => φ (coulombInsertZero w y)) (coulombOneSiteKernel N β hβ y) ≤
      P * (∫ w, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) (coulombInsertZero w y) 0‖ ^ 2
        ∂coulombOneSiteKernel N β hβ y) ∧
    entropy (coulombOneSiteKernel N β hβ y) (fun w => φ (coulombInsertZero w y) ^ 2) ≤
      ((K * (∫ w, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) (coulombInsertZero w y) 0‖ ^ 2
        ∂coulombOneSiteKernel N β hβ y) : ℝ) : EReal) := by
  obtain ⟨P, hP, hp⟩ := pointCore_uniform_poincare (Q := β) hβ
  obtain ⟨K, hK, hk⟩ := pointCore_uniform_tight_lsi (Q := β) hβ
  refine ⟨P, K, hP, hK, ?_⟩
  intro N y φ
  let a := coulombOneSiteExponents N β
  let ψ := coulombCoreSliceZero a φ y
  have hQ : ∑ j, a j ≤ β := (coulomb_one_site_exponent_sum_lt N hβ).le
  have hp' := hp N a (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) hQ ψ
  have hk' := hk N a (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) hQ ψ
  have he : (∫ w, ‖gradient (ψ : ℂ → ℝ) w‖ ^ 2 ∂pointMeasure β a (fun j => y j)) =
      ∫ w, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) (coulombInsertZero w y) 0‖ ^ 2
        ∂coulombOneSiteKernel N β hβ y := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun w => congrArg (fun v : ℂ => ‖v‖ ^ 2)
      (coulombCoreSliceZero_gradient a φ y w))
  rw [he] at hp' hk'
  exact ⟨hp', hk'⟩

end RepulsiveCoulomb

