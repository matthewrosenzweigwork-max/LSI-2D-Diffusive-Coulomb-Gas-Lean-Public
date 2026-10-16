module

public import LeanResearch.RepulsiveCoulomb.CoulombGroundStateTemperature

@[expose] public section

/-! RECORDS-ONLY UNCHECKED DRAFT. Exact energy transfer to a limiting
positive temperature, with explicit uniform drift and mass bounds. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulomb_tendsto_zero_mul_bounded (c s : ℕ → ℝ) (K : ℝ)
    (hc : Tendsto c atTop (𝓝 0)) (hs : ∀ n, |s n| ≤ K) :
    Tendsto (fun n => c n * s n) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ?_)
    (show Tendsto (fun n => |c n| * K) atTop (𝓝 0) by
      simpa only [abs_zero, zero_mul] using hc.abs.mul_const K)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hs n) (abs_nonneg _)

theorem coulombInverseGroundState_energy_tendsto_zero {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (γ : ℕ → ℝ) (hγ : ∀ n, 0 < γ n)
    (ψ : ℕ → TestFunction (coulombDomain N) ℝ ⊤)
    (hlim : Tendsto γ atTop (𝓝 β)) (K M : ℝ)
    (hS : ∀ n, (∫ z : CoulombConfig N,
      ‖gradient (coulombPotential (1 : ℝ)) z‖ ^ 2 * ψ n z ^ 2) ≤ K)
    (hM : ∀ n, (∫ z : CoulombConfig N, ψ n z ^ 2) ≤ M)
    (hE : Tendsto (fun n => ∫ z,
      ‖gradient (coulombInverseGroundStateCore (hγ n) (ψ n) : CoulombConfig N → ℝ) z‖ ^ 2
        ∂coulombMeasure N (γ n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z,
      ‖gradient (coulombInverseGroundStateCore hβ (ψ n) : CoulombConfig N → ℝ) z‖ ^ 2
        ∂coulombMeasure N β) atTop (𝓝 0) := by
  have hcoef : Tendsto (fun n => (β ^ 2 - (γ n) ^ 2) / 4) atTop (𝓝 0) := by
    simpa only [sub_self, zero_div] using
      (((tendsto_const_nhds : Tendsto (fun _ : ℕ => β ^ 2) atTop (𝓝 (β ^ 2))).sub
        (hlim.pow 2)).div_const 4)
  have hsmall : Tendsto (fun n => (N : ℝ) * (β - γ n)) atTop (𝓝 0) := by
    simpa only [sub_self, mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (N : ℝ)) atTop (𝓝 (N : ℝ))).mul
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => β) atTop (𝓝 β)).sub hlim))
  have hSabs (n : ℕ) : |∫ z : CoulombConfig N,
      ‖gradient (coulombPotential (1 : ℝ)) z‖ ^ 2 * ψ n z ^ 2| ≤ K := by
    rw [abs_of_nonneg (integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hS n
  have hMabs (n : ℕ) : |∫ z : CoulombConfig N, ψ n z ^ 2| ≤ M := by
    rw [abs_of_nonneg (integral_nonneg fun z => sq_nonneg _)]
    exact hM n
  have h1 := coulomb_tendsto_zero_mul_bounded _ _ K hcoef hSabs
  have h2 := coulomb_tendsto_zero_mul_bounded _ _ M hsmall hMabs
  have h := (hE.add h1).sub h2
  have heq : (fun n => ∫ z,
      ‖gradient (coulombInverseGroundStateCore hβ (ψ n) : CoulombConfig N → ℝ) z‖ ^ 2
        ∂coulombMeasure N β) =
    (fun n => (∫ z,
      ‖gradient (coulombInverseGroundStateCore (hγ n) (ψ n) : CoulombConfig N → ℝ) z‖ ^ 2
        ∂coulombMeasure N (γ n)) +
      ((β ^ 2 - (γ n) ^ 2) / 4) * (∫ z : CoulombConfig N,
        ‖gradient (coulombPotential (1 : ℝ)) z‖ ^ 2 * ψ n z ^ 2) -
      (N : ℝ) * (β - γ n) * (∫ z : CoulombConfig N, ψ n z ^ 2)) :=
    funext fun n => coulombInverseGroundState_energy_comparison hβ (hγ n) (ψ n)
  rw [heq]
  simpa only [zero_add, sub_zero] using h

end RepulsiveCoulomb
