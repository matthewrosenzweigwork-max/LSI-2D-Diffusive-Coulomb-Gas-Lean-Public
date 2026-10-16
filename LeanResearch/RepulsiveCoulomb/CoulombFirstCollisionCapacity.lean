module

public import LeanResearch.RepulsiveCoulomb.CoulombCollisionTensor
public import LeanResearch.RepulsiveCoulomb.CoulombRelativeRawIntegral

@[expose] public section

/-! Vanishing global weighted energy at the first collision hyperplane.
The positive power beta/(N+2) is retained exactly. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombFirstCollisionBump_energy_bound (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ε : ℝ) (hε : 0 < ε),
      (∫ z, ‖gradient (coulombFirstCollisionBump N ε hε) z‖ ^ 2 ∂coulombMeasure (N + 2) β) ≤
        K * ε ^ (β / ((N + 2 : ℕ) : ℝ)) := by
  let α := β / ((N + 2 : ℕ) : ℝ)
  have hα : 0 < α := div_pos hβ (by positivity)
  obtain ⟨C, hC, hd⟩ := coulombDensity_relative_le_power N hβ
  obtain ⟨B, hB, hb⟩ := planar_power_cutoff_energy_bound hα.le
  let A := ∫ p, coulombFrozenGaussian N β p
  have hA : 0 ≤ A := integral_nonneg (coulombFrozenGaussian_nonneg N β)
  refine ⟨C * (A + 1) * B, by positivity, ?_⟩
  intro ε hε
  let g : ℂ → ℝ := fun u => ‖u‖ ^ α * ‖gradient (pointCutoffBump 0 ε hε) u‖ ^ 2
  let f : (ℂ × CoulombConfig N) × ℂ → ℝ := fun q =>
    coulombDensity (N + 2) β (coulombRelativeInsert q.1.1 q.2 q.1.2) *
      ‖gradient (pointCutoffBump 0 ε hε) q.2‖ ^ 2
  have hg : Integrable g := planar_power_cutoff_energy_integrable hα.le hε
  have hg0 (u : ℂ) : 0 ≤ g u := mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _)
  have hf0 (q : (ℂ × CoulombConfig N) × ℂ) : 0 ≤ f q :=
    mul_nonneg (coulombDensity_nonneg β _) (sq_nonneg _)
  have hmajor : Integrable (fun q : (ℂ × CoulombConfig N) × ℂ =>
      C * (coulombFrozenGaussian N β q.1 * g q.2)) := by
    rw [Measure.volume_eq_prod (ℂ × CoulombConfig N) ℂ]
    exact ((coulombFrozenGaussian_integrable N hβ).mul_prod hg).const_mul C
  have hle (q : (ℂ × CoulombConfig N) × ℂ) :
      f q ≤ C * (coulombFrozenGaussian N β q.1 * g q.2) := by
    have h := mul_le_mul_of_nonneg_right (hd q.1 q.2)
      (sq_nonneg ‖gradient (pointCutoffBump 0 ε hε) q.2‖)
    convert h using 1 <;> dsimp [f, g, α] <;> ring
  have hm : Measurable f := by
    exact ((coulombDensity_continuous hβ.le).measurable.comp
      (coulombRelativeInsert_joint_measurable N)).mul
      (((TauCeti.continuous_gradient_testFunction (pointCutoffTestFunction 0 ε hε)).norm.pow 2).measurable.comp
        measurable_snd)
  have hfi : Integrable f := hmajor.mono' hm.aestronglyMeasurable
    (Eventually.of_forall (fun q => by rw [Real.norm_eq_abs, abs_of_nonneg (hf0 q)]; exact hle q))
  have hi := integral_mono hfi hmajor hle
  rw [integral_const_mul, Measure.volume_eq_prod (ℂ × CoulombConfig N) ℂ,
    integral_prod_mul] at hi
  rw [coulombFirstCollisionBump_energy_pullback N hβ ε hε]
  change (∫ q, f q) ≤ _
  calc
    _ ≤ C * (A * ∫ u, g u) := hi
    _ ≤ C * ((A + 1) * ∫ u, g u) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by linarith : A ≤ A + 1) (integral_nonneg hg0)) hC.le
    _ ≤ C * ((A + 1) * (B * ε ^ α)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hb ε hε) (by positivity)) hC.le
    _ = _ := by ring

theorem coulombFirstCollisionBump_energy_tendsto_zero (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, ‖gradient (coulombFirstCollisionBump N (ε n) (hε n)) z‖ ^ 2
      ∂coulombMeasure (N + 2) β) atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := coulombFirstCollisionBump_energy_bound N hβ
  have hα : 0 < β / ((N + 2 : ℕ) : ℝ) := div_pos hβ (by positivity)
  have ht := ((Real.continuous_rpow_const hα.le).tendsto 0).comp hlim
  have hz : (0 : ℝ) ^ (β / ((N + 2 : ℕ) : ℝ)) = 0 := Real.zero_rpow hα.ne'
  rw [hz] at ht
  apply squeeze_zero (fun n => integral_nonneg (fun z => sq_nonneg _)) (fun n => hb (ε n) (hε n))
  simpa using ht.const_mul K

end RepulsiveCoulomb

