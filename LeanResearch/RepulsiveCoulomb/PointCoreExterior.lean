import LeanResearch.RepulsiveCoulomb.CutoffPairEnergy

/-! Actual outer-core mass absorption from the uniform quadratic-moment bound. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem exterior_quadratic_mass {μ : Measure ℂ} {R : ℝ} (hR : 0 < R)
    (f : ℂ → ℝ) (hf : Integrable (fun x => f x ^ 2) μ)
    (hm : Integrable (fun x => ‖x‖ ^ 2 * f x ^ 2) μ)
    (hz : ∀ x ∈ ball (0 : ℂ) R, f x = 0) :
    R ^ 2 * (∫ x, f x ^ 2 ∂μ) ≤ ∫ x, ‖x‖ ^ 2 * f x ^ 2 ∂μ := by
  rw [← integral_const_mul]
  apply integral_mono (hf.const_mul _) hm
  intro x
  by_cases hx : x ∈ ball (0 : ℂ) R
  · simp [hz x hx]
  · have hn : R ≤ ‖x‖ := by simpa [mem_ball, dist_zero_right] using hx
    exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg (f x))

theorem exterior_moment_absorb {C R M E : ℝ} (hR : 0 < R)
    (hlarge : 2 * C ≤ R ^ 2) (hM : 0 ≤ M)
    (h : R ^ 2 * M ≤ C * (E + M)) : M ≤ (2 * C / R ^ 2) * E := by
  have hs := mul_le_mul_of_nonneg_right hlarge hM
  have hbound : M * R ^ 2 ≤ 2 * C * E := by nlinarith only [hs, h]
  simpa only [div_mul_eq_mul_div] using (le_div_iff₀ (sq_pos_of_pos hR)).mpr hbound

theorem pointCore_uniform_exterior_mass {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
      (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ (R : ℝ) (hR : 0 < R),
      2 * C ≤ R ^ 2 → ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      (∀ x ∈ ball (0 : ℂ) R, φ x = 0) →
      (∫ x, φ x ^ 2 ∂pointMeasure γ a y) ≤ (2 * C / R ^ 2) *
        (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) := by
  obtain ⟨C, hC, hc⟩ := pointCore_weighted_moment_bound (Q := Q) hγ
  refine ⟨C, hC, ?_⟩
  intro m a ha y hQ R hR hlarge φ hz
  let _ := pointMeasure_isProbability hγ ha y
  have hs : HasCompactSupport (fun x : ℂ => φ x ^ 2) :=
    φ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hi : Integrable (fun x : ℂ => φ x ^ 2) (pointMeasure γ a y) :=
    (φ.continuous.pow 2).integrable_of_hasCompactSupport hs
  have htail := exterior_quadratic_mass hR (φ : ℂ → ℝ) hi
    (pointCore_moment_integrable hγ ha y φ) hz
  exact exterior_moment_absorb hR hlarge (integral_nonneg (fun _ => sq_nonneg _))
    (htail.trans (hc m a ha y hQ φ))

theorem pointCore_cutoff_pair_energy {m : ℕ} {γ R D : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hR : 0 < R)
    (hD : 0 ≤ D) (hb : ∀ z, ‖gradient (pointCutoffBump 0 R hR) z‖ ≤ D)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    (∫ x, ‖gradient (pointCoreInnerCutoff R hR φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
      (∫ x, ‖gradient (pointCoreOuterCutoff R hR φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) ≤
      2 * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
      4 * D ^ 2 * (∫ x, φ x ^ 2 ∂pointMeasure γ a y) := by
  let _ := pointMeasure_isProbability hγ ha y
  apply cutoff_pair_energy_le (pointMeasure γ a y)
    ((pointCutoffBump_contDiff 0 R hR).differentiable (by simp))
    (φ.contDiff.differentiable (by simp))
    (fun _ => (pointCutoffBump 0 R hR).nonneg)
    (fun _ => (pointCutoffBump 0 R hR).le_one) hD hb
  · exact testFunction_physical_energy_integrable _ (pointCoreInnerCutoff R hR φ) _
  · exact testFunction_physical_energy_integrable _ (pointCoreOuterCutoff R hR φ) _
  · exact testFunction_physical_energy_integrable _ φ _
  · have hs : HasCompactSupport (fun x : ℂ => φ x ^ 2) :=
      φ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact (φ.continuous.pow 2).integrable_of_hasCompactSupport hs

end RepulsiveCoulomb
