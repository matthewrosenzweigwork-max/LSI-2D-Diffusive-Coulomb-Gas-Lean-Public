module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.LogSmoothConvolution
public import LeanResearch.RepulsiveCoulomb.CoulombCoordinateSplit
public import LeanResearch.RepulsiveCoulomb.CoulombSliceGeometry

@[expose] public section

/-! Additive original-paper producer. Genuine cylindrical logarithmic integrability for arbitrary
compactly supported continuous tests on the full Euclidean configuration
space. No collision-avoidance hypothesis or distributional identity is used. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace Metric
open scoped Topology
namespace RepulsiveCoulomb.PaperRoute

theorem collision_split_symm {N : ℕ} (p : ℂ × CoulombConfig N) :
    (coulombSplitZero N).symm p = coulombInsertZero p.1 p.2 := by
  rcases p with ⟨u,y⟩
  exact coulombSplitZero_symm_apply u y

/-- A planar local-L1 function times an actual compact continuous full-space
test is integrable after the normal/tangential coordinate split. -/
theorem cylindrical_local_integrable_test_prod {N : ℕ} {k : ℂ → ℝ}
    (hkm : Measurable k) (hk : LocallyIntegrable k volume)
    {ψ : CoulombConfig (N + 1) → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun p : ℂ × CoulombConfig N => k p.1 * ψ (coulombInsertZero p.1 p.2))
      (volume.prod volume) := by
  obtain ⟨R, hR, hsub⟩ := hψc.isBounded.subset_closedBall_lt (1 : ℝ) (0 : CoulombConfig (N + 1))
  obtain ⟨B, hB⟩ := hψ.bounded_above_of_compact_support hψc
  have hB0 : 0 ≤ B := (norm_nonneg (ψ 0)).trans (hB 0)
  let S : Set ℂ := closedBall 0 R
  let T : Set (CoulombConfig N) := closedBall 0 R
  let g : ℂ → ℝ := S.indicator k
  let t : CoulombConfig N → ℝ := T.indicator (fun _ => 1)
  have hgi : Integrable g := (integrable_indicator_iff measurableSet_closedBall).mpr
    (hk.integrableOn_isCompact (isCompact_closedBall (0 : ℂ) R))
  have hti : Integrable t := by
    apply (integrable_indicator_iff measurableSet_closedBall).mpr
    exact integrableOn_const (isCompact_closedBall (0 : CoulombConfig N) R).measure_lt_top.ne
  have ht0 (y : CoulombConfig N) : 0 ≤ t y := Set.indicator_nonneg (fun _ _ => zero_le_one) y
  have hi := (hgi.norm.mul_prod hti).const_mul B
  apply hi.mono' ((hkm.comp measurable_fst).mul
    (hψ.measurable.comp (coulombInsertZero_measurable N))).aestronglyMeasurable
  filter_upwards with p
  change ‖k p.1 * ψ (coulombInsertZero p.1 p.2)‖ ≤ B * (‖g p.1‖ * t p.2)
  by_cases hz : ψ (coulombInsertZero p.1 p.2) = 0
  · simp only [hz, mul_zero, norm_zero]
    exact mul_nonneg hB0 (mul_nonneg (norm_nonneg _) (ht0 _))
  · have hfull : ‖coulombInsertZero p.1 p.2‖ ≤ R := by
      simpa only [mem_closedBall, dist_zero_right] using hsub (subset_tsupport ψ hz)
    have hsq := coulombInsertZero_norm_sq p.1 p.2
    have hx : ‖p.1‖ ≤ R := by
      nlinarith [norm_nonneg p.1, norm_nonneg p.2, norm_nonneg (coulombInsertZero p.1 p.2),
        sq_nonneg ‖p.2‖]
    have hy : ‖p.2‖ ≤ R := by
      nlinarith [norm_nonneg p.1, norm_nonneg p.2, norm_nonneg (coulombInsertZero p.1 p.2),
        sq_nonneg ‖p.1‖]
    have hxS : p.1 ∈ S := by simpa only [S, mem_closedBall, dist_zero_right] using hx
    have hyT : p.2 ∈ T := by simpa only [T, mem_closedBall, dist_zero_right] using hy
    rw [norm_mul, show g p.1 = k p.1 from Set.indicator_of_mem hxS k,
      show t p.2 = 1 from Set.indicator_of_mem hyT _, mul_one, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)

theorem cylindrical_local_integrable_test {N : ℕ} {k : ℂ → ℝ}
    (hkm : Measurable k) (hk : LocallyIntegrable k volume)
    {ψ : CoulombConfig (N + 1) → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun z : CoulombConfig (N + 1) => k (z 0) * ψ z) := by
  have h := cylindrical_local_integrable_test_prod hkm hk hψ hψc
  apply ((coulombSplitZero_measurePreserving N).symm.integrable_comp_emb
    (coulombSplitZero N).symm.measurableEmbedding).mp
  simpa only [Measure.volume_eq_prod, Function.comp_def, collision_split_symm, coulombInsertZero_zero] using h

theorem cylindrical_log_test_integrable {N : ℕ}
    {ψ : CoulombConfig (N + 1) → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun z : CoulombConfig (N + 1) => planarLogKernel (z 0) * ψ z) :=
  cylindrical_local_integrable_test (by unfold planarLogKernel; fun_prop)
    planarLogKernel_locallyIntegrable hψ hψc

theorem cylindrical_log_test_integrable_prod {N : ℕ}
    {ψ : CoulombConfig (N + 1) → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun p : ℂ × CoulombConfig N =>
      planarLogKernel p.1 * ψ (coulombInsertZero p.1 p.2)) (volume.prod volume) :=
  cylindrical_local_integrable_test_prod (by unfold planarLogKernel; fun_prop)
    planarLogKernel_locallyIntegrable hψ hψc

/-- Fubini is justified by the genuine product integrability, including tests
whose support intersects the normal collision hyperplane. -/
theorem cylindrical_log_test_integral_split {N : ℕ}
    {ψ : CoulombConfig (N + 1) → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    (∫ z : CoulombConfig (N + 1), planarLogKernel (z 0) * ψ z) =
      ∫ u : ℂ, ∫ y : CoulombConfig N, planarLogKernel u * ψ (coulombInsertZero u y) := by
  have hchange := (coulombSplitZero_measurePreserving N).symm.integral_comp
    (coulombSplitZero N).symm.measurableEmbedding
    (fun z : CoulombConfig (N + 1) => planarLogKernel (z 0) * ψ z)
  have hprod := cylindrical_log_test_integrable_prod hψ hψc
  rw [← hchange]
  simp only [collision_split_symm, coulombInsertZero_zero]
  rw [Measure.volume_eq_prod]
  exact integral_prod _ hprod

/-- Normal slices are genuine compact C2 planar tests. -/
theorem cylindrical_normal_slice_test {N : ℕ}
    {φ : CoulombConfig (N + 1) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (y : CoulombConfig N) :
    ContDiff ℝ 2 (fun u : ℂ => φ (coulombInsertZero u y)) ∧
      HasCompactSupport (fun u : ℂ => φ (coulombInsertZero u y)) :=
  ⟨hφ.comp ((coulombInsertZero_contDiff y).of_le (by simp)),
    hφc.comp_isClosedEmbedding (coulombInsertZero_isometry y).isClosedEmbedding⟩

/-- The actual planar fundamental solution on every normal slice. -/
theorem cylindrical_normal_slice_fundamental {N : ℕ}
    {φ : CoulombConfig (N + 1) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (y : CoulombConfig N) :
    Integrable (fun u : ℂ => planarLogKernel u *
      Laplacian.laplacian (fun w => φ (coulombInsertZero w y)) u) ∧
    (∫ u : ℂ, planarLogKernel u * Laplacian.laplacian
      (fun w => φ (coulombInsertZero w y)) u) =
        (-2 * Real.pi) * φ (coulombInsertZero 0 y) := by
  obtain ⟨hs, hc⟩ := cylindrical_normal_slice_test hφ hφc y
  exact log_fundamental_solution hs hc

end RepulsiveCoulomb.PaperRoute
