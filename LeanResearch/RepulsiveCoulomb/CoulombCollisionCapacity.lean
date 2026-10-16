import LeanResearch.RepulsiveCoulomb.CoulombFirstCollisionCapacity
import LeanResearch.RepulsiveCoulomb.CoulombAllPairsSwap
import LeanResearch.RepulsiveCoulomb.PointCutoffApproximation

/-! Actual smooth cutoffs and vanishing weighted energy for every collision pair. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

def coulombCollisionProjection {N : ℕ} (i j : Fin N) : CoulombConfig N →L[ℝ] ℂ :=
  (Real.sqrt 2)⁻¹ • (coulombCoordinate i - coulombCoordinate j)

def coulombCollisionBump {N : ℕ} (i j : Fin N) (ε : ℝ) (hε : 0 < ε) : CoulombConfig N → ℝ :=
  fun z => pointCutoffBump 0 ε hε (coulombCollisionProjection i j z)

theorem coulombCollisionBump_contDiff {N : ℕ} (i j : Fin N) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (coulombCollisionBump i j ε hε) :=
  (pointCutoffBump 0 ε hε).contDiff.comp (coulombCollisionProjection i j).contDiff

theorem coulombCollisionBump_nonneg {N : ℕ} (i j : Fin N) (ε : ℝ) (hε : 0 < ε) (z : CoulombConfig N) :
    0 ≤ coulombCollisionBump i j ε hε z := (pointCutoffBump 0 ε hε).nonneg

theorem coulombCollisionBump_le_one {N : ℕ} (i j : Fin N) (ε : ℝ) (hε : 0 < ε) (z : CoulombConfig N) :
    coulombCollisionBump i j ε hε z ≤ 1 := (pointCutoffBump 0 ε hε).le_one

theorem coulombCollisionBump_one {N : ℕ} (i j : Fin N) (ε : ℝ) (hε : 0 < ε) {z : CoulombConfig N}
    (hz : ‖coulombCollisionProjection i j z‖ ≤ ε) :
    coulombCollisionBump i j ε hε z = 1 :=
  pointCutoffBump_one 0 ε hε (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)

theorem coulombCollisionBump_eq_first_permute {N : ℕ} (i j : Fin (N + 2)) (σ : Equiv.Perm (Fin (N + 2)))
    (h0 : σ 0 = i) (h1 : σ (Fin.succ 0) = j) (ε : ℝ) (hε : 0 < ε) :
    coulombCollisionBump i j ε hε = fun z => coulombFirstCollisionBump N ε hε (coulombPermute σ z) := by
  funext z
  change pointCutoffBump 0 ε hε ((Real.sqrt 2)⁻¹ • (z i - z j)) =
    pointCutoffBump 0 ε hε ((Real.sqrt 2)⁻¹ • (coulombPermute σ z 0 - coulombPermute σ z (Fin.succ 0)))
  rw [coulombPermute_apply, coulombPermute_apply, h0, h1]

theorem coulombCollisionBump_gradient_norm_permute {N : ℕ} (i j : Fin (N + 2)) (σ : Equiv.Perm (Fin (N + 2)))
    (h0 : σ 0 = i) (h1 : σ (Fin.succ 0) = j) (ε : ℝ) (hε : 0 < ε) (z : CoulombConfig (N + 2)) :
    ‖gradient (coulombCollisionBump i j ε hε) z‖ =
      ‖gradient (coulombFirstCollisionBump N ε hε) (coulombPermute σ z)‖ := by
  rw [coulombCollisionBump_eq_first_permute i j σ h0 h1]
  rw [gradient_comp_linearIsometryEquiv (coulombPermute σ) (f := coulombFirstCollisionBump N ε hε) z
    ((coulombFirstCollisionBump_contDiff N ε hε).differentiable (by simp) _),
    (coulombPermute σ).symm.norm_map]

theorem coulombCollisionBump_energy_eq_first {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (i j : Fin (N + 2)) (hij : i ≠ j) (ε : ℝ) (hε : 0 < ε) :
    (∫ z, ‖gradient (coulombCollisionBump i j ε hε) z‖ ^ 2 ∂coulombMeasure (N + 2) β) =
      ∫ z, ‖gradient (coulombFirstCollisionBump N ε hε) z‖ ^ 2 ∂coulombMeasure (N + 2) β := by
  obtain ⟨σ, h0, h1⟩ := exists_coulomb_pair_permutation i j hij
  simp_rw [coulombCollisionBump_gradient_norm_permute i j σ h0 h1]
  exact (coulombPermute_gibbs_preserving hβ.le σ).integral_comp
    (coulombPermute σ).toMeasurableEquiv.measurableEmbedding
      (fun z => ‖gradient (coulombFirstCollisionBump N ε hε) z‖ ^ 2)

theorem coulombCollisionBump_energy_integrable {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (i j : Fin (N + 2)) (hij : i ≠ j) (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun z => ‖gradient (coulombCollisionBump i j ε hε) z‖ ^ 2)
      (coulombMeasure (N + 2) β) := by
  let _ := coulombMeasure_isProbability (N := N + 2) hβ
  obtain ⟨σ, h0, h1⟩ := exists_coulomb_pair_permutation i j hij
  obtain ⟨B, hB, hb⟩ := exists_pointCutoffBump_gradient_bound
  have hc : Continuous (gradient (coulombCollisionBump i j ε hε)) :=
    ((coulombCollisionBump_contDiff i j ε hε).gradient_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  have hm : MemLp (gradient (coulombCollisionBump i j ε hε)) 2 (coulombMeasure (N + 2) β) :=
    MemLp.of_bound hc.aestronglyMeasurable (B / ε) (Eventually.of_forall (fun z => by
      rw [coulombCollisionBump_gradient_norm_permute i j σ h0 h1, coulombFirstCollisionBump_gradient_norm]
      exact hb 0 ε hε _))
  exact hm.norm.integrable_sq

theorem coulombCollisionBump_energy_bound (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ K : ℝ, 0 < K ∧ ∀ (i j : Fin (N + 2)), i ≠ j → ∀ (ε : ℝ) (hε : 0 < ε),
      (∫ z, ‖gradient (coulombCollisionBump i j ε hε) z‖ ^ 2 ∂coulombMeasure (N + 2) β) ≤
        K * ε ^ (β / ((N + 2 : ℕ) : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := coulombFirstCollisionBump_energy_bound N hβ
  refine ⟨K, hK, ?_⟩
  intro i j hij ε hε
  rw [coulombCollisionBump_energy_eq_first hβ i j hij]
  exact hb ε hε

theorem coulombCollisionBump_energy_tendsto_zero {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (i j : Fin (N + 2)) (hij : i ≠ j) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, ‖gradient (coulombCollisionBump i j (ε n) (hε n)) z‖ ^ 2
      ∂coulombMeasure (N + 2) β) atTop (𝓝 0) := by
  simp_rw [coulombCollisionBump_energy_eq_first hβ i j hij]
  exact coulombFirstCollisionBump_energy_tendsto_zero N hβ ε hε hlim

theorem coulombCollisionBump_tendsto_zero_off_collision {N : ℕ} (i j : Fin N)
    (z : CoulombConfig N) (hz : z i ≠ z j) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => coulombCollisionBump i j (ε n) (hε n) z) atTop (𝓝 0) := by
  have hn : coulombCollisionProjection i j z ≠ 0 :=
    smul_ne_zero (inv_ne_zero (Real.sqrt_pos.2 (by norm_num)).ne') (sub_ne_zero.mpr hz)
  exact pointCutoff_tendsto_zero_off_center 0 (coulombCollisionProjection i j z) hn ε hε hlim

end RepulsiveCoulomb

