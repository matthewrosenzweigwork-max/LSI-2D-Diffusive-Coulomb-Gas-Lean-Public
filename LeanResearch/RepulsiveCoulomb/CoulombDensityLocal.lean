module

public import LeanResearch.RepulsiveCoulomb.CoulombCollisionNull

@[expose] public section

/-! Actual normalized particle density, null-set equivalence and compact
comparison away from collisions. Constants here may depend on N,beta,K. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem coulombPartition_eq_ofReal_integral {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    coulombPartition N β = ENNReal.ofReal (∫ z : CoulombConfig N, coulombWeight β z) :=
  (ofReal_integral_eq_lintegral_ofReal (coulombWeight_integrable hβ)
    (Eventually.of_forall (coulombWeight_nonneg β))).symm

theorem coulombWeight_integral_pos {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    0 < ∫ z : CoulombConfig N, coulombWeight β z := by
  have h := coulombPartition_pos (N := N) hβ
  rw [coulombPartition_eq_ofReal_integral hβ] at h
  exact ENNReal.ofReal_pos.mp h

def coulombDensity (N : ℕ) (β : ℝ) (z : CoulombConfig N) : ℝ :=
  (∫ w : CoulombConfig N, coulombWeight β w)⁻¹ * coulombWeight β z

theorem coulombDensity_continuous {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) : Continuous (coulombDensity N β) :=
  (coulombWeight_continuous hβ).const_mul _

theorem coulombDensity_nonneg {N : ℕ} (β : ℝ) (z : CoulombConfig N) : 0 ≤ coulombDensity N β z :=
  mul_nonneg (inv_nonneg.mpr (integral_nonneg (coulombWeight_nonneg β))) (coulombWeight_nonneg β z)

theorem coulombDensity_pos_off_collisions {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) : 0 < coulombDensity N β z :=
  mul_pos (inv_pos.mpr (coulombWeight_integral_pos hβ)) (coulombWeight_pos_off_collisions β z hz)

theorem coulombDensity_pos_ae {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    ∀ᵐ z : CoulombConfig N, 0 < coulombDensity N β z := by
  filter_upwards [coulombDomain_ae N] with z hz
  exact coulombDensity_pos_off_collisions hβ hz

theorem coulombMeasure_eq_withDensity {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    coulombMeasure N β = volume.withDensity (fun z => ENNReal.ofReal (coulombDensity N β z)) := by
  have hZ := coulombWeight_integral_pos (N := N) hβ
  rw [coulombMeasure, coulombPartition_eq_ofReal_integral hβ,
    ← withDensity_smul _ (coulombWeight_continuous hβ.le).measurable.ennreal_ofReal]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, coulombDensity,
    ENNReal.ofReal_mul (inv_pos.mpr hZ).le, ENNReal.ofReal_inv_of_pos hZ]

theorem coulombMeasure_ae_iff {N : ℕ} {β : ℝ} (hβ : 0 < β) {P : CoulombConfig N → Prop} :
    (∀ᵐ z ∂coulombMeasure N β, P z) ↔ ∀ᵐ z : CoulombConfig N, P z := by
  rw [coulombMeasure_eq_withDensity hβ,
    ae_withDensity_iff (coulombDensity_continuous hβ.le).measurable.ennreal_ofReal]
  constructor
  · intro h
    filter_upwards [h, coulombDensity_pos_ae hβ] with z hz hp
    exact hz (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
  · intro h
    filter_upwards [h] with z hz
    exact fun _ => hz

theorem coulombDensity_bounds_on_compact {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (havoid : K ⊆ coulombDomain N) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z ∈ K, c ≤ coulombDensity N β z ∧ coulombDensity N β z ≤ C := by
  by_cases hne : K.Nonempty
  · obtain ⟨zmin, hzmin, hmin⟩ := hK.exists_isMinOn hne (coulombDensity_continuous hβ.le).continuousOn
    obtain ⟨zmax, hzmax, hmax⟩ := hK.exists_isMaxOn hne (coulombDensity_continuous hβ.le).continuousOn
    refine ⟨coulombDensity N β zmin, coulombDensity N β zmax,
      coulombDensity_pos_off_collisions hβ (havoid hzmin),
      coulombDensity_pos_off_collisions hβ (havoid hzmax), ?_⟩
    intro z hz
    exact ⟨hmin hz, hmax hz⟩
  · refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro z hz
    exact (hne ⟨z, hz⟩).elim

theorem coulombMeasure_restrict_comparison {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (havoid : K ⊆ coulombDomain N) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ENNReal.ofReal c • volume.restrict K ≤ (coulombMeasure N β).restrict K ∧
      (coulombMeasure N β).restrict K ≤ ENNReal.ofReal C • volume.restrict K := by
  obtain ⟨c, C, hc, hC, hb⟩ := coulombDensity_bounds_on_compact hβ hK havoid
  refine ⟨c, C, hc, hC, ?_, ?_⟩
  · rw [coulombMeasure_eq_withDensity hβ, restrict_withDensity hK.isClosed.measurableSet, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
    exact ENNReal.ofReal_le_ofReal (hb z hz).1
  · rw [coulombMeasure_eq_withDensity hβ, restrict_withDensity hK.isClosed.measurableSet, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
    exact ENNReal.ofReal_le_ofReal (hb z hz).2

end RepulsiveCoulomb
