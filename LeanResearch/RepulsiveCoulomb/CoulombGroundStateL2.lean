import LeanResearch.RepulsiveCoulomb.CoulombGroundStateEnergy

/-! The actual normalized ground-state map as a real L2 linear isometry.
No dependent cast of an Lp element is used. -/
noncomputable section
open MeasureTheory Filter
open PeriodicAttractiveLogGas
namespace RepulsiveCoulomb

theorem coulombGroundState_memLp {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Lp ℝ 2 (coulombMeasure N β)) :
    MemLp (fun z : CoulombConfig N => Real.sqrt (coulombDensity N β z) * u z) 2 volume := by
  have htransport (f : CoulombConfig N → ℝ) (hf : Integrable f (coulombMeasure N β)) :
      Integrable f (volume.withDensity (fun z => ENNReal.ofReal (coulombDensity N β z))) := by
    rw [← coulombMeasure_eq_withDensity hβ]
    exact hf
  have hu := htransport (fun z => u z ^ 2) (Lp.memLp u).integrable_sq
  have hw := (integrable_withDensity_iff_integrable_smul'
    (coulombDensity_continuous hβ.le).measurable.ennreal_ofReal
    (Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))).mp hu
  have hi : Integrable (fun z : CoulombConfig N => coulombDensity N β z * u z ^ 2) := by
    simpa only [ENNReal.toReal_ofReal (coulombDensity_nonneg (N := N) β _), smul_eq_mul] using hw
  have hs : AEStronglyMeasurable
      (fun z : CoulombConfig N => Real.sqrt (coulombDensity N β z) * u z) volume :=
    (((coulombDensity_continuous hβ.le).sqrt).stronglyMeasurable.mul (Lp.stronglyMeasurable u)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hs).mpr
  convert! hi using 1
  funext z
  rw [mul_pow, Real.sq_sqrt (coulombDensity_nonneg β z)]

def coulombGroundStateL2Fun {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Lp ℝ 2 (coulombMeasure N β)) : Lp ℝ 2 (volume : Measure (CoulombConfig N)) :=
  (coulombGroundState_memLp hβ u).toLp _

theorem coulombGroundStateL2Fun_coe {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Lp ℝ 2 (coulombMeasure N β)) :
    coulombGroundStateL2Fun hβ u =ᵐ[volume]
      fun z : CoulombConfig N => Real.sqrt (coulombDensity N β z) * u z :=
  (coulombGroundState_memLp hβ u).coeFn_toLp

theorem coulombGroundStateL2Fun_add {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u v : Lp ℝ 2 (coulombMeasure N β)) :
    coulombGroundStateL2Fun hβ (u + v) = coulombGroundStateL2Fun hβ u + coulombGroundStateL2Fun hβ v := by
  apply Lp.ext
  filter_upwards [coulombGroundStateL2Fun_coe hβ (u + v), coulombGroundStateL2Fun_coe hβ u,
    coulombGroundStateL2Fun_coe hβ v,
    Lp.coeFn_add (coulombGroundStateL2Fun hβ u) (coulombGroundStateL2Fun hβ v),
    (coulombMeasure_ae_iff hβ).mp (Lp.coeFn_add u v)] with z hsum hu hv hr hs
  simp only [Pi.add_apply] at hr hs
  rw [hsum, hr, hu, hv, hs]
  ring

theorem coulombGroundStateL2Fun_smul {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (c : ℝ) (u : Lp ℝ 2 (coulombMeasure N β)) :
    coulombGroundStateL2Fun hβ (c • u) = c • coulombGroundStateL2Fun hβ u := by
  apply Lp.ext
  filter_upwards [coulombGroundStateL2Fun_coe hβ (c • u), coulombGroundStateL2Fun_coe hβ u,
    Lp.coeFn_smul c (coulombGroundStateL2Fun hβ u),
    (coulombMeasure_ae_iff hβ).mp (Lp.coeFn_smul c u)] with z hl hu hr hs
  simp only [Pi.smul_apply] at hr hs
  rw [hl, hr, hu, hs]
  simp only [smul_eq_mul]
  ring

theorem coulombGroundStateL2Fun_norm {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Lp ℝ 2 (coulombMeasure N β)) : ‖coulombGroundStateL2Fun hβ u‖ = ‖u‖ := by
  have he : ‖coulombGroundStateL2Fun hβ u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [← integral_sq_eq_L2_norm_sq, ← integral_sq_eq_L2_norm_sq]
    calc
      _ = ∫ z : CoulombConfig N, (Real.sqrt (coulombDensity N β z) * u z) ^ 2 :=
        integral_congr_ae ((coulombGroundStateL2Fun_coe hβ u).mono (fun z hz => congrArg (fun t : ℝ => t ^ 2) hz))
      _ = ∫ z : CoulombConfig N, coulombDensity N β z * u z ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          dsimp only
          rw [mul_pow, Real.sq_sqrt (coulombDensity_nonneg β z)]
      _ = _ := (coulombMeasure_integral_density_of_integrable hβ _ (Lp.memLp u).integrable_sq).symm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

def coulombGroundStateL2 {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    Lp ℝ 2 (coulombMeasure N β) →ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (CoulombConfig N)) where
  toFun := coulombGroundStateL2Fun hβ
  map_add' := coulombGroundStateL2Fun_add hβ
  map_smul' c u := by simpa only [RingHom.id_apply] using coulombGroundStateL2Fun_smul hβ c u
  norm_map' := coulombGroundStateL2Fun_norm hβ

theorem coulombGroundStateL2_coe {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Lp ℝ 2 (coulombMeasure N β)) :
    coulombGroundStateL2 hβ u =ᵐ[volume]
      fun z : CoulombConfig N => Real.sqrt (coulombDensity N β z) * u z :=
  coulombGroundStateL2Fun_coe hβ u

end RepulsiveCoulomb
