module

public import LeanResearch.RepulsiveCoulomb.CoulombOneSiteRawIntegral

@[expose] public section

/-! The actual normalized first-site conditional law and marginal. Frozen
collisions are allowed; no possibly zero frozen density is ever canceled. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RepulsiveCoulomb

def coulombOneSiteMarginalDensity (N : ℕ) (β : ℝ) (y : CoulombConfig N) : ℝ≥0∞ :=
  (coulombPartition (N + 1) β)⁻¹ *
    ENNReal.ofReal (coulombWeightAtExponent β (β / ((N + 1 : ℕ) : ℝ)) y) *
    pointPartition β (fun _ : Fin N => β / ((N + 1 : ℕ) : ℝ)) (fun j => y j)

def coulombOneSiteMarginal (N : ℕ) (β : ℝ) : Measure (CoulombConfig N) :=
  volume.withDensity (coulombOneSiteMarginalDensity N β)

theorem coulombOneSiteMarginalDensity_measurable {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) :
    Measurable (coulombOneSiteMarginalDensity N β) := by
  have ha : 0 ≤ β / ((N + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  exact (measurable_const.mul (coulombWeightAtExponent_continuous β ha).measurable.ennreal_ofReal).mul
    (pointPartition_measurable_config β (fun _ : Fin N => ha))

theorem coulomb_one_site_tower {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F : CoulombConfig (N + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z ∂coulombMeasure (N + 1) β) =
      ∫⁻ y : CoulombConfig N,
        (∫⁻ w : ℂ, F (coulombInsertZero w y) ∂pointMeasure β
          (fun _ : Fin N => β / ((N + 1 : ℕ) : ℝ)) (fun j => y j)) ∂coulombOneSiteMarginal N β := by
  let a : Fin N → ℝ := fun _ => β / ((N + 1 : ℕ) : ℝ)
  have ha : ∀ j, 0 ≤ a j := fun _ => div_nonneg hβ.le (Nat.cast_nonneg _)
  have hjoint : Measurable (fun p : CoulombConfig N × ℂ => F (coulombInsertZero p.2 p.1)) :=
    hF.comp ((coulombInsertZero_measurable N).comp measurable_swap)
  have hcond := pointMeasure_lintegral_parameter β ha hjoint
  rw [coulombMeasure, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul volume (coulombWeight_continuous hβ.le).measurable.ennreal_ofReal hF]
  change (coulombPartition (N + 1) β)⁻¹ *
      (∫⁻ z, ENNReal.ofReal (coulombWeight β z) * F z) = _
  rw [coulomb_raw_one_site_lintegral hβ.le hF, coulombOneSiteMarginal,
    lintegral_withDensity_eq_lintegral_mul volume (coulombOneSiteMarginalDensity_measurable hβ.le) hcond]
  rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (coulombPartition_pos (N := N + 1) hβ).ne')]
  apply lintegral_congr
  intro y
  have hslice : Measurable (fun w : ℂ => F (coulombInsertZero w y)) :=
    hF.comp ((coulombInsertZero_measurable N).comp measurable_prodMk_right)
  change (coulombPartition (N + 1) β)⁻¹ *
      (ENNReal.ofReal (coulombWeightAtExponent β (β / ((N + 1 : ℕ) : ℝ)) y) *
        ∫⁻ w : ℂ, ENNReal.ofReal (pointWeight β a (fun j => y j) w) * F (coulombInsertZero w y)) =
      coulombOneSiteMarginalDensity N β y * (∫⁻ w : ℂ, F (coulombInsertZero w y) ∂pointMeasure β a (fun j => y j))
  rw [pointMeasure_lintegral β a (fun j => y j) hslice]
  have hc := ENNReal.mul_inv_cancel (pointPartition_pos β a (fun j => y j)).ne'
    (pointPartition_lt_top hβ ha (fun j => y j)).ne
  unfold coulombOneSiteMarginalDensity
  change _ = ((coulombPartition (N + 1) β)⁻¹ *
      ENNReal.ofReal (coulombWeightAtExponent β (β / ((N + 1 : ℕ) : ℝ)) y) * pointPartition β a (fun j => y j)) * _
  calc
    _ = ((coulombPartition (N + 1) β)⁻¹ * ENNReal.ofReal (coulombWeightAtExponent β (β / ((N + 1 : ℕ) : ℝ)) y)) *
        (pointPartition β a (fun j => y j) * (pointPartition β a (fun j => y j))⁻¹) *
        (∫⁻ w : ℂ, ENNReal.ofReal (pointWeight β a (fun j => y j) w) * F (coulombInsertZero w y)) := by
      rw [hc, mul_one]
      ac_rfl
    _ = _ := by ac_rfl

theorem coulombOneSiteMarginal_isProbability {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (coulombOneSiteMarginal N β) := by
  let _ := coulombMeasure_isProbability (N := N + 1) hβ
  have h := coulomb_one_site_tower (N := N) hβ (F := fun _ => 1) measurable_const
  have hfiber (y : CoulombConfig N) : (∫⁻ _w : ℂ, (1 : ℝ≥0∞) ∂pointMeasure β
      (fun _ : Fin N => β / ((N + 1 : ℕ) : ℝ)) (fun j => y j)) = 1 := by
    let _ := pointMeasure_isProbability hβ (fun _ : Fin N => div_nonneg hβ.le (Nat.cast_nonneg (N + 1))) (fun j => y j)
    simp only [lintegral_one, measure_univ]
  simp_rw [hfiber] at h
  constructor
  simpa only [lintegral_one, measure_univ] using h.symm

end RepulsiveCoulomb
