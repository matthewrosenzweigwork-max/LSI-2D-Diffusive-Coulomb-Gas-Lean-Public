module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalRadialCartesianConversion

@[expose] public section

/-! Complete transfer of the NEW exterior profile tails to all Cartesian Frechet
orders, followed by the actual compact-unit-disk estimate. The exponent is
exactly beta+n throughout. -/
noncomputable section
open MeasureTheory Real Set Filter Metric
open scoped Topology ContDiff
namespace RepulsiveCoulomb.PaperRoute

/-- On r>=1, every radius factor r^j/r^n is <=1 for j<=n. -/
theorem thermal_cartesian_exterior_tails_of_profile
    {ρ : ℂ → ℝ} {q : ℝ → ℝ} {β : ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hrad : ∀ x : ℂ, ρ x = q ‖x‖)
    (htail : ∀ j : ℕ, ThermalExteriorTail q β j) (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℂ, 1 ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ n ρ x‖ ≤ B * thermalExteriorWeight β n ‖x‖ := by
  classical
  obtain ⟨A, hA, hAb⟩ := thermal_radial_cartesian_bound n
  have hc : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      |iteratedDeriv j q r| ≤ C * thermalExteriorWeight β j r := htail
  choose C hC hCb using hc
  let S : ℝ := ∑ j ∈ Finset.range (n + 1), C j
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => (hC j).le)
  refine ⟨A * S + 1, by positivity, fun x hx => ?_⟩
  have hx0 : x ≠ 0 := by intro h; subst x; norm_num at hx
  have hn : 0 < ‖x‖ ^ n := pow_pos (lt_of_lt_of_le zero_lt_one hx) _
  have hW0 := (thermalExteriorWeight_pos β n hx).le
  have hs : (∑ j ∈ Finset.range (n + 1),
      (‖x‖ ^ j / ‖x‖ ^ n) * |iteratedDeriv j q ‖x‖|) ≤
        S * thermalExteriorWeight β n ‖x‖ := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1), C j * thermalExteriorWeight β n ‖x‖ := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
        have hfactor : ‖x‖ ^ j / ‖x‖ ^ n ≤ 1 :=
          (div_le_one hn).mpr (pow_le_pow_right₀ hx hjn)
        calc
          _ ≤ 1 * |iteratedDeriv j q ‖x‖| :=
            mul_le_mul_of_nonneg_right hfactor (abs_nonneg _)
          _ ≤ C j * thermalExteriorWeight β j ‖x‖ := by simpa only [thermalExteriorWeight, one_mul] using hCb j ‖x‖ hx
          _ ≤ _ := mul_le_mul_of_nonneg_left (thermalExteriorWeight_mono β hjn hx) (hC j).le
      _ = _ := by dsimp only [S]; rw [Finset.sum_mul]
  calc
    _ ≤ A * ∑ j ∈ Finset.range (n + 1),
        (‖x‖ ^ j / ‖x‖ ^ n) * |iteratedDeriv j q ‖x‖| := hAb ρ q hρ hq hrad x hx0
    _ ≤ A * (S * thermalExteriorWeight β n ‖x‖) := mul_le_mul_of_nonneg_left hs hA.le
    _ ≤ _ := by nlinarith

/-- The exact Gaussian-polynomial weight is bounded below on the unit disk. -/
theorem thermalExteriorWeight_lower_on_unitBall {β : ℝ} (hβ : 0 < β)
    (n : ℕ) {x : ℂ} (hx : ‖x‖ ≤ 1) :
    Real.exp (-β / 2) ≤ thermalExteriorWeight β n ‖x‖ := by
  have hp : 1 ≤ (1 + ‖x‖) ^ (β + (n : ℝ)) :=
    Real.one_le_rpow (by linarith [norm_nonneg x]) (by positivity)
  have he : Real.exp (-β / 2) ≤ Real.exp (-β * ‖x‖ ^ 2 / 2) := by
    apply Real.exp_le_exp.mpr
    have hs : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    nlinarith
  exact (by simpa only [thermalExteriorWeight, one_mul] using
    mul_le_mul hp he (Real.exp_pos _).le (by positivity : 0 ≤ (1 + ‖x‖) ^ (β + (n : ℝ))))

/-- Actual compact derivative boundedness handles the origin and the unit disk;
no extension of the norm through zero is used. -/
theorem thermal_cartesian_tails_of_profile
    {ρ : ℂ → ℝ} {q : ℝ → ℝ} {β : ℝ} (hβ : 0 < β)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hrad : ∀ x : ℂ, ρ x = q ‖x‖)
    (htail : ∀ j : ℕ, ThermalExteriorTail q β j) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℂ,
      ‖iteratedFDeriv ℝ n ρ x‖ ≤
        C * (1 + ‖x‖) ^ (β + (n : ℝ)) * Real.exp (-β * ‖x‖ ^ 2 / 2) := by
  obtain ⟨B, hB, hBbound⟩ := thermal_cartesian_exterior_tails_of_profile hρ hq hrad htail n
  have hd : Continuous (iteratedFDeriv ℝ n ρ) := hρ.continuous_iteratedFDeriv (by simp)
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hd.continuousOn
  let I : ℝ := max 0 L * Real.exp (β / 2)
  let C : ℝ := max B I + 1
  have hC : 0 < C := by
    have h : B ≤ max B I := le_max_left _ _
    dsimp only [C]
    linarith
  refine ⟨C, hC, fun x => ?_⟩
  have hWpos : 0 < thermalExteriorWeight β n ‖x‖ := by
    unfold thermalExteriorWeight
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)
  have hfinal : ‖iteratedFDeriv ℝ n ρ x‖ ≤ C * thermalExteriorWeight β n ‖x‖ := by
    by_cases hx : 1 ≤ ‖x‖
    · exact (hBbound x hx).trans (mul_le_mul_of_nonneg_right
        (by dsimp only [C]; linarith [le_max_left B I]) hWpos.le)
    · have hx1 : ‖x‖ ≤ 1 := (lt_of_not_ge hx).le
      have hxin : x ∈ closedBall (0 : ℂ) 1 := by simpa only [mem_closedBall, dist_zero_right] using hx1
      have he : I * Real.exp (-β / 2) = max 0 L := by
        dsimp only [I]
        rw [mul_assoc, ← Real.exp_add]
        have hz : β / 2 + -β / 2 = 0 := by ring
        rw [hz, Real.exp_zero, mul_one]
      have hI0 : 0 ≤ I := by dsimp only [I]; positivity
      have hIl : max 0 L ≤ I * thermalExteriorWeight β n ‖x‖ := by
        rw [← he]
        exact mul_le_mul_of_nonneg_left (thermalExteriorWeight_lower_on_unitBall hβ n hx1) hI0
      exact ((hL x hxin).trans (le_max_right _ _)).trans (hIl.trans
        (mul_le_mul_of_nonneg_right
          (by dsimp only [C]; linarith [le_max_right B I]) hWpos.le))
  simpa only [thermalExteriorWeight, mul_assoc] using hfinal

/-- New raw-input thermal density endpoint. Its smoothness and zeroth-order
EL envelope may be supplied by the NEW minimizer branch; every higher tail is
produced here through the literal radial-profile argument. -/
theorem thermal_actual_density_cartesian_tails
    {ρ : ℂ → ℝ} {β C M K : ℝ} (hβ : 0 < β)
    (hρm : Measurable ρ) (hρpos : ∀ x, 0 < ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y)
    (hEL : ∀ x, Real.log (ρ x) =
      -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C)
    (hρsmooth : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hUsmooth : ContDiff ℝ (⊤ : ℕ∞) (equilibriumDensityPotential ρ))
    (hK : 0 < K)
    (htail : ∀ x, ρ x ≤ K * (1 + ‖x‖) ^ β * Real.exp (-β * ‖x‖ ^ 2 / 2)) :
    ∀ n : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ x : ℂ,
      ‖iteratedFDeriv ℝ n ρ x‖ ≤
        A * (1 + ‖x‖) ^ (β + (n : ℝ)) * Real.exp (-β * ‖x‖ ^ 2 / 2) := by
  have hq := thermalDensityProfile_contDiff hρsmooth
  have hrad : ∀ x : ℂ, ρ x = thermalDensityProfile ρ ‖x‖ := by
    intro x
    apply hρrad
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
  have hp := thermal_actual_density_profile_tails hβ hρm hρpos hρM hρi hρmass hρ2
    hρrad hEL hρsmooth hUsmooth hK htail
  have hp' : ∀ n : ℕ, ThermalExteriorTail (thermalDensityProfile ρ) β n := by
    intro n
    obtain ⟨A, hA, hb⟩ := hp n
    exact ⟨A, hA, fun r hr => by simpa only [thermalExteriorWeight, mul_assoc] using hb r hr⟩
  exact fun n => thermal_cartesian_tails_of_profile hβ hρsmooth hq hrad hp' n

end RepulsiveCoulomb.PaperRoute
