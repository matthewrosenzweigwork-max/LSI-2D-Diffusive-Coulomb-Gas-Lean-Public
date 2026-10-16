module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalExteriorPotentialBounds
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchPolynomialGaussian

@[expose] public section

/-! The actual exterior real-profile induction. Lower q tails give finite sup bounds;
NEW potential recurrence bounds the higher derivatives of r+u'; Leibniz applied
to q'=-beta*(r+u')*q gives the exact exponent beta+n. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology ContDiff
namespace RepulsiveCoulomb.PaperRoute

def thermalExteriorWeight (β : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  (1 + r) ^ (β + (n : ℝ)) * Real.exp (-β * r ^ 2 / 2)

def ThermalExteriorTail (q : ℝ → ℝ) (β : ℝ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
    |iteratedDeriv n q r| ≤ C * thermalExteriorWeight β n r

theorem thermalExteriorWeight_pos (β : ℝ) (n : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    0 < thermalExteriorWeight β n r := by
  exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.exp_pos _)

theorem thermalExteriorWeight_mono (β : ℝ) {m n : ℕ} (hmn : m ≤ n)
    {r : ℝ} (hr : 1 ≤ r) : thermalExteriorWeight β m r ≤ thermalExteriorWeight β n r := by
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply Real.rpow_le_rpow_of_exponent_le (by linarith)
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  linarith

theorem thermalExteriorWeight_succ (β : ℝ) (n : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    thermalExteriorWeight β (n + 1) r = (1 + r) * thermalExteriorWeight β n r := by
  unfold thermalExteriorWeight
  rw [Nat.cast_add, Nat.cast_one, ← add_assoc,
    Real.rpow_add (by linarith : 0 < 1 + r), Real.rpow_one]
  ring

theorem thermalExteriorWeight_eq_polynomialGaussian (β : ℝ) (n : ℕ)
    {r : ℝ} (hr : 0 ≤ r) :
    thermalExteriorWeight β n r =
      equilibriumPolynomialGaussian (β + (n : ℝ)) (β / 2) (r : ℂ) := by
  unfold thermalExteriorWeight equilibriumPolynomialGaussian
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  congr 2
  ring

/-- This is a scalar Gaussian absorption lemma, not a thermal derivative input. -/
theorem thermalExteriorWeight_uniform_bound {β : ℝ} (hβ : 0 < β)
    (n : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    thermalExteriorWeight β n r ≤ Real.exp ((β + (n : ℝ)) ^ 2 / β) := by
  rw [thermalExteriorWeight_eq_polynomialGaussian β n (by linarith)]
  have h := equilibriumPolynomialGaussian_bound
    (by positivity : 0 ≤ β + (n : ℝ)) (half_pos hβ) (r : ℂ)
  have he : Real.exp (-(β / 2 / 2) * ‖(r : ℂ)‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have hb : 0 < β / 2 / 2 := by positivity
      nlinarith [sq_nonneg ‖(r : ℂ)‖])
  have hh := h.trans (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)
  simpa only [mul_one, show 2 * (β / 2) = β by ring] using hh

theorem ThermalExteriorTail.derivativeBound {q : ℝ → ℝ} {β : ℝ} {n : ℕ}
    (h : ThermalExteriorTail q β n) (hβ : 0 < β) : ThermalExteriorDerivativeBound q n := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C * Real.exp ((β + (n : ℝ)) ^ 2 / β), by positivity, fun r hr => ?_⟩
  exact (hbound r hr).trans
    (mul_le_mul_of_nonneg_left (thermalExteriorWeight_uniform_bound hβ n hr) hC.le)

def thermalRadialScore (u : ℝ → ℝ) (r : ℝ) : ℝ := r + deriv u r

theorem thermalRadialScore_contDiff {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (thermalRadialScore u) :=
  contDiff_id.add (contDiff_infty_iff_deriv.mp hu).2

theorem thermalConfinementProfile_deriv {u : ℝ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    deriv (thermalConfinementProfile u) = thermalRadialScore u := by
  funext r
  have hd := (((hasDerivAt_id r).pow 2).div_const 2).add
    ((hu.differentiable (by simp) r).hasDerivAt)
  change HasDerivAt (thermalConfinementProfile u) _ r at hd
  change deriv (thermalConfinementProfile u) r = r + deriv u r
  rw [hd.deriv]
  norm_num


/-- The zeroth score grows at most linearly; enclosed mass supplies the constant 1. -/
theorem thermalRadialScore_abs_le {q u : ℝ → ℝ}
    (hNewton : EqOn (fun r => r * deriv u r)
      (fun r => -thermalMassProfile q r) (Ioi 0))
    (hmass : ∀ r : ℝ, 1 ≤ r → 0 ≤ thermalMassProfile q r ∧ thermalMassProfile q r ≤ 1)
    {r : ℝ} (hr : 1 ≤ r) : |thermalRadialScore u r| ≤ 1 + r := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have h := congrArg abs (hNewton hr0)
  rw [abs_mul, abs_of_pos hr0, abs_neg, abs_of_nonneg (hmass r hr).1] at h
  have hdu : |deriv u r| ≤ 1 := by
    have hl : |deriv u r| ≤ r * |deriv u r| := by nlinarith [abs_nonneg (deriv u r)]
    exact hl.trans (h.le.trans (hmass r hr).2)
  exact (abs_add_le r (deriv u r)).trans (by rw [abs_of_pos hr0]; linarith)

/-- Positive-order score derivatives are UNIFORMLY bounded. The weaker common
linear envelope in the next lemma is only for convenient finite-sum assembly. -/
theorem thermalRadialScore_derivative_bound {q u : ℝ → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hNewton : EqOn (fun r => r * deriv u r)
      (fun r => -thermalMassProfile q r) (Ioi 0))
    (hmass : ∀ r : ℝ, 1 ≤ r → 0 ≤ thermalMassProfile q r ∧ thermalMassProfile q r ≤ 1)
    {j : ℕ} (hj : 0 < j)
    (hb : ∀ i : ℕ, i < j → ThermalExteriorDerivativeBound q i) :
    ThermalExteriorDerivativeBound (thermalRadialScore u) j := by
  obtain ⟨C, hC0, hC⟩ := thermal_exterior_potential_derivatives_bounded hq hu hNewton hmass j hb
  refine ⟨1 + C, by positivity, fun r hr => ?_⟩
  have hdu : ContDiff ℝ (⊤ : ℕ∞) (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have he : iteratedDeriv j (thermalRadialScore u) r =
      iteratedDeriv j (fun s : ℝ => s) r + iteratedDeriv (j + 1) u r := by
    change iteratedDeriv j (fun s : ℝ => s + deriv u s) r = _
    have hduj : ContDiff ℝ j (deriv u) :=
      hdu.of_le (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))
    have hadd := iteratedDeriv_fun_add (f := fun s : ℝ => s) (g := deriv u)
      (n := j) (x := r) contDiff_id.contDiffAt hduj.contDiffAt
    simpa only [← iteratedDeriv_succ'] using hadd
  rw [he]
  have hid : |iteratedDeriv j (fun s : ℝ => s) r| ≤ 1 := by
    simp only [iteratedDeriv_fun_id, ite_eq_right (Nat.ne_of_gt hj)]
    split_ifs <;> norm_num
  exact (abs_add_le _ _).trans (add_le_add hid (hC r hr))

/-- A common factor (1+r) applies to each coefficient derivative through n,
with every coefficient derived from lower q bounds by the preceding theorem. -/
theorem thermalRadialScore_derivative_linear_bound {q u : ℝ → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hNewton : EqOn (fun r => r * deriv u r)
      (fun r => -thermalMassProfile q r) (Ioi 0))
    (hmass : ∀ r : ℝ, 1 ≤ r → 0 ≤ thermalMassProfile q r ∧ thermalMassProfile q r ≤ 1)
    (j : ℕ) (hb : ∀ i : ℕ, i < j → ThermalExteriorDerivativeBound q i) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 1 ≤ r →
      |iteratedDeriv j (thermalRadialScore u) r| ≤ A * (1 + r) := by
  by_cases hj : j = 0
  · subst j
    refine ⟨1, zero_le_one, fun r hr => ?_⟩
    simpa only [iteratedDeriv_zero, one_mul] using thermalRadialScore_abs_le hNewton hmass hr
  · obtain ⟨A, hA0, hA⟩ := thermalRadialScore_derivative_bound hq hu hNewton hmass
      (Nat.pos_of_ne_zero hj) hb
    refine ⟨A, hA0, fun r hr => (hA r hr).trans ?_⟩
    nlinarith

/-- One genuine derivative step; prior tails are only induction information. -/
theorem thermal_exterior_density_tail_step {q u : ℝ → ℝ} {β : ℝ} (hβ : 0 < β)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hNewton : EqOn (fun r => r * deriv u r)
      (fun r => -thermalMassProfile q r) (Ioi 0))
    (hmass : ∀ r : ℝ, 1 ≤ r → 0 ≤ thermalMassProfile q r ∧ thermalMassProfile q r ≤ 1)
    (hscore : deriv q = fun r => -β * (thermalRadialScore u r * q r))
    (n : ℕ) (hprior : ∀ j : ℕ, j ≤ n → ThermalExteriorTail q β j) :
    ThermalExteriorTail q β (n + 1) := by
  classical
  have hc : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
      (j ≤ n → ∀ r : ℝ, 1 ≤ r → |iteratedDeriv j q r| ≤ C * thermalExteriorWeight β j r) := by
    intro j
    by_cases hj : j ≤ n
    · obtain ⟨C, hC, hb⟩ := hprior j hj
      exact ⟨C, hC, fun _ => hb⟩
    · exact ⟨1, zero_lt_one, fun h => (hj h).elim⟩
  choose C hCpos hCb using hc
  have ha : ∀ j : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      (j ≤ n → ∀ r : ℝ, 1 ≤ r →
        |iteratedDeriv j (thermalRadialScore u) r| ≤ A * (1 + r)) := by
    intro j
    by_cases hj : j ≤ n
    · obtain ⟨A, hA, hb⟩ := thermalRadialScore_derivative_linear_bound hq hu hNewton hmass j
        (fun i hi => (hprior i (by omega)).derivativeBound hβ)
      exact ⟨A, hA, fun _ => hb⟩
    · exact ⟨0, le_rfl, fun h => (hj h).elim⟩
  choose A hA0 hAb using ha
  let S : ℝ := ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * A j * C (n - j)
  have hS0 : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA0 j)) (hCpos (n - j)).le
  refine ⟨β * S + 1, by positivity, fun r hr => ?_⟩
  have hW0 := (thermalExteriorWeight_pos β (n + 1) hr).le
  have hasmooth := thermalRadialScore_contDiff hu
  have hformula : iteratedDeriv (n + 1) q r =
      -β * ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * iteratedDeriv j (thermalRadialScore u) r *
          iteratedDeriv (n - j) q r := by
    rw [iteratedDeriv_succ', hscore, iteratedDeriv_const_mul_field,
      iteratedDeriv_fun_mul (hasmooth.contDiffAt.of_le (by simp))
        (hq.contDiffAt.of_le (by simp))]
  rw [hformula, abs_mul, abs_neg, abs_of_pos hβ]
  have hs : |∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * iteratedDeriv j (thermalRadialScore u) r *
          iteratedDeriv (n - j) q r| ≤ S * thermalExteriorWeight β (n + 1) r := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1),
          |(n.choose j : ℝ) * iteratedDeriv j (thermalRadialScore u) r *
            iteratedDeriv (n - j) q r| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : ℝ) * A j * C (n - j)) * thermalExteriorWeight β (n + 1) r := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
        have hnj : n - j ≤ n := Nat.sub_le _ _
        have hqle : |iteratedDeriv (n - j) q r| ≤ C (n - j) * thermalExteriorWeight β n r :=
          (hCb (n - j) hnj r hr).trans
            (mul_le_mul_of_nonneg_left (thermalExteriorWeight_mono β hnj hr) (hCpos _).le)
        calc
          _ = (n.choose j : ℝ) * |iteratedDeriv j (thermalRadialScore u) r| *
              |iteratedDeriv (n - j) q r| := by
            simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (n.choose j : ℝ) by positivity)]
          _ ≤ ((n.choose j : ℝ) * (A j * (1 + r))) *
              (C (n - j) * thermalExteriorWeight β n r) := by
            apply mul_le_mul
              (mul_le_mul_of_nonneg_left (hAb j hjn r hr) (Nat.cast_nonneg _)) hqle
              (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (hA0 j) (by linarith)))
          _ = _ := by rw [thermalExteriorWeight_succ β n hr]; ring
      _ = _ := by dsimp only [S]; rw [Finset.sum_mul]
  have h := mul_le_mul_of_nonneg_left hs hβ.le
  have hlast : β * (S * thermalExteriorWeight β (n + 1) r) ≤
      (β * S + 1) * thermalExteriorWeight β (n + 1) r := by nlinarith
  exact h.trans hlast

/-- Strong induction supplies precisely the previously proved real-profile tails. -/
theorem thermal_exterior_density_tails {q u : ℝ → ℝ} {β : ℝ} (hβ : 0 < β)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hNewton : EqOn (fun r => r * deriv u r)
      (fun r => -thermalMassProfile q r) (Ioi 0))
    (hmass : ∀ r : ℝ, 1 ≤ r → 0 ≤ thermalMassProfile q r ∧ thermalMassProfile q r ≤ 1)
    (hscore : deriv q = fun r => -β * (thermalRadialScore u r * q r))
    (hzero : ThermalExteriorTail q β 0) :
    ∀ n : ℕ, ThermalExteriorTail q β n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact hzero
    | succ n =>
      exact thermal_exterior_density_tail_step hβ hq hu hNewton hmass hscore n
        (fun j hj => ih j (by omega))

/-- Concrete supplied-density specialization: the sole tail input is the already
proved zeroth-order EL envelope. All higher real-profile tails are generated
by the preceding Newton/Leibniz induction. -/
theorem thermal_actual_density_profile_tails
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
    ∀ n : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 1 ≤ r →
      |iteratedDeriv n (thermalDensityProfile ρ) r| ≤
        A * (1 + r) ^ (β + (n : ℝ)) * Real.exp (-β * r ^ 2 / 2) := by
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hρpos x).le
  have hUrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ →
      equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y := by
    intro x y hxy
    have h := congrArg Real.log (hρrad hxy)
    rw [hEL x, hEL y, hxy] at h
    apply mul_left_cancel₀ hβ.ne'
    linarith
  have hq := thermalDensityProfile_contDiff hρsmooth
  have hu := thermalPotentialProfile_contDiff hUsmooth
  have hNewton := thermalPotentialProfile_mul_deriv
    hρm hρ0 hρM hρi hρmass hρ2 hρrad hUrad
  have hmass : ∀ r : ℝ, 1 ≤ r →
      0 ≤ thermalMassProfile (thermalDensityProfile ρ) r ∧
        thermalMassProfile (thermalDensityProfile ρ) r ≤ 1 :=
    fun r hr => thermalMassProfile_mem_unitInterval hρm hρ0 hρi hρmass hρrad (by linarith)
  have hscore : deriv (thermalDensityProfile ρ) = fun r =>
      -β * (thermalRadialScore (thermalPotentialProfile ρ) r * thermalDensityProfile ρ r) := by
    rw [thermalDensityProfile_deriv_score hρpos hEL hUsmooth,
      thermalConfinementProfile_deriv hu]
    funext r
    ring
  have hzero : ThermalExteriorTail (thermalDensityProfile ρ) β 0 := by
    refine ⟨K, hK, fun r hr => ?_⟩
    have h := htail (r : ℂ)
    simpa only [iteratedDeriv_zero, thermalDensityProfile, abs_of_pos (hρpos (r : ℂ)),
      thermalExteriorWeight, Nat.cast_zero, add_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ r by linarith), mul_assoc] using h
  intro n
  obtain ⟨A, hA, hb⟩ := thermal_exterior_density_tails hβ hq hu hNewton hmass hscore hzero n
  exact ⟨A, hA, fun r hr => by simpa only [thermalExteriorWeight, mul_assoc] using hb r hr⟩

end RepulsiveCoulomb.PaperRoute
