import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalExteriorProfiles

/-! Differentiating r*u'=-M produces the exact radial recurrence, then exterior
potential-derivative bounds using only the lower density derivatives specified
in canonical.tex. No inverse-power extension through zero is differentiated. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology ContDiff
namespace RepulsiveCoulomb.PaperRoute

/-- A convenient actual derivative API for a smooth real profile. -/
theorem thermal_hasDerivAt_iteratedDeriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (r : ℝ) :
    HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f r) r := by
  rw [iteratedDeriv_succ]
  exact (hf.differentiable_iteratedDeriv n (by exact_mod_cast ENat.natCast_lt_top n) r).hasDerivAt

/-- The two surviving terms of Leibniz for multiplication by the radius. -/
theorem thermal_iteratedDeriv_radius_mul_succ {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (r : ℝ) :
    iteratedDeriv (n + 1) (fun s => s * f s) r =
      r * iteratedDeriv (n + 1) f r + (n + 1 : ℕ) * iteratedDeriv n f r := by
  induction n generalizing r with
  | zero =>
    have hd := (hasDerivAt_id r).mul (thermal_hasDerivAt_iteratedDeriv hf 0 r)
    simpa only [Nat.zero_add, iteratedDeriv_zero, iteratedDeriv_one, Nat.cast_one, one_mul,
      mul_one, add_comm, Pi.mul_def, id_eq] using hd.deriv
  | succ n ih =>
    have he : iteratedDeriv (n + 1) (fun s => s * f s) =
        fun r => r * iteratedDeriv (n + 1) f r +
          (n + 1 : ℕ) * iteratedDeriv n f r := funext ih
    rw [show n.succ + 1 = (n + 1) + 1 by omega, iteratedDeriv_succ, he]
    have hd := ((hasDerivAt_id r).mul (thermal_hasDerivAt_iteratedDeriv hf (n + 1) r)).add
      ((thermal_hasDerivAt_iteratedDeriv hf n r).const_mul (n + 1 : ℝ))
    simp only [Pi.add_def, Pi.mul_def, id_eq, Nat.cast_add, Nat.cast_one] at hd ⊢
    rw [hd.deriv]
    ring

theorem thermal_iteratedDeriv_radius_mul {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (r : ℝ) :
    iteratedDeriv n (fun s => s * f s) r =
      r * iteratedDeriv n f r + (n : ℝ) * iteratedDeriv (n - 1) f r := by
  cases n with
  | zero => simp only [iteratedDeriv_zero, Nat.cast_zero, zero_mul, add_zero]
  | succ n => simpa only [Nat.succ_sub_one] using thermal_iteratedDeriv_radius_mul_succ hf n r

/-- Exact mass derivatives, including n=0 without an undefined negative order:
the coefficient of the Nat-truncated lower order is then zero. -/
theorem thermalMassProfile_iteratedDeriv {q : ℝ → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (n : ℕ) (r : ℝ) :
    iteratedDeriv (n + 1) (thermalMassProfile q) r =
      2 * Real.pi * (r * iteratedDeriv n q r +
        (n : ℝ) * iteratedDeriv (n - 1) q r) := by
  rw [iteratedDeriv_succ', thermalMassProfile_deriv hq.continuous,
    iteratedDeriv_const_mul_field, thermal_iteratedDeriv_radius_mul hq]

/-- The only equality differentiated is valid on the OPEN positive ray. -/
theorem thermal_potential_profile_derivative_recurrence {q u : ℝ → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hNewton : EqOn (fun r => r * deriv u r)
      (fun r => -thermalMassProfile q r) (Ioi 0))
    (n : ℕ) {r : ℝ} (hr : 0 < r) :
    r * iteratedDeriv (n + 2) u r +
      (n + 1 : ℕ) * iteratedDeriv (n + 1) u r =
      -(2 * Real.pi * (r * iteratedDeriv n q r +
        (n : ℝ) * iteratedDeriv (n - 1) q r)) := by
  have h := hNewton.iteratedDeriv_of_isOpen isOpen_Ioi (n + 1) hr
  have hdu : ContDiff ℝ (⊤ : ℕ∞) (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  rw [thermal_iteratedDeriv_radius_mul_succ hdu, iteratedDeriv_fun_neg,
    thermalMassProfile_iteratedDeriv hq] at h
  simpa only [← iteratedDeriv_succ', Nat.add_assoc] using h

/-- Exterior uniform bounds are explicit existential real constants, rather
than an assumed all-order certificate. -/
def ThermalExteriorDerivativeBound (f : ℝ → ℝ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → |iteratedDeriv n f r| ≤ C

/-- For u^(n+1), only density orders j<n are supplied. Thus u^k needs q only
through k-2, with the k=1 base using enclosed mass alone. -/
theorem thermal_exterior_potential_derivatives_bounded {q u : ℝ → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hNewton : EqOn (fun r => r * deriv u r)
      (fun r => -thermalMassProfile q r) (Ioi 0))
    (hmass : ∀ r : ℝ, 1 ≤ r → 0 ≤ thermalMassProfile q r ∧ thermalMassProfile q r ≤ 1)
    (n : ℕ) (hb : ∀ j : ℕ, j < n → ThermalExteriorDerivativeBound q j) :
    ThermalExteriorDerivativeBound u (n + 1) := by
  revert hb
  induction n with
  | zero =>
    intro hb
    refine ⟨1, zero_le_one, fun r hr => ?_⟩
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have h := congrArg abs (hNewton hr0)
    rw [abs_mul, abs_of_pos hr0, abs_neg, abs_of_nonneg (hmass r hr).1] at h
    rw [iteratedDeriv_one]
    have hl : |deriv u r| ≤ r * |deriv u r| := by
      nlinarith [abs_nonneg (deriv u r)]
    exact hl.trans (h.le.trans (hmass r hr).2)
  | succ n ih =>
    intro hb
    obtain ⟨U, hU0, hU⟩ := ih (fun j hj => hb j (by omega))
    obtain ⟨A, hA0, hA⟩ := hb n (by omega)
    obtain ⟨B, hB0, hB⟩ := hb (n - 1) (by omega)
    let C : ℝ := (n + 1 : ℕ) * U + 2 * Real.pi * (A + (n : ℝ) * B)
    have hC0 : 0 ≤ C := by dsimp [C]; positivity
    refine ⟨C, hC0, fun r hr => ?_⟩
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hrec := thermal_potential_profile_derivative_recurrence hq hu hNewton n hr0
    have he : r * iteratedDeriv (n + 2) u r =
        -((n + 1 : ℕ) * iteratedDeriv (n + 1) u r) -
          2 * Real.pi * (r * iteratedDeriv n q r +
            (n : ℝ) * iteratedDeriv (n - 1) q r) := by linarith
    have hraw : r * |iteratedDeriv (n + 2) u r| ≤
        (n + 1 : ℕ) * U + 2 * Real.pi * (r * A + (n : ℝ) * B) := by
      calc
        _ = |r * iteratedDeriv (n + 2) u r| := by rw [abs_mul, abs_of_pos hr0]
        _ = |-((n + 1 : ℕ) * iteratedDeriv (n + 1) u r) -
            2 * Real.pi * (r * iteratedDeriv n q r +
              (n : ℝ) * iteratedDeriv (n - 1) q r)| := congrArg abs he
        _ ≤ |(n + 1 : ℕ) * iteratedDeriv (n + 1) u r| +
            |2 * Real.pi * (r * iteratedDeriv n q r +
              (n : ℝ) * iteratedDeriv (n - 1) q r)| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
            (-((n + 1 : ℕ) * iteratedDeriv (n + 1) u r))
            (-(2 * Real.pi * (r * iteratedDeriv n q r +
              (n : ℝ) * iteratedDeriv (n - 1) q r)))
        _ ≤ (n + 1 : ℕ) * U + 2 * Real.pi * (r * A + (n : ℝ) * B) := by
          simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by positivity),
            abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
          apply add_le_add (mul_le_mul_of_nonneg_left (hU r hr) (by positivity))
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            _ ≤ |r * iteratedDeriv n q r| + |(n : ℝ) * iteratedDeriv (n - 1) q r| := abs_add_le _ _
            _ = r * |iteratedDeriv n q r| + (n : ℝ) * |iteratedDeriv (n - 1) q r| := by
              rw [abs_mul, abs_mul, abs_of_pos hr0, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity)]
            _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hA r hr) hr0.le)
              (mul_le_mul_of_nonneg_left (hB r hr) (Nat.cast_nonneg n))
    have hscale : (n + 1 : ℕ) * U + 2 * Real.pi * (r * A + (n : ℝ) * B) ≤ r * C := by
      dsimp only [C]
      have h1 := mul_nonneg (sub_nonneg.mpr hr)
        (show 0 ≤ (n + 1 : ℕ) * U by positivity)
      have h2 := mul_nonneg (sub_nonneg.mpr hr)
        (show 0 ≤ 2 * Real.pi * (n : ℝ) * B by positivity)
      nlinarith
    exact (mul_le_mul_iff_right₀ hr0).mp (hraw.trans hscale)

end RepulsiveCoulomb.PaperRoute
