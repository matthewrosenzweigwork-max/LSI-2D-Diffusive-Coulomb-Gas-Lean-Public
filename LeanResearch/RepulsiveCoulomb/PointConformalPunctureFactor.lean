module

public import LeanResearch.RepulsiveCoulomb.PointConformalFlatPrimitive

@[expose] public section

/-! Exact local factorization at a merged puncture. Removing every exponent at
one location leaves a smooth positive conformal density on a neighborhood of that
location, even when many original indices coincide there. This is preparation for
an actual cone-chart construction, not a replacement by a comparable model. -/
noncomputable section
open MeasureTheory Set Metric Filter InnerProductSpace
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def removePointExponents {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (p : ℂ)
    (j : Fin m) : ℝ := if y j = p then 0 else a j

theorem removePointExponents_nonneg {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) (j : Fin m) :
    0 ≤ removePointExponents a y p j := by
  unfold removePointExponents
  split_ifs
  · exact le_rfl
  · exact ha j

theorem removePointExponents_punctures {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (p : ℂ) :
    pointPunctures (removePointExponents a y p) y = pointPunctures a y \ {p} := by
  classical
  ext z
  constructor
  · rintro ⟨j, hj, hz⟩
    have hne : y j ≠ p := by intro h; simp [removePointExponents, h] at hj
    have haj : 0 < a j := by simpa [removePointExponents, hne] using hj
    exact ⟨⟨j, haj, hz⟩, fun h ↦ hne (hz.symm.trans (mem_singleton_iff.mp h))⟩
  · rintro ⟨⟨j, hj, hz⟩, hzp⟩
    have hne : y j ≠ p := fun h ↦ hzp (by simp [hz, h])
    exact ⟨j, by simpa [removePointExponents, hne] using hj, hz⟩

theorem removed_location_not_puncture {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (p : ℂ) :
    p ∉ pointPunctures (removePointExponents a y p) y := by
  rw [removePointExponents_punctures]
  simp

theorem coalescedPointExponent_eq_sum_ite {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    coalescedPointExponent a y p = ∑ j, if y j = p then a j else 0 := by
  classical
  rw [coalescedPointExponent, Finset.sum_filter]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  have hz : a j = 0 := le_antisymm (le_of_not_gt (by simpa using hj)) (ha j)
  simp [hz]

/-- Exact, including at the removed puncture. -/
theorem rawPointWeight_factor_at {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p z : ℂ) :
    rawPointWeight a y z = ‖z - p‖ ^ coalescedPointExponent a y p *
      rawPointWeight (removePointExponents a y p) y z := by
  classical
  rw [coalescedPointExponent_eq_sum_ite ha]
  rw [Real.rpow_sum_of_nonneg (norm_nonneg _) (fun j _ ↦ by split_ifs; exact ha j; exact le_rfl)]
  rw [rawPointWeight, rawPointWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : y j = p <;> simp [removePointExponents, hj]

/-- The square-root density factors with half the merged exponent. -/
theorem pointConformalDensity_factor_at {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p z : ℂ) :
    pointConformalDensity a y z = ‖z - p‖ ^ (coalescedPointExponent a y p / 2) *
      pointConformalDensity (removePointExponents a y p) y z := by
  unfold pointConformalDensity
  rw [rawPointWeight_factor_at ha, Real.sqrt_mul (Real.rpow_nonneg (norm_nonneg _) _)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  ring

/-- A harmonic regular remainder on a full disk, including the chosen location. -/
theorem exists_pointConformal_puncture_factor {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball p r) ∧
      ∀ z ∈ ball p r,
        pointConformalDensity a y z = ‖z - p‖ ^ (coalescedPointExponent a y p / 2) * Real.exp (h z) := by
  obtain ⟨r, hr, hball⟩ := exists_pointDomain_ball (removePointExponents a y p) y
    (removed_location_not_puncture a y p)
  have ha' := removePointExponents_nonneg ha y p
  refine ⟨r, hr, pointConformalLog (removePointExponents a y p) y,
    (pointConformalLog_harmonicOnNhd ha' y).mono hball, ?_⟩
  intro z hz
  rw [pointConformalDensity_factor_at ha,
    exp_pointConformalLog ha' y (hball hz)]

/-- The regular factor is the modulus of a nonvanishing holomorphic function
on a full disk containing the puncture. -/
theorem exists_pointConformal_holomorphic_puncture_factor {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball p r) ∧
      (∀ z ∈ ball p r, g z ≠ 0) ∧ ∀ z ∈ ball p r,
        pointConformalDensity a y z = ‖z - p‖ ^ (coalescedPointExponent a y p / 2) * ‖g z‖ := by
  obtain ⟨r, hr, h, hh, hfac⟩ := exists_pointConformal_puncture_factor ha y p
  obtain ⟨H, hH, hre⟩ := hh.exists_analyticOnNhd_ball_re_eq
  refine ⟨r, hr, (fun z ↦ Complex.exp (H z)), ?_, ?_, ?_⟩
  · intro z hz
    exact (hH z hz).cexp
  · intro z _
    exact Complex.exp_ne_zero _
  · intro z hz
    have he : (H z).re = h z := hre hz
    rw [Complex.norm_exp, he]
    exact hfac z hz

end RepulsiveCoulomb
