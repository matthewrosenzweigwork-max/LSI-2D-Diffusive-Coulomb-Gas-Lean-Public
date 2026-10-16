import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalExteriorDensityTails
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Actual radial-to-Cartesian derivative conversion by dilation to the unit sphere.
The norm is differentiated ONLY on the open punctured plane. The genuine
smooth planar function is used for the global dilation identity. This proves
r^n ||D^n rho(x)|| <= A_n sum_(j<=n) r^j |q^(j)(r)|, including the harmless j=0
term in Mathlib's composition estimate. Dividing gives the paper's radius
factors r^(j-n). No old all-order tail producer appears. -/
noncomputable section
open MeasureTheory Real Set Filter Metric
open scoped Topology ContDiff
namespace RepulsiveCoulomb.PaperRoute

/-- All finitely many angular norm derivatives are uniformly bounded on the
unit sphere. The bound D^j is produced from compactness, never assumed. -/
theorem thermal_norm_derivatives_sphere_bound (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ j : ℕ, 1 ≤ j → j ≤ n → ∀ θ : ℂ, ‖θ‖ = 1 →
      ‖iteratedFDerivWithin ℝ j (fun z : ℂ => ‖z‖) ({0}ᶜ) θ‖ ≤ D ^ j := by
  classical
  let s : Set ℂ := {0}ᶜ
  have hs : IsOpen s := isClosed_singleton.isOpen_compl
  have hnorm : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => ‖z‖) s := by
    intro x hx
    exact (contDiffAt_norm ℝ (by simpa only [s, mem_compl_iff, mem_singleton_iff] using hx)).contDiffWithinAt
  have hsub : sphere (0 : ℂ) 1 ⊆ s := by
    intro θ hθ
    have hn : ‖θ‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hθ
    have hne : θ ≠ 0 := by intro h; simp only [h, norm_zero] at hn; norm_num at hn
    simpa only [s, mem_compl_iff, mem_singleton_iff] using hne
  have hb : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ θ : ℂ, ‖θ‖ = 1 →
      ‖iteratedFDerivWithin ℝ j (fun z : ℂ => ‖z‖) s θ‖ ≤ B := by
    intro j
    have hc := (hnorm.continuousOn_iteratedFDerivWithin (m := j) (by simp) hs.uniqueDiffOn).mono hsub
    obtain ⟨B, hB⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn hc
    refine ⟨max 0 B, le_max_left _ _, fun θ hθ => (hB θ ?_).trans (le_max_right _ _)⟩
    simpa only [mem_sphere, dist_zero_right] using hθ
  choose B hB0 hBb using hb
  let D : ℝ := 1 + ∑ j ∈ Finset.range (n + 1), B j
  have hD : 1 ≤ D := by
    dsimp only [D]
    have hsum : 0 ≤ ∑ j ∈ Finset.range (n + 1), B j := Finset.sum_nonneg (fun j _ => hB0 j)
    linarith
  refine ⟨D, hD, fun j hj1 hjn θ hθ => ?_⟩
  have hsum : B j ≤ ∑ i ∈ Finset.range (n + 1), B i :=
    Finset.single_le_sum (fun i _ => hB0 i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hjn))
  have hjD : B j ≤ D := by dsimp only [D]; linarith
  exact (hBb j θ hθ).trans (hjD.trans (le_self_pow₀ hD (by omega)))

/-- The radial conversion with the powers kept explicit. The constant is
universal at fixed order; the hypotheses are ordinary smoothness and the
literal radial representation, not any derivative-bound certificate. -/
theorem thermal_radial_cartesian_scaled_bound (n : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (ρ : ℂ → ℝ) (q : ℝ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ρ → ContDiff ℝ (⊤ : ℕ∞) q →
      (∀ x : ℂ, ρ x = q ‖x‖) → ∀ x : ℂ, x ≠ 0 →
      ‖x‖ ^ n * ‖iteratedFDeriv ℝ n ρ x‖ ≤
        A * ∑ j ∈ Finset.range (n + 1), ‖x‖ ^ j * |iteratedDeriv j q ‖x‖| := by
  classical
  obtain ⟨D, hD1, hDb⟩ := thermal_norm_derivatives_sphere_bound n
  let A : ℝ := (n.factorial : ℝ) * D ^ n
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos n)) (pow_pos (lt_of_lt_of_le zero_lt_one hD1) _)
  refine ⟨A, hA, fun ρ q hρ hq hrad x hx => ?_⟩
  let r : ℝ := ‖x‖
  let θ : ℂ := r⁻¹ • x
  let s : Set ℂ := {0}ᶜ
  let g : ℝ → ℝ := fun t => q (r * t)
  let C : ℝ := ∑ j ∈ Finset.range (n + 1), r ^ j * |iteratedDeriv j q r|
  have hr : 0 < r := norm_pos_iff.mpr hx
  have hθ : ‖θ‖ = 1 := by
    dsimp only [θ]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_cancel₀ hr.ne'
  have hθne : θ ≠ 0 := by intro h; simp only [h, norm_zero] at hθ; norm_num at hθ
  have hθs : θ ∈ s := by simpa only [s, mem_compl_iff, mem_singleton_iff] using hθne
  have hscale : r • θ = x := by simp only [θ, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hs : IsOpen s := isClosed_singleton.isOpen_compl
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => ‖z‖) s := by
    intro y hy
    exact (contDiffAt_norm ℝ (by simpa only [s, mem_compl_iff, mem_singleton_iff] using hy)).contDiffWithinAt
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hq.comp (contDiff_const.mul contDiff_id)
  have hC : ∀ j : ℕ, j ≤ n →
      ‖iteratedFDerivWithin ℝ j g univ ‖θ‖‖ ≤ C := by
    intro j hj
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv, hθ]
    have hder := congrFun (iteratedDeriv_comp_const_mul (hq.of_le (by simp)) r (n := j)) 1
    change iteratedDeriv j g 1 = r ^ j * iteratedDeriv j q (r * 1) at hder
    rw [hder, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr.le j)]
    change r ^ j * |iteratedDeriv j q r| ≤
      ∑ i ∈ Finset.range (n + 1), r ^ i * |iteratedDeriv i q r|
    exact Finset.single_le_sum (f := fun i : ℕ => r ^ i * |iteratedDeriv i q r|)
      (fun i _ => mul_nonneg (pow_nonneg hr.le i) (abs_nonneg (iteratedDeriv i q r)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hD : ∀ j : ℕ, 1 ≤ j → j ≤ n →
      ‖iteratedFDerivWithin ℝ j (fun z : ℂ => ‖z‖) s θ‖ ≤ D ^ j :=
    fun j hj1 hjn => hDb j hj1 hjn θ hθ
  have hc := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := n)
    hg.contDiffOn hf (by simp) uniqueDiffOn_univ hs.uniqueDiffOn
    (Set.mapsTo_univ _ _) hθs hC hD
  have he : g ∘ (fun z : ℂ => ‖z‖) = (fun z : ℂ => ρ (r • z)) := by
    funext z
    rw [hrad]
    simp only [Function.comp_apply, g, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  rw [he, iteratedFDerivWithin_of_isOpen n hs hθs] at hc
  rw [congrFun (iteratedFDeriv_comp_const_smul r (hρ.of_le (by simp)) (i := n)) θ,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr.le n), hscale] at hc
  calc
    _ ≤ (n.factorial : ℝ) * C * D ^ n := hc
    _ = _ := by dsimp only [A, C, r]; ring

/-- Divided form displays the factors r^j/r^n, equal to r^(j-n) for r>0.
The j=0 summand is the harmless extra term in the general composition estimate. -/
theorem thermal_radial_cartesian_bound (n : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (ρ : ℂ → ℝ) (q : ℝ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ρ → ContDiff ℝ (⊤ : ℕ∞) q →
      (∀ x : ℂ, ρ x = q ‖x‖) → ∀ x : ℂ, x ≠ 0 →
      ‖iteratedFDeriv ℝ n ρ x‖ ≤
        A * ∑ j ∈ Finset.range (n + 1),
          (‖x‖ ^ j / ‖x‖ ^ n) * |iteratedDeriv j q ‖x‖| := by
  obtain ⟨A, hA, hb⟩ := thermal_radial_cartesian_scaled_bound n
  refine ⟨A, hA, fun ρ q hρ hq hrad x hx => ?_⟩
  have hr : 0 < ‖x‖ ^ n := pow_pos (norm_pos_iff.mpr hx) _
  apply (mul_le_mul_iff_right₀ hr).mp
  have he : ‖x‖ ^ n * (A * ∑ j ∈ Finset.range (n + 1),
      (‖x‖ ^ j / ‖x‖ ^ n) * |iteratedDeriv j q ‖x‖|) =
      A * ∑ j ∈ Finset.range (n + 1), ‖x‖ ^ j * |iteratedDeriv j q ‖x‖| := by
    rw [← mul_assoc, mul_comm (‖x‖ ^ n) A, mul_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    field_simp [hr.ne', norm_ne_zero_iff.mpr hx]
  rw [he]
  exact hb ρ q hρ hq hrad x hx

end RepulsiveCoulomb.PaperRoute
