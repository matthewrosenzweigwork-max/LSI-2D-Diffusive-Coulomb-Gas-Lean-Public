import LeanResearch.RepulsiveCoulomb.PointLineCapNatFamily
import LeanResearch.RepulsiveCoulomb.PointLineCapPositiveOrientation
import LeanResearch.RepulsiveCoulomb.JordanFiniteCornerPointWinding
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Records-only, uncompiled. Positive winding is derived for the actual
natural-indexed mixed family. The basepoint is moved to the midpoint of its
literal last circular edge, where the right normal is outside the disk. This
closes the orientation-transfer gap without assuming a +2pi point sum. -/
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators
namespace RepulsiveCoulomb

/-- The actual finite-loop realization has its original positive circle
velocity at the midpoint of the last edge. -/
theorem lineCap_nat_circle_basepoint
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t)
    {R α β : ℝ} (hR : 0 < R) (hab : α < β)
    (hcircle : f n = pointCircleCapArc R α β) :
    let Γ := euclideanFiniteCornerLoop f n ((n : ℝ) + 1 / 2)
    Continuous Γ ∧ Function.Periodic Γ 1 ∧ InjOn Γ (Ico (0 : ℝ) 1) ∧
      DifferentiableAt ℝ Γ 0 ∧ deriv Γ 0 ≠ 0 ∧ ‖Γ 0‖ = R ∧
      deriv Γ 0 = ((n + 1 : ℝ) * (β - α)) • (Complex.I * Γ 0) ∧
      Γ '' Icc (0 : ℝ) 1 = ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 := by
  let Γ := euclideanFiniteCornerLoop f n ((n : ℝ) + 1 / 2)
  let P := pointContinuousPeriodize (euclideanFiniteCornerArc f n)
  let M : ℝ := n + 1
  let b : ℝ := ((n : ℝ) + 1 / 2) / M
  have hM : 0 < M := by dsimp [M]; positivity
  have hb : b ∈ Ioo (0 : ℝ) 1 := by
    dsimp [b]
    constructor
    · exact div_pos (by positivity) hM
    · apply (div_lt_one hM).mpr
      dsimp [M]
      linarith
  have hfc : ∀ k ≤ n, Continuous (f k) := fun k hk => (hf k hk).continuous
  obtain ⟨hP, hpP, hiP, _, himP⟩ := euclideanFiniteCornerPeriodize_properties f n hfc hv hclose hinj
  change Function.Periodic P 1 at hpP
  have hΓ : Continuous Γ := hP.comp (continuous_id.add_const b)
  have hpΓ : Function.Periodic Γ 1 := by
    intro t
    change P (t + 1 + b) = P (t + b)
    rw [show t + 1 + b = (t + b) + 1 by ring, hpP]
  have hiΓ : InjOn Γ (Ico (0 : ℝ) 1) :=
    periodic_simple_loop_shift_injOn hpP hiP (Ioo_subset_Icc_self hb)
  have hlocal : Γ =ᶠ[𝓝 (0 : ℝ)] (fun t => f n (M * t + 1 / 2)) := by
    have hclock : Tendsto (fun t : ℝ => M * t + 1 / 2) (𝓝 0) (𝓝 (1 / 2)) := by
      simpa using ((continuous_const.mul continuous_id).add_const (1 / 2 : ℝ)).tendsto 0
    filter_upwards [hclock (show Ioo (0 : ℝ) 1 ∈ 𝓝 (1 / 2 : ℝ) from
      Ioo_mem_nhds (by norm_num) (by norm_num))] with t ht
    change P (t + b) = f n (M * t + 1 / 2)
    have he : t + b = ((n : ℝ) + (M * t + 1 / 2)) / (n + 1 : ℝ) := by
      dsimp [b, M]
      field_simp
      <;> ring
    rw [he]
    exact euclideanFiniteCornerPeriodize_slot f n hfc hv hclose n le_rfl
      (M * t + 1 / 2) (Ioo_subset_Icc_self ht)
  have hbase : Γ 0 = pointCircleCapArc R α β (1 / 2) := by
    simpa only [mul_zero, zero_add, hcircle] using hlocal.self_of_nhds
  have hD : HasDerivAt Γ
      (M • ((β - α) • (Complex.I * pointCircleCapArc R α β (1 / 2)))) 0 := by
    have hlin : HasDerivAt (fun t : ℝ => M * t + 1 / 2) M 0 := by
      simpa only [id_eq, mul_one] using! ((hasDerivAt_id (0 : ℝ)).const_mul M).add_const (1 / 2)
    have hcurve : HasDerivAt (pointCircleCapArc R α β)
        ((β - α) • (Complex.I * pointCircleCapArc R α β (1 / 2))) (M * 0 + 1 / 2) := by
      simpa only [mul_zero, zero_add] using hasDerivAt_pointCircleCapArc R α β (1 / 2)
    have heq : Γ =ᶠ[𝓝 0] (fun t => pointCircleCapArc R α β (M * t + 1 / 2)) := by
      simpa only [hcircle] using hlocal
    have hcomp : HasDerivAt (fun t => pointCircleCapArc R α β (M * t + 1 / 2))
        (M • ((β - α) • (Complex.I * pointCircleCapArc R α β (1 / 2)))) 0 := by
      simpa only [Function.comp_def] using! hcurve.scomp 0 hlin
    exact hcomp.congr_of_eventuallyEq heq
  have hDne : deriv Γ 0 ≠ 0 := by
    rw [hD.deriv]
    exact smul_ne_zero hM.ne' (smul_ne_zero (sub_pos.mpr hab).ne'
      (mul_ne_zero Complex.I_ne_zero (norm_pos_iff.mp (by
        rw [pointCircleCapArc_norm hR.le]
        exact hR))))
  refine ⟨hΓ, hpΓ, hiΓ, hD.differentiableAt, hDne, ?_, ?_, ?_⟩
  · change ‖Γ 0‖ = R
    rw [hbase]
    exact pointCircleCapArc_norm hR.le α β (1 / 2)
  · change deriv Γ 0 = (M * (β - α)) • (Complex.I * Γ 0)
    rw [hD.deriv, hbase, smul_smul]
  · exact euclideanFiniteCornerLoop_image f n hfc hv hclose _

/-- The natural-index point sum is +2pi because the actual last edge runs
counterclockwise and the actual bounded region lies inside its disk. -/
theorem lineCap_nat_positive_point_sum
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t)
    {R α β : ℝ} (hR : 0 < R) (hab : α < β)
    (hcircle : f n = pointCircleCapArc R α β)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hK : IsCompact (closure U))
    (hcover : U ∪ V = (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)ᶜ)
    (hball : U ⊆ ball (0 : ℂ) R) {w : ℂ} (hw : w ∈ U)
    (Ξ : ℕ → Icc (0 : ℝ) 1 → ℝ) (hΞ : ∀ k ≤ n, Continuous (Ξ k))
    (hΞl : ∀ k ≤ n, ∀ t, Complex.exp ((Ξ k t : ℂ) * Complex.I) =
      (f k t - w) / (‖f k t - w‖ : ℂ)) :
    (∑ k ∈ Finset.range (n + 1), (Ξ k 1 - Ξ k 0)) = 2 * Real.pi := by
  let Γ := euclideanFiniteCornerLoop f n ((n : ℝ) + 1 / 2)
  obtain ⟨hΓ, hpΓ, hiΓ, hdΓ, hnΓ, hnorm, hvel, himΓ⟩ :=
    lineCap_nat_circle_basepoint f n hf hv hclose hinj hR hab hcircle
  have hcoverΓ : U ∪ V = (Γ '' Icc (0 : ℝ) 1)ᶜ := by rwa [himΓ]
  have hwC : w ∉ ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 := by
    have hwUV : w ∈ U ∪ V := Or.inl hw
    rw [hcover] at hwUV
    exact hwUV
  have havoid (t : Icc (0 : ℝ) 1) : Γ t - w ≠ 0 := by
    intro hz
    apply hwC
    rw [← himΓ]
    exact ⟨t, t.2, sub_eq_zero.mp hz⟩
  obtain ⟨Θ, hΘ, hΘl⟩ := exists_interval_euclidean_angle_lift
    ((hΓ.comp continuous_subtype_val).sub continuous_const) havoid
  have hsum := finite_corner_periodic_point_increment_sum f n
    (fun k hk => (hf k hk).continuous) hv hclose ((n : ℝ) + 1 / 2) hwC Ξ Θ hΞ hΘ hΞl hΘl
  have hpositive := lineCap_positive_inside_winding_of_circle_basepoint hΓ hdΓ hpΓ hiΓ hnΓ hR
    (mul_pos (by positivity : (0 : ℝ) < n + 1) (sub_pos.mpr hab)) hnorm hvel
    hU hUc hV hVc hK hcoverΓ hball w hw Θ hΘ hΘl
  exact hsum.trans hpositive

end RepulsiveCoulomb
