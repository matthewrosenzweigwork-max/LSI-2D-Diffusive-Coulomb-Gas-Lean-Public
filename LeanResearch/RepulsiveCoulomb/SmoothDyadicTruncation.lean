module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

@[expose] public section

/-! Genuine smooth one-sided truncations for the weak-to-strong Sobolev upgrade.
Their derivative lives in one dyadic value band, including exact endpoint zeros. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem smoothTransition_deriv_zero_outside {x : ℝ} (hx : x ∉ Ioo (0 : ℝ) 1) :
    deriv Real.smoothTransition x = 0 := by
  rcases le_or_gt x 0 with h0 | h0
  · apply IsLocalMin.deriv_eq_zero
    change ∀ᶠ z in 𝓝 x, Real.smoothTransition x ≤ Real.smoothTransition z
    filter_upwards [] with z
    rw [Real.smoothTransition.zero_of_nonpos h0]
    exact Real.smoothTransition.nonneg z
  · have h1 : 1 ≤ x := by by_contra h; exact hx ⟨h0, lt_of_not_ge h⟩
    apply IsLocalMax.deriv_eq_zero
    change ∀ᶠ z in 𝓝 x, Real.smoothTransition z ≤ Real.smoothTransition x
    filter_upwards [] with z
    rw [Real.smoothTransition.one_of_one_le h1]
    exact Real.smoothTransition.le_one z

theorem exists_smoothTransition_deriv_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, ‖deriv Real.smoothTransition x‖ ≤ K := by
  have hc : Continuous (fun x : ℝ => ‖deriv Real.smoothTransition x‖) :=
    (@Real.smoothTransition.contDiff 1).continuous_deriv_one.norm
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).bddAbove_image hc.continuousOn
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · exact (hB (mem_image_of_mem _ ⟨hx.1.le, hx.2.le⟩)).trans (le_max_left _ _)
  · rw [smoothTransition_deriv_zero_outside hx, norm_zero]
    exact le_trans zero_le_one (le_max_right _ _)

def smoothDyadicTruncation (a t : ℝ) : ℝ := a * Real.smoothTransition ((t - a) / a)

theorem smoothDyadicTruncation_contDiff (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (smoothDyadicTruncation a) := by
  unfold smoothDyadicTruncation
  simp only [div_eq_mul_inv]
  fun_prop

theorem smoothDyadicTruncation_nonneg {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    0 ≤ smoothDyadicTruncation a t := mul_nonneg ha (Real.smoothTransition.nonneg _)

theorem smoothDyadicTruncation_le {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    smoothDyadicTruncation a t ≤ a := by
  exact (mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) ha).trans_eq (mul_one a)

theorem smoothDyadicTruncation_zero {a t : ℝ} (ha : 0 < a) (ht : t ≤ a) :
    smoothDyadicTruncation a t = 0 := by
  unfold smoothDyadicTruncation
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) ha.le), mul_zero]

theorem smoothDyadicTruncation_eq_height {a t : ℝ} (ha : 0 < a) (ht : 2 * a ≤ t) :
    smoothDyadicTruncation a t = a := by
  unfold smoothDyadicTruncation
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ ha).mpr (by linarith)), mul_one]

theorem smoothDyadicTruncation_deriv {a : ℝ} (ha : 0 < a) (t : ℝ) :
    deriv (smoothDyadicTruncation a) t = deriv Real.smoothTransition ((t - a) / a) := by
  have hθ := (@Real.smoothTransition.contDiff 1).differentiable_one ((t - a) / a)
  have h := (hθ.hasDerivAt.comp t (((hasDerivAt_id t).sub_const a).div_const a)).const_mul a
  have he : a * (deriv Real.smoothTransition ((t - a) / a) * (1 / a)) =
      deriv Real.smoothTransition ((t - a) / a) := by field_simp
  change deriv (fun s : ℝ => a * Real.smoothTransition ((s - a) / a)) t = _
  simpa only [Function.comp_def, id_eq, he] using h.deriv

theorem smoothDyadicTruncation_deriv_zero_outside {a t : ℝ} (ha : 0 < a)
    (ht : t ∉ Ioo a (2 * a)) : deriv (smoothDyadicTruncation a) t = 0 := by
  rw [smoothDyadicTruncation_deriv ha t]
  apply smoothTransition_deriv_zero_outside
  intro hx
  apply ht
  refine ⟨?_, ?_⟩
  · have h := (div_pos_iff_of_pos_right ha).mp hx.1
    linarith
  · have h := (div_lt_one ha).mp hx.2
    linarith

end RepulsiveCoulomb
