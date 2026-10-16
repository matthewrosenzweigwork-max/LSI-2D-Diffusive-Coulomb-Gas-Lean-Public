module

public import LeanResearch.RepulsiveCoulomb.JordanSecantAngle
public import LeanResearch.RepulsiveCoulomb.JordanAffineTraceTangent
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Uncompiled records-only successor. Endpoint tangent direction is obtained
from ordered secants. A continuous strictly increasing source clock need NOT
be differentiable; no zero-derivative conclusion is drawn from monotonicity. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem normalized_pos_real_smul_all (z : ℂ) {r : ℝ} (hr : 0 < r) :
    (r • z) / (‖r • z‖ : ℂ) = z / (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · exact normalized_complex_smul_pos hz hr

/-- Normalized slopes agree when the two time increments have the same sign. -/
theorem normalized_slopes_of_oriented_source
    {F G : ℝ → ℂ} {s u t v : ℝ} (hsu : s ≠ u) (htv : t ≠ v)
    (hpos : 0 < (t - v) / (s - u))
    (hbase : F u = G v) (hpoint : F s = G t) :
    slope F u s / (‖slope F u s‖ : ℂ) =
      slope G v t / (‖slope G v t‖ : ℂ) := by
  have he : slope F u s = ((t - v) / (s - u)) • slope G v t := by
    simp only [slope_def_module, hbase, hpoint, smul_smul]
    congr 1
    field_simp [sub_ne_zero.mpr hsu, sub_ne_zero.mpr htv]
  rw [he, normalized_pos_real_smul_all _ hpos]

/-- Abstract filter form used at either endpoint. Both derivatives are actual
physical derivatives; normalization is compared by the same ordered chord. -/
theorem normalized_derivatives_eq_of_oriented_clock
    {ι : Type*} {l : Filter ι} [NeBot l]
    {F G : ℝ → ℂ} {u v : ℝ} {V W : ℂ} {s t : ι → ℝ}
    (hF : HasDerivAt F V u) (hG : HasDerivAt G W v)
    (hV : V ≠ 0) (hW : W ≠ 0)
    (hs : Tendsto s l (𝓝[≠] u)) (ht : Tendsto t l (𝓝[≠] v))
    (hbase : F u = G v)
    (hparam : ∀ᶠ i in l, F (s i) = G (t i))
    (horient : ∀ᶠ i in l, 0 < (t i - v) / (s i - u)) :
    V / (‖V‖ : ℂ) = W / (‖W‖ : ℂ) := by
  have hFs := hF.tendsto_slope.comp hs
  have hGs := hG.tendsto_slope.comp ht
  have hFn := hFs.div ((Complex.continuous_ofReal.tendsto ‖V‖).comp hFs.norm)
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hV))
  have hGn := hGs.div ((Complex.continuous_ofReal.tendsto ‖W‖).comp hGs.norm)
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hW))
  have hsame : (fun i => slope F u (s i) / (‖slope F u (s i)‖ : ℂ)) =ᶠ[l]
      (fun i => slope G v (t i) / (‖slope G v (t i)‖ : ℂ)) := by
    filter_upwards [hs self_mem_nhdsWithin, ht self_mem_nhdsWithin, hparam, horient]
      with i hsi hti hpi hoi
    exact normalized_slopes_of_oriented_source hsi hti hoi hbase hpi
  exact tendsto_nhds_unique hFn (hGn.congr' hsame.symm)

/-- The first endpoint of an actual increasing equal-image representative
has exactly the forward source tangent direction. -/
theorem oriented_clock_initial_tangent
    {F G : ℝ → ℂ} {τ : ℝ → ℝ}
    (hτ : Continuous τ) (hmono : StrictMonoOn τ (Icc (0 : ℝ) 1))
    (hparam : EqOn F (G ∘ τ) (Icc (0 : ℝ) 1))
    (hF : DifferentiableAt ℝ F 0) (hG : DifferentiableAt ℝ G (τ 0))
    (hV : deriv F 0 ≠ 0) (hW : deriv G (τ 0) ≠ 0) :
    deriv F 0 / (‖deriv F 0‖ : ℂ) = deriv G (τ 0) / (‖deriv G (τ 0)‖ : ℂ) := by
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with s hs hs1
    exact ⟨hs, hs1⟩
  have ht : Tendsto τ (𝓝[>] (0 : ℝ)) (𝓝[>] (τ 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(hτ.tendsto 0).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [hsmall] with s hs
    exact hmono (by norm_num) (Ioo_subset_Icc_self hs) hs.1
  apply normalized_derivatives_eq_of_oriented_clock hF.hasDerivAt hG.hasDerivAt hV hW
    (tendsto_id.mono_right (nhdsGT_le_nhdsNE 0)) (ht.mono_right (nhdsGT_le_nhdsNE (τ 0)))
    (hparam (by norm_num))
  · filter_upwards [hsmall] with s hs
    exact hparam (Ioo_subset_Icc_self hs)
  · filter_upwards [hsmall] with s hs
    exact div_pos (sub_pos.mpr (hmono (by norm_num) (Ioo_subset_Icc_self hs) hs.1))
      (by simpa using hs.1)

/-- At the final endpoint both source and representative secants approach
from below, so their signed time quotient is still positive. -/
theorem oriented_clock_final_tangent
    {F G : ℝ → ℂ} {τ : ℝ → ℝ}
    (hτ : Continuous τ) (hmono : StrictMonoOn τ (Icc (0 : ℝ) 1))
    (hparam : EqOn F (G ∘ τ) (Icc (0 : ℝ) 1))
    (hF : DifferentiableAt ℝ F 1) (hG : DifferentiableAt ℝ G (τ 1))
    (hV : deriv F 1 ≠ 0) (hW : deriv G (τ 1) ≠ 0) :
    deriv F 1 / (‖deriv F 1‖ : ℂ) = deriv G (τ 1) / (‖deriv G (τ 1)‖ : ℂ) := by
  have hsmall : ∀ᶠ s : ℝ in 𝓝[<] 1, s ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with s hs hs0
    exact ⟨hs0, hs⟩
  have ht : Tendsto τ (𝓝[<] (1 : ℝ)) (𝓝[<] (τ 1)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(hτ.tendsto 1).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [hsmall] with s hs
    exact hmono (Ioo_subset_Icc_self hs) (by norm_num) hs.2
  apply normalized_derivatives_eq_of_oriented_clock hF.hasDerivAt hG.hasDerivAt hV hW
    (tendsto_id.mono_right (nhdsLT_le_nhdsNE 1)) (ht.mono_right (nhdsLT_le_nhdsNE (τ 1)))
    (hparam (by norm_num))
  · filter_upwards [hsmall] with s hs
    exact hparam (Ioo_subset_Icc_self hs)
  · filter_upwards [hsmall] with s hs
    exact div_pos_of_neg_of_neg (sub_neg.mpr (hmono (Ioo_subset_Icc_self hs) (by norm_num) hs.2))
      (sub_neg.mpr hs.2)

end RepulsiveCoulomb
