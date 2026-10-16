/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; see Imported/TauCeti/LICENSE.
Authors of the original covering argument: The Tau Ceti contributors

The Vitali selection argument below is adapted from the frozen attributed
Imported/TauCeti/MeasureTheory/Integral/MaximalFunction.lean,
TauCeti.mul_measure_le_of_forall_exists_ball. This generic version replaces Haar scaling by the supplied global doubling
constant, through the newly proved closed-fourfold bound D cubed. The upstream Haar
hypothesis is neither erased nor applied to a non-Haar measure; its frozen
source and PROVENANCE.json remain unchanged.
-/
import LeanResearch.RepulsiveCoulomb.PaperRoute.GenericDoublingSobolevBasics
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual global weak (1,1) control, from the supplied global D only.
No null-sphere premise and no assumed maximal-function certificate occurs. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem GlobalDoublingWith.vitali_weak_bound {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D)
    {S : Set ℂ} {R : ℝ} {g : ℂ → ℝ≥0∞} {t : ℝ≥0∞}
    (hS : ∀ x ∈ S, ∃ r ∈ Ioc (0 : ℝ) R,
      t * μ (ball x r) ≤ ∫⁻ z in ball x r, g z ∂μ) :
    t * μ S ≤
      ENNReal.ofReal (D ^ 3) * ∫⁻ z, g z ∂μ := by
  classical
  choose! r hr hle using hS
  obtain ⟨u, hu, hdisj, hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall S id r R
      (fun x hx => (hr x hx).2) 4 (by norm_num)
  simp only [id_eq] at hdisj hcov
  have hcount : u.Countable :=
    hdisj.countable_of_nonempty_interior fun x hx =>
      ⟨x, ball_subset_interior_closedBall (mem_ball_self (hr x (hu hx)).1)⟩
  let : Countable u := hcount.to_subtype
  have hsub : S ⊆ ⋃ b ∈ u, closedBall b (4 * r b) := fun x hx => by
    obtain ⟨b, hb, hball⟩ := hcov x hx
    exact mem_biUnion hb (hball (mem_closedBall_self (hr x hx).1.le))
  have hdisj' : Pairwise (Function.onFun Disjoint fun b : u => ball (b : ℂ) (r b)) :=
    fun b b' hbb' =>
      (hdisj b.2 b'.2 (Subtype.coe_injective.ne hbb')).mono ball_subset_closedBall ball_subset_closedBall
  calc
    t * μ S ≤ t * ∑' b : u, μ (closedBall (b : ℂ) (4 * r b)) := by
      apply mul_le_mul' le_rfl
      exact (measure_mono hsub).trans (measure_biUnion_le μ hcount _)
    _ = ∑' b : u, t * μ (closedBall (b : ℂ) (4 * r b)) := ENNReal.tsum_mul_left.symm
    _ ≤ ∑' b : u, ENNReal.ofReal (D ^ 3) * ∫⁻ z in ball (b : ℂ) (r b), g z ∂μ := by
      apply ENNReal.tsum_le_tsum
      intro b
      calc
        _ ≤ t * (ENNReal.ofReal (D ^ 3) * μ (ball (b : ℂ) (r b))) :=
          mul_le_mul' le_rfl (hD.closedBall_four_le b (hr b (hu b.2)).1)
        _ = ENNReal.ofReal (D ^ 3) * (t * μ (ball (b : ℂ) (r b))) := by ac_rfl
        _ ≤ _ := mul_le_mul' le_rfl (hle b (hu b.2))
    _ = ENNReal.ofReal (D ^ 3) * ∑' b : u, ∫⁻ z in ball (b : ℂ) (r b), g z ∂μ :=
      ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (D ^ 3) * ∫⁻ z in ⋃ b : u, ball (b : ℂ) (r b), g z ∂μ := by
      rw [lintegral_iUnion (fun b => measurableSet_ball) hdisj']
    _ ≤ _ := mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)


/-- Countable maximal operator with radii 10 R 2⁻ⁿ, on the actual measure. -/
def doublingDyadicMaximal (μ : Measure ℂ) (R : ℝ) (g : ℂ → ℝ≥0∞) (x : ℂ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨍⁻ z in ball x (doublingDyadicRadius R n), g z ∂μ

theorem GlobalDoublingWith.dyadicMaximal_weak_bound {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) {R : ℝ} (hR : 0 < R)
    (g : ℂ → ℝ≥0∞) (t : ℝ≥0∞) :
    t * μ {x | t < doublingDyadicMaximal μ R g x} ≤
      ENNReal.ofReal (D ^ 3) * ∫⁻ z, g z ∂μ := by
  apply hD.vitali_weak_bound (R := 10 * R)
  intro x hx
  change t < ⨆ n : ℕ, ⨍⁻ z in ball x (doublingDyadicRadius R n), g z ∂μ at hx
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hx
  refine ⟨doublingDyadicRadius R n,
    ⟨doublingDyadicRadius_pos hR n, doublingDyadicRadius_le_ten hR n⟩, ?_⟩
  rw [setLAverage_eq] at hn
  exact (ENNReal.mul_lt_of_lt_div hn).le

theorem PositiveFiniteBalls.dyadicMaximal_le_of_bound {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) {R : ℝ} (hR : 0 < R)
    {g : ℂ → ℝ≥0∞} {b : ℝ≥0∞} (hb : ∀ z, g z ≤ b) (x : ℂ) :
    doublingDyadicMaximal μ R g x ≤ b := by
  apply iSup_le
  intro n
  calc
    _ ≤ ⨍⁻ _ in ball x (doublingDyadicRadius R n), b ∂μ :=
      laverage_mono_ae (Filter.Eventually.of_forall hb)
    _ = b := setLAverage_const (hμ x _ (doublingDyadicRadius_pos hR n)).1.ne'
      (hμ x _ (doublingDyadicRadius_pos hR n)).2.ne b

/-- Cut off the energy on the physical outer ball, before taking a GLOBAL maximal operator. -/
def doublingLocalMaximalEnergy (μ : Measure ℂ) (c : ℂ) (R : ℝ)
    (g : ℂ → ℝ) (x : ℂ) : ℝ≥0∞ :=
  doublingDyadicMaximal μ R ((ball c (11 * R)).indicator (fun z => ENNReal.ofReal (g z))) x

theorem PositiveFiniteBalls.localMaximalEnergy_lt_top {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) (c : ℂ) {R : ℝ} (hR : 0 < R)
    {g : ℂ → ℝ} (hg : Continuous g) (x : ℂ) :
    doublingLocalMaximalEnergy μ c R g x < ⊤ := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall c (11 * R)).bddAbove_image hg.continuousOn
  apply (hμ.dyadicMaximal_le_of_bound hR (b := ENNReal.ofReal B) ?_ x).trans_lt
    ENNReal.ofReal_lt_top
  intro z
  by_cases hz : z ∈ ball c (11 * R)
  · rw [Set.indicator_of_mem hz]
    exact ENNReal.ofReal_le_ofReal (hB (mem_image_of_mem g (ball_subset_closedBall hz)))
  · rw [Set.indicator_of_notMem hz]
    exact bot_le

theorem GlobalDoublingWith.localMaximalEnergy_weak_bound {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (g : ℂ → ℝ) (t : ℝ≥0∞) :
    t * μ {x | t < doublingLocalMaximalEnergy μ c R g x} ≤
      ENNReal.ofReal (D ^ 3) * ∫⁻ z in ball c (11 * R), ENNReal.ofReal (g z) ∂μ := by
  simpa only [doublingLocalMaximalEnergy, lintegral_indicator measurableSet_ball] using
    hD.dyadicMaximal_weak_bound hR
      ((ball c (11 * R)).indicator (fun z => ENNReal.ofReal (g z))) t

theorem PositiveFiniteBalls.localMaximalEnergy_average_bound {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) {c x : ℂ} {R : ℝ} (hR : 0 < R)
    (hx : x ∈ ball c R) (g : ℂ → ℝ) (hg : Continuous g)
    (hgn : ∀ z, 0 ≤ g z) (n : ℕ) :
    (⨍ z in ball x (doublingDyadicRadius R n), g z ∂μ) ≤
      (doublingLocalMaximalEnergy μ c R g x).toReal := by
  have he : (⨍⁻ z in ball x (doublingDyadicRadius R n),
      (ball c (11 * R)).indicator (fun w => ENNReal.ofReal (g w)) z ∂μ) =
      ⨍⁻ z in ball x (doublingDyadicRadius R n), ENNReal.ofReal (g z) ∂μ := by
    apply laverage_congr
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact Set.indicator_of_mem (doublingDyadicBall_subset_outer hR hx n hz) _
  have h : ENNReal.ofReal (⨍ z in ball x (doublingDyadicRadius R n), g z ∂μ) ≤
      doublingLocalMaximalEnergy μ c R g x := by
    rw [ofReal_setAverage (hμ.continuous_ball_integrable hg x _) (Eventually.of_forall hgn)]
    rw [← setLAverage_eq, ← he]
    exact le_iSup (fun k => ⨍⁻ z in ball x (doublingDyadicRadius R k),
      (ball c (11 * R)).indicator (fun w => ENNReal.ofReal (g w)) z ∂μ) n
  have ht := ENNReal.toReal_mono (hμ.localMaximalEnergy_lt_top c hR hg x).ne h
  simpa only [ENNReal.toReal_ofReal (average_nonneg hgn)] using ht


/-- Positive finite balls supply the sigma-finiteness needed by parameter integration. -/
theorem PositiveFiniteBalls.measurable_ball_mass {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) (r : ℝ) :
    Measurable (fun c : ℂ => μ (ball c r)) := by
  let : IsLocallyFiniteMeasure μ := hμ.locallyFinite
  have hs : MeasurableSet {p : ℂ × ℂ | dist p.2 p.1 < r} :=
    (isOpen_lt (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  have h := measurable_measure_prodMk_left (ν := μ) hs
  convert h using 1
  ext c
  congr 1

theorem PositiveFiniteBalls.measurable_ball_laverage {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) (r : ℝ) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable (fun x => ⨍⁻ z in ball x r, g z ∂μ) := by
  let : IsLocallyFiniteMeasure μ := hμ.locallyFinite
  let S : Set (ℂ × ℂ) := {p | dist p.2 p.1 < r}
  have hs : MeasurableSet S :=
    (isOpen_lt (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  have hk : Measurable (S.indicator (fun p : ℂ × ℂ => g p.2)) :=
    (hg.comp measurable_snd).indicator hs
  have hi : Measurable (fun x : ℂ => ∫⁻ z in ball x r, g z ∂μ) := by
    have hh := hk.lintegral_prod_right' (ν := μ)
    convert hh using 1
    ext x
    have he : (fun z : ℂ => S.indicator (fun p : ℂ × ℂ => g p.2) (x, z)) =
        (ball x r).indicator g := by
      ext z
      simp only [S, Set.indicator, Set.mem_ofPred_eq, mem_ball]
    rw [he, lintegral_indicator measurableSet_ball]
  simp_rw [setLAverage_eq]
  exact hi.div (hμ.measurable_ball_mass r)

theorem PositiveFiniteBalls.measurable_dyadicMaximal {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) (R : ℝ) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable (doublingDyadicMaximal μ R g) :=
  Measurable.iSup (fun n => hμ.measurable_ball_laverage (doublingDyadicRadius R n) hg)

theorem PositiveFiniteBalls.measurable_localMaximalEnergy {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) (c : ℂ) (R : ℝ) {g : ℂ → ℝ} (hg : Continuous g) :
    Measurable (doublingLocalMaximalEnergy μ c R g) :=
  hμ.measurable_dyadicMaximal R (hg.measurable.ennreal_ofReal.indicator measurableSet_ball)

end RepulsiveCoulomb.PaperRoute
