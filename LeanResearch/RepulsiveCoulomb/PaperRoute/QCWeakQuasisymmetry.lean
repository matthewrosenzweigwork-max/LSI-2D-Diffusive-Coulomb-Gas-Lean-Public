import LeanResearch.RepulsiveCoulomb.PaperRoute.QCScalarEnergy
import LeanResearch.RepulsiveCoulomb.PaperRoute.PlanarAnnulusOscillationEnergy
import LeanResearch.RepulsiveCoulomb.PaperRoute.WeakQuasisymmetryGeometry
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-!
# Analytic planar QC homeomorphisms are quantitatively weakly quasisymmetric

The endpoint uses only the actual supplied homeomorphism, its Lipschitz bounds
on compact source balls, and almost-everywhere actual real differentiability,
positive signed determinant and analytic distortion. The proof uses the same
map throughout. No weak-quasisymmetry, area or energy conclusion is assumed.

The proved scalar pullback energy and annular oscillation estimates bound
half-scale distortion by exp(9*pi^2*K/(4*log 2)). Four equispaced source steps
then give the explicit weak-QS constant (1 + exp(9*pi^2*K/(4*log 2)))^4 - 1.
This is a generic producer; it does not specialize the original accepted map
or claim the later DS, Poincare or complete manuscript endpoint.

The homeomorphism is the actual map F. The circle witnesses are derived here
from its continuous inverse and the compactness of finite source balls.
There is no assumed crossing certificate and no assumption about inverse
Sobolev regularity, absolute continuity on curves, or rectifiability.
-/

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology

namespace RepulsiveCoulomb.PaperRoute

/-- The inverse image under the actual F of a target affine line.
Its restriction to [0,1] is the segment pullback; to [1,infinity) it is the ray. -/
def qcPullbackTargetLine (F : ℂ ≃ₜ ℂ) (a q : ℂ) (t : ℝ) : ℂ :=
  F.symm (F a + t • (F q - F a))

theorem continuous_qcPullbackTargetLine (F : ℂ ≃ₜ ℂ) (a q : ℂ) :
    Continuous (qcPullbackTargetLine F a q) := by
  exact F.symm.continuous.comp
    (continuous_const.add (continuous_id.smul continuous_const))

@[simp] theorem qcPullbackTargetLine_zero (F : ℂ ≃ₜ ℂ) (a q : ℂ) :
    qcPullbackTargetLine F a q 0 = a := by
  simp [qcPullbackTargetLine]

@[simp] theorem qcPullbackTargetLine_one (F : ℂ ≃ₜ ℂ) (a q : ℂ) :
    qcPullbackTargetLine F a q 1 = q := by
  simp [qcPullbackTargetLine]

theorem norm_image_qcPullbackTargetLine (F : ℂ ≃ₜ ℂ) (a q : ℂ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖F (qcPullbackTargetLine F a q t) - F a‖ = t * ‖F q - F a‖ := by
  unfold qcPullbackTargetLine
  rw [F.apply_symm_apply, add_sub_cancel_left, norm_smul_of_nonneg ht]

/-- The pullback of a nonconstant target ray eventually leaves any prescribed
source closed ball, witnessed at an explicitly chosen finite real parameter. -/
theorem exists_qcPullbackTargetLine_norm_gt (F : ℂ ≃ₜ ℂ) (a b : ℂ)
    (hba : b ≠ a) (ρ : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ρ < ‖qcPullbackTargetLine F a b T - a‖ := by
  have hFab : F b ≠ F a := fun h => hba (F.injective h)
  have hL : 0 < ‖F b - F a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hFab)
  have hFcenter : Continuous (fun z : ℂ => F z - F a) :=
    F.continuous.sub continuous_const
  obtain ⟨M, hM⟩ := (isCompact_closedBall a ρ).exists_bound_of_continuousOn
    hFcenter.continuousOn
  let T : ℝ := max 1 ((M + 1) / ‖F b - F a‖)
  have hT : 1 ≤ T := le_max_left _ _
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hMT : M + 1 ≤ T * ‖F b - F a‖ :=
    (div_le_iff₀ hL).mp (le_max_right _ _)
  have hMT' : M < T * ‖F b - F a‖ := lt_of_lt_of_le (lt_add_one M) hMT
  refine ⟨T, hT, ?_⟩
  by_contra hescape
  have hinside : qcPullbackTargetLine F a b T ∈ closedBall a ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact le_of_not_gt hescape
  have hbound := hM (qcPullbackTargetLine F a b T) hinside
  change ‖F (qcPullbackTargetLine F a b T) - F a‖ ≤ M at hbound
  rw [norm_image_qcPullbackTargetLine F a b hT0] at hbound
  exact (not_le_of_gt hMT') hbound

/-- Every source circle of radius between 0 and ‖c-a‖ has a point whose image
lies in the target closed ball with center F a and radius ‖F c-F a‖. -/
theorem exists_source_sphere_image_norm_le (F : ℂ ≃ₜ ℂ) (a c : ℂ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρc : ρ ≤ ‖c - a‖) :
    ∃ z ∈ sphere a ρ, ‖F z - F a‖ ≤ ‖F c - F a‖ := by
  let g : ℝ → ℝ := fun t => ‖qcPullbackTargetLine F a c t - a‖
  have hg : Continuous g :=
    ((continuous_qcPullbackTargetLine F a c).sub continuous_const).norm
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : g 1 = ‖c - a‖ := by simp [g]
  have hmem : ρ ∈ Icc (g 0) (g 1) := by
    rw [hg0, hg1]
    exact ⟨hρ, hρc⟩
  obtain ⟨t, ht, htρ⟩ := intermediate_value_Icc zero_le_one hg.continuousOn hmem
  refine ⟨qcPullbackTargetLine F a c t, ?_, ?_⟩
  · exact Metric.mem_sphere.mpr (by simpa only [dist_eq_norm] using htρ)
  · rw [norm_image_qcPullbackTargetLine F a c ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)).trans_eq (one_mul _)

/-- Every source circle outside b has a point whose image is at least as far
from F a as F b. The target ray stays outside the outer open target ball. -/
theorem exists_source_sphere_image_norm_ge (F : ℂ ≃ₜ ℂ) (a b : ℂ)
    (hba : b ≠ a) {ρ : ℝ} (hbρ : ‖b - a‖ ≤ ρ) :
    ∃ z ∈ sphere a ρ, ‖F b - F a‖ ≤ ‖F z - F a‖ := by
  obtain ⟨T, hT, hescape⟩ := exists_qcPullbackTargetLine_norm_gt F a b hba ρ
  let g : ℝ → ℝ := fun t => ‖qcPullbackTargetLine F a b t - a‖
  have hg : Continuous g :=
    ((continuous_qcPullbackTargetLine F a b).sub continuous_const).norm
  have hg1 : g 1 = ‖b - a‖ := by simp [g]
  have hmem : ρ ∈ Icc (g 1) (g T) := by
    constructor
    · simpa only [hg1] using hbρ
    · exact hescape.le
  obtain ⟨t, ht, htρ⟩ := intermediate_value_Icc hT hg.continuousOn hmem
  refine ⟨qcPullbackTargetLine F a b t, ?_, ?_⟩
  · exact Metric.mem_sphere.mpr (by simpa only [dist_eq_norm] using htρ)
  · rw [norm_image_qcPullbackTargetLine F a b (le_trans zero_le_one ht.1)]
    exact (one_mul ‖F b - F a‖).symm.trans_le
      (mul_le_mul_of_nonneg_right ht.1 (norm_nonneg _))

/-- Actual zero and one values on every source circle in the annulus.
Only the two elementary target plateau properties of ψ are used. In the QC
application these are already proved for the concrete cubic logarithmic cutoff. -/
theorem exists_source_sphere_cutoff_zero_one
    (F : ℂ ≃ₜ ℂ) (a b c : ℂ) (ψ : ℂ → ℝ)
    (hba : b ≠ a)
    (hzero : ∀ y : ℂ, ‖y - F a‖ ≤ ‖F c - F a‖ → ψ y = 0)
    (hone : ∀ y : ℂ, ‖F b - F a‖ ≤ ‖y - F a‖ → ψ y = 1)
    {ρ : ℝ} (hbρ : ‖b - a‖ < ρ) (hρc : ρ < ‖c - a‖) :
    ∃ z₀ ∈ sphere a ρ, ∃ z₁ ∈ sphere a ρ,
      ψ (F z₀) = 0 ∧ ψ (F z₁) = 1 := by
  obtain ⟨z₀, hz₀, hFz₀⟩ := exists_source_sphere_image_norm_le F a c
    ((norm_nonneg (b - a)).trans hbρ.le) hρc.le
  obtain ⟨z₁, hz₁, hFz₁⟩ := exists_source_sphere_image_norm_ge F a b hba hbρ.le
  exact ⟨z₀, hz₀, z₁, hz₁, hzero (F z₀) hFz₀, hone (F z₁) hFz₁⟩

/-- Norm-equation interface if an annular energy producer uses explicit norms
rather than sphere membership. -/
theorem exists_source_circle_cutoff_zero_one
    (F : ℂ ≃ₜ ℂ) (a b c : ℂ) (ψ : ℂ → ℝ)
    (hba : b ≠ a)
    (hzero : ∀ y : ℂ, ‖y - F a‖ ≤ ‖F c - F a‖ → ψ y = 0)
    (hone : ∀ y : ℂ, ‖F b - F a‖ ≤ ‖y - F a‖ → ψ y = 1)
    {ρ : ℝ} (hbρ : ‖b - a‖ < ρ) (hρc : ρ < ‖c - a‖) :
    ∃ z₀ z₁ : ℂ, ‖z₀ - a‖ = ρ ∧ ‖z₁ - a‖ = ρ ∧
      ψ (F z₀) = 0 ∧ ψ (F z₁) = 1 := by
  obtain ⟨z₀, hz₀, z₁, hz₁, hzero₀, hone₁⟩ :=
    exists_source_sphere_cutoff_zero_one F a b c ψ hba hzero hone hbρ hρc
  exact ⟨z₀, z₁, by simpa only [Metric.mem_sphere, dist_eq_norm] using hz₀,
    by simpa only [Metric.mem_sphere, dist_eq_norm] using hz₁, hzero₀, hone₁⟩

/-- Elementary logarithmic comparison, after both real energy estimates. -/
theorem log_ratio_le_of_qc_energy {K s r l L : ℝ}
    (hs : 0 < s) (hsr : 2 * s ≤ r) (hl : 0 < l) (hlL : l < L)
    (henergy : (2 / Real.pi) * Real.log (r / s) ≤
      9 * Real.pi * K / (2 * Real.log (L / l))) :
    Real.log (L / l) ≤ 9 * Real.pi ^ 2 * K / (4 * Real.log 2) := by
  have hlog : 0 < Real.log (L / l) := Real.log_pos ((one_lt_div hl).mpr hlL)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrs : (2 : ℝ) ≤ r / s := (le_div_iff₀ hs).mpr hsr
  have hlogrs : Real.log 2 ≤ Real.log (r / s) :=
    Real.log_le_log (by norm_num) hrs
  have hb : (2 / Real.pi) * Real.log 2 ≤
      9 * Real.pi * K / (2 * Real.log (L / l)) :=
    (mul_le_mul_of_nonneg_left hlogrs (div_nonneg (by norm_num) Real.pi_pos.le)).trans henergy
  have hb' := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hlog)).mp hb
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hlog2)).mpr
  have hc := mul_le_mul_of_nonneg_right hb' Real.pi_pos.le
  field_simp at hc
  nlinarith

/-- Actual analytic quasiconformality controls target distances at half source scale. -/
theorem qc_half_scale_norm_control
    (F : ℂ ≃ₜ ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hQC : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x ∧
        ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (a b c : ℂ) (habc : 2 * ‖b - a‖ ≤ ‖c - a‖) :
    ‖F b - F a‖ ≤ Real.exp (9 * Real.pi ^ 2 * K / (4 * Real.log 2)) * ‖F c - F a‖ := by
  have hexp : 1 ≤ Real.exp (9 * Real.pi ^ 2 * K / (4 * Real.log 2)) :=
    Real.one_le_exp (by positivity)
  by_cases hba : b = a
  · subst b
    simp only [sub_self, norm_zero]
    positivity
  have hs : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hba)
  have hca : c ≠ a := by
    intro h
    subst c
    simp only [sub_self, norm_zero] at habc
    linarith
  have hl : 0 < ‖F c - F a‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hca (F.injective h)))
  by_cases hle : ‖F b - F a‖ ≤ ‖F c - F a‖
  · exact hle.trans (le_mul_of_one_le_left (norm_nonneg _) hexp)
  have hlL : ‖F c - F a‖ < ‖F b - F a‖ := lt_of_not_ge hle
  let v : ℂ → ℝ := cubicLogCutoff (F a) ‖F c - F a‖ ‖F b - F a‖ ∘ F
  have hpsi := contDiff_cubicLogCutoff (a := F a) hl hlL
  have hsupp := hasCompactSupport_fderiv_cubicLogCutoff (a := F a) hl hlL
  obtain ⟨C, hC⟩ := exists_lipschitzOn_scalar_comp_closedBall hLocal hpsi hsupp
    (‖a‖ + (‖c - a‖ + 1))
  have hv : LipschitzOnWith C v (closedBall a (‖c - a‖ + 1)) := by
    apply hC.mono
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    have hz' : ‖z - a‖ ≤ ‖c - a‖ + 1 := by
      simpa only [mem_closedBall, dist_eq_norm] using hz
    calc
      ‖z‖ ≤ ‖z - a‖ + ‖a‖ := norm_le_norm_sub_add z a
      _ ≤ ‖a‖ + (‖c - a‖ + 1) := by linarith
  have hosc : ∀ t ∈ Ioo ‖b - a‖ ‖c - a‖,
      (∃ z ∈ sphere a t, v z = 0) ∧ (∃ z ∈ sphere a t, v z = 1) := by
    intro t ht
    obtain ⟨z0, hz0, z1, hz1, h0, h1⟩ := exists_source_sphere_cutoff_zero_one
      F a b c (cubicLogCutoff (F a) ‖F c - F a‖ ‖F b - F a‖) hba
      (fun _ h => cubicLogCutoff_eq_zero hl hlL h)
      (fun _ h => cubicLogCutoff_eq_one hl hlL h) ht.1 ht.2
    exact ⟨⟨z0, hz0, h0⟩, ⟨z1, hz1, h1⟩⟩
  have hlow := (planar_annulus_oscillation_energy_of_lipschitzOn_closedBall hv hs
    (by linarith) (by linarith) hosc).2
  have hint : Integrable (fun x : ℂ => ‖fderiv ℝ v x‖ ^ 2) volume :=
    integrable_sq_norm_fderiv_scalar_comp F hK hLocal hQC hpsi hsupp
  have htotal : (∫ z in {z : ℂ | ‖b - a‖ < ‖z - a‖ ∧ ‖z - a‖ < ‖c - a‖},
      ‖fderiv ℝ v z‖ ^ 2) ≤ ∫ z : ℂ, ‖fderiv ℝ v z‖ ^ 2 :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun z => sq_nonneg _)) hint
  have hupp : (∫ z : ℂ, ‖fderiv ℝ v z‖ ^ 2) ≤
      9 * Real.pi * K / (2 * Real.log (‖F b - F a‖ / ‖F c - F a‖)) :=
    integral_sq_norm_fderiv_cubicLogCutoff_comp_le F hK hLocal hQC (F a) hl hlL
  have hlog := log_ratio_le_of_qc_energy hs habc hl hlL (hlow.trans (htotal.trans hupp))
  exact (div_le_iff₀ hl).mp ((Real.log_le_iff_le_exp (div_pos (hl.trans hlL) hl)).mp hlog)

theorem weakQuasisymmetricWith_of_half_scale
    {F : ℂ → ℂ} {h : ℝ} (hh : 1 ≤ h)
    (hhalf : ∀ a b c : ℂ, 2 * dist a b ≤ dist a c →
      dist (F a) (F b) ≤ h * dist (F a) (F c)) :
    WeakQuasisymmetricWith F ((1 + h) ^ 4 - 1) := by
  have hh0 : 0 ≤ h := le_trans zero_le_one hh
  have hP : 0 ≤ 1 + h := by linarith
  refine ⟨?_, ?_⟩
  · have htwo : (2 : ℝ) ≤ 1 + h := by linarith
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 4
    norm_num at hpow
    linarith
  · intro a b c hab
    let M : ℝ := dist (F a) (F c)
    let T : ℝ → ℝ := fun t => (1 + h) * t + h * M
    have hM : 0 ≤ M := dist_nonneg
    have hmono {u v : ℝ} (huv : u ≤ v) : T u ≤ T v := by
      dsimp [T]
      exact add_le_add (mul_le_mul_of_nonneg_left huv hP) le_rfl

    -- One short step, choosing a or c as the sufficiently distant reference.
    have step (p q : ℂ) (hpq : 4 * dist p q ≤ dist a c) :
        dist (F q) (F a) ≤ T (dist (F p) (F a)) := by
      have htri : dist a c ≤ dist p a + dist p c := by
        simpa only [dist_comm a p] using dist_triangle a p c
      have hout : dist (F q) (F a) ≤
          dist (F p) (F q) + dist (F p) (F a) := by
        simpa only [dist_comm (F q) (F p)] using dist_triangle (F q) (F p) (F a)
      rcases le_total (dist p a) (dist p c) with hfar | hfar
      · have hpqc : 2 * dist p q ≤ dist p c := by linarith
        have hcontrol := hhalf p q c hpqc
        have htarget : dist (F p) (F c) ≤ dist (F p) (F a) + M :=
          dist_triangle (F p) (F a) (F c)
        calc
          dist (F q) (F a)
              ≤ dist (F p) (F q) + dist (F p) (F a) := hout
          _ ≤ h * (dist (F p) (F a) + M) + dist (F p) (F a) :=
            add_le_add (hcontrol.trans
              (mul_le_mul_of_nonneg_left htarget hh0)) le_rfl
          _ = T (dist (F p) (F a)) := by dsimp [T]; ring
      · have hpqa : 2 * dist p q ≤ dist p a := by linarith
        have hcontrol := hhalf p q a hpqa
        calc
          dist (F q) (F a)
              ≤ dist (F p) (F q) + dist (F p) (F a) := hout
          _ ≤ h * dist (F p) (F a) + dist (F p) (F a) :=
            add_le_add hcontrol le_rfl
          _ ≤ T (dist (F p) (F a)) := by
            dsimp [T]
            nlinarith [mul_nonneg hh0 hM]

    -- Three iterated midpoints give four exactly equispaced steps.
    let x2 : ℂ := midpoint ℝ a b
    let x1 : ℂ := midpoint ℝ a x2
    let x3 : ℂ := midpoint ℝ x2 b
    have hax2 : dist a x2 = dist a b / 2 := by
      simp [x2, dist_left_midpoint, div_eq_mul_inv, mul_comm]
    have hx2b : dist x2 b = dist a b / 2 := by
      simp [x2, dist_midpoint_right, div_eq_mul_inv, mul_comm]
    have hd1 : dist a x1 = dist a b / 4 := by
      calc
        dist a x1 = dist a x2 / 2 := by
          simp [x1, dist_left_midpoint, div_eq_mul_inv, mul_comm]
        _ = dist a b / 4 := by rw [hax2]; ring
    have hd2 : dist x1 x2 = dist a b / 4 := by
      calc
        dist x1 x2 = dist a x2 / 2 := by
          simp [x1, dist_midpoint_right, div_eq_mul_inv, mul_comm]
        _ = dist a b / 4 := by rw [hax2]; ring
    have hd3 : dist x2 x3 = dist a b / 4 := by
      calc
        dist x2 x3 = dist x2 b / 2 := by
          simp [x3, dist_left_midpoint, div_eq_mul_inv, mul_comm]
        _ = dist a b / 4 := by rw [hx2b]; ring
    have hd4 : dist x3 b = dist a b / 4 := by
      calc
        dist x3 b = dist x2 b / 2 := by
          simp [x3, dist_midpoint_right, div_eq_mul_inv, mul_comm]
        _ = dist a b / 4 := by rw [hx2b]; ring
    have h1 := step a x1 (by rw [hd1]; linarith)
    have h2 := step x1 x2 (by rw [hd2]; linarith)
    have h3 := step x2 x3 (by rw [hd3]; linarith)
    have h4 := step x3 b (by rw [hd4]; linarith)
    have h1' : dist (F x1) (F a) ≤ h * M := by
      simpa only [dist_self, T, mul_zero, zero_add] using h1
    have hbound : dist (F b) (F a) ≤ T (T (T (h * M))) := by
      calc
        dist (F b) (F a) ≤ T (dist (F x3) (F a)) := h4
        _ ≤ T (T (dist (F x2) (F a))) := hmono h3
        _ ≤ T (T (T (dist (F x1) (F a)))) := hmono (hmono h2)
        _ ≤ T (T (T (h * M))) := hmono (hmono (hmono h1'))
    calc
      dist (F a) (F b) = dist (F b) (F a) := dist_comm _ _
      _ ≤ T (T (T (h * M))) := hbound
      _ = ((1 + h) ^ 4 - 1) * dist (F a) (F c) := by
        dsimp [T, M]
        ring


/-- Generic QC-to-weak-QS producer for the actual supplied homeomorphism.
No weak-quasisymmetry, area or scalar-energy conclusion is assumed. -/
theorem weakQuasisymmetricWith_of_analytic_qc
    (F : ℂ ≃ₜ ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hQC : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x ∧
        ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x) :
    WeakQuasisymmetricWith F
      ((1 + Real.exp (9 * Real.pi ^ 2 * K / (4 * Real.log 2))) ^ 4 - 1) := by
  apply weakQuasisymmetricWith_of_half_scale (Real.one_le_exp (by positivity))
  intro a b c habc
  simpa only [dist_eq_norm, norm_sub_rev] using qc_half_scale_norm_control F hK hLocal hQC a b c
    (by simpa only [dist_eq_norm, norm_sub_rev] using habc)

end RepulsiveCoulomb.PaperRoute
