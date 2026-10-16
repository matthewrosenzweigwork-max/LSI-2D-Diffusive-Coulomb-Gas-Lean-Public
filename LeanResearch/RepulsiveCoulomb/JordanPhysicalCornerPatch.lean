import LeanResearch.RepulsiveCoulomb.JordanC1Joining
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Explicit physical C1 rounding. No holomorphic chart or local inverse is
used. All quantities below are the actual physical curve and its derivative.
Records-only, uncompiled candidate. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

def physicalCornerClock (δ t : ℝ) : ℝ := (t + δ) / (2 * δ)
def physicalCornerLeftClock (δ t : ℝ) : ℝ := -δ * (1 - physicalCornerClock δ t) ^ 2
def physicalCornerRightClock (δ t : ℝ) : ℝ := δ * (physicalCornerClock δ t) ^ 2

def physicalCornerPatch (L R : ℝ → ℂ) (p : ℂ) (δ t : ℝ) : ℂ :=
  L (physicalCornerLeftClock δ t) + R (physicalCornerRightClock δ t) - p

theorem physicalCornerClock_mem {δ t : ℝ} (hδ : 0 < δ)
    (ht : t ∈ Icc (-δ) δ) : physicalCornerClock δ t ∈ Icc (0 : ℝ) 1 := by
  unfold physicalCornerClock
  exact ⟨div_nonneg (by linarith [ht.1]) (by positivity),
    (div_le_one (by positivity : 0 < 2 * δ)).mpr (by linarith [ht.2])⟩

theorem physicalCornerClock_ranges {δ t : ℝ} (hδ : 0 < δ)
    (ht : t ∈ Icc (-δ) δ) :
    physicalCornerLeftClock δ t ∈ Icc (-δ) 0 ∧
      physicalCornerRightClock δ t ∈ Icc (0 : ℝ) δ := by
  have hs := physicalCornerClock_mem hδ ht
  have h₁ : (1 - physicalCornerClock δ t) ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  have h₂ : (physicalCornerClock δ t) ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  dsimp [physicalCornerLeftClock, physicalCornerRightClock]
  constructor <;> constructor <;>
    nlinarith [sq_nonneg (physicalCornerClock δ t), sq_nonneg (1 - physicalCornerClock δ t)]

theorem physicalCornerClock_endpoints {δ : ℝ} (hδ : δ ≠ 0) :
    physicalCornerClock δ (-δ) = 0 ∧ physicalCornerClock δ δ = 1 := by
  constructor
  · simp [physicalCornerClock]
  · unfold physicalCornerClock
    field_simp [hδ]
    ring

theorem physicalCornerPatch_endpoints {L R : ℝ → ℂ} {p : ℂ} {δ : ℝ}
    (hδ : δ ≠ 0) (hL0 : L 0 = p) (hR0 : R 0 = p) :
    physicalCornerPatch L R p δ (-δ) = L (-δ) ∧
      physicalCornerPatch L R p δ δ = R δ := by
  have hs := physicalCornerClock_endpoints hδ
  simp [physicalCornerPatch, physicalCornerLeftClock, physicalCornerRightClock,
    hs.1, hs.2, hL0, hR0]

theorem physicalCornerPatch_contDiff {L R : ℝ → ℂ} (hL : ContDiff ℝ 1 L)
    (hR : ContDiff ℝ 1 R) (p : ℂ) (δ : ℝ) :
    ContDiff ℝ 1 (physicalCornerPatch L R p δ) := by
  unfold physicalCornerPatch physicalCornerLeftClock physicalCornerRightClock physicalCornerClock
  fun_prop

theorem physicalCornerClock_hasDerivAt (δ t : ℝ) :
    HasDerivAt (physicalCornerClock δ) (2 * δ)⁻¹ t := by
  convert! ((hasDerivAt_id t).add_const δ).div_const (2 * δ) using 1 <;>
    simp [physicalCornerClock, one_div, id_eq]

theorem physicalCornerLeftClock_hasDerivAt {δ : ℝ} (hδ : δ ≠ 0) (t : ℝ) :
    HasDerivAt (physicalCornerLeftClock δ) (1 - physicalCornerClock δ t) t := by
  have h := (((hasDerivAt_const t (1 : ℝ)).sub
    (physicalCornerClock_hasDerivAt δ t)).fun_pow 2).const_mul (-δ)
  simp only [Pi.sub_apply] at h
  convert h using 1
  · rfl
  · field_simp [hδ]
    ring

theorem physicalCornerRightClock_hasDerivAt {δ : ℝ} (hδ : δ ≠ 0) (t : ℝ) :
    HasDerivAt (physicalCornerRightClock δ) (physicalCornerClock δ t) t := by
  have h := ((physicalCornerClock_hasDerivAt δ t).fun_pow 2).const_mul δ
  convert h using 1
  · rfl
  · field_simp [hδ]
    ring

theorem physicalCornerPatch_hasDerivAt {L R : ℝ → ℂ}
    (hL : Differentiable ℝ L) (hR : Differentiable ℝ R) (p : ℂ)
    {δ : ℝ} (hδ : δ ≠ 0) (t : ℝ) :
    HasDerivAt (physicalCornerPatch L R p δ)
      ((1 - physicalCornerClock δ t) • deriv L (physicalCornerLeftClock δ t) +
        physicalCornerClock δ t • deriv R (physicalCornerRightClock δ t)) t := by
  exact (((hL _).hasDerivAt.scomp t (physicalCornerLeftClock_hasDerivAt hδ t)).add
    ((hR _).hasDerivAt.scomp t (physicalCornerRightClock_hasDerivAt hδ t))).sub_const p

theorem physicalCornerPatch_deriv {L R : ℝ → ℂ}
    (hL : Differentiable ℝ L) (hR : Differentiable ℝ R) (p : ℂ)
    {δ : ℝ} (hδ : δ ≠ 0) (t : ℝ) :
    deriv (physicalCornerPatch L R p δ) t =
      (1 - physicalCornerClock δ t) • deriv L (physicalCornerLeftClock δ t) +
        physicalCornerClock δ t • deriv R (physicalCornerRightClock δ t) :=
  (physicalCornerPatch_hasDerivAt hL hR p hδ t).deriv

theorem physicalCornerPatch_endpoint_derivatives {L R : ℝ → ℂ}
    (hL : Differentiable ℝ L) (hR : Differentiable ℝ R) (p : ℂ)
    {δ : ℝ} (hδ : δ ≠ 0) :
    deriv (physicalCornerPatch L R p δ) (-δ) = deriv L (-δ) ∧
      deriv (physicalCornerPatch L R p δ) δ = deriv R δ := by
  have hs := physicalCornerClock_endpoints hδ
  simp [physicalCornerPatch_deriv hL hR p hδ,
    physicalCornerLeftClock, physicalCornerRightClock, hs.1, hs.2]

/-- Positivity is proved on the actual physical derivative. -/
theorem physicalCornerPatch_positive_deriv {L R : ℝ → ℂ}
    (hL : Differentiable ℝ L) (hR : Differentiable ℝ R) (p c : ℂ)
    {δ : ℝ} (hδ : 0 < δ)
    (hLp : ∀ t ∈ Icc (-δ) 0, 0 < (c * deriv L t).re)
    (hRp : ∀ t ∈ Icc (0 : ℝ) δ, 0 < (c * deriv R t).re)
    {t : ℝ} (ht : t ∈ Icc (-δ) δ) :
    0 < (c * deriv (physicalCornerPatch L R p δ) t).re := by
  have hs := physicalCornerClock_mem hδ ht
  have hr := physicalCornerClock_ranges hδ ht
  have hA := hLp _ hr.1
  have hB := hRp _ hr.2
  have he (α β : ℝ) (u v : ℂ) :
      (c * (α • u + β • v)).re = α * (c * u).re + β * (c * v).re := by
    simp [Complex.real_smul, Complex.mul_re, Complex.mul_im]
    ring
  rw [physicalCornerPatch_deriv hL hR p hδ.ne', he]
  by_cases hs0 : physicalCornerClock δ t = 0
  · simpa [hs0] using hA
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (by linarith [hs.2]) hA.le)
      (mul_pos (lt_of_le_of_ne hs.1 (Ne.symm hs0)) hB)

/-- A positive projection proves strict monotonicity and therefore simplicity. -/
theorem complex_curve_strictMono_projection {f : ℝ → ℂ}
    (hf : Differentiable ℝ f) (c : ℂ) {a b : ℝ}
    (hp : ∀ t ∈ Icc a b, 0 < (c * deriv f t).re) :
    StrictMonoOn (fun t => (c * f t).re) (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
  · exact (Complex.continuous_re.comp (continuous_const.mul hf.continuous)).continuousOn
  · intro t ht
    have hd : HasDerivAt (fun t => (c * f t).re) (c * deriv f t).re t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ((hf t).hasDerivAt.const_mul c)
    rw [hd.deriv]
    exact hp t (interior_subset ht)

theorem physicalCornerPatch_regular_injective {L R : ℝ → ℂ}
    (hL : ContDiff ℝ 1 L) (hR : ContDiff ℝ 1 R) (p c : ℂ)
    {δ : ℝ} (hδ : 0 < δ)
    (hLp : ∀ t ∈ Icc (-δ) 0, 0 < (c * deriv L t).re)
    (hRp : ∀ t ∈ Icc (0 : ℝ) δ, 0 < (c * deriv R t).re) :
    (∀ t ∈ Icc (-δ) δ, deriv (physicalCornerPatch L R p δ) t ≠ 0) ∧
      InjOn (physicalCornerPatch L R p δ) (Icc (-δ) δ) := by
  have hd (t : ℝ) (ht : t ∈ Icc (-δ) δ) :
      0 < (c * deriv (physicalCornerPatch L R p δ) t).re :=
    physicalCornerPatch_positive_deriv
      (hL.differentiable (by norm_num)) (hR.differentiable (by norm_num)) p c hδ hLp hRp ht
  constructor
  · intro t ht hz
    have h := hd t ht
    simpa [hz] using h
  · intro s hs t ht heq
    exact (complex_curve_strictMono_projection
      ((physicalCornerPatch_contDiff hL hR p δ).differentiable (by norm_num)) c
      (fun x hx => hd x hx)).injOn hs ht (congrArg (fun z : ℂ => (c * z).re) heq)

/-- Global C1 gluing uses only the proved exact values and jets. -/
theorem exists_C1_physical_corner_patch {L R : ℝ → ℂ}
    (hL : ContDiff ℝ 1 L) (hR : ContDiff ℝ 1 R) {p : ℂ}
    (hL0 : L 0 = p) (hR0 : R 0 = p) (c : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hLp : ∀ t ∈ Icc (-δ) 0, 0 < (c * deriv L t).re)
    (hRp : ∀ t ∈ Icc (0 : ℝ) δ, 0 < (c * deriv R t).re) :
    ∃ C : ℝ → ℂ, ContDiff ℝ 1 C ∧
      (∀ t, t ≤ -δ → C t = L t) ∧ (∀ t, δ ≤ t → C t = R t) ∧
      (∀ t ∈ Icc (-δ) δ, C t = physicalCornerPatch L R p δ t) ∧
      (∀ t ∈ Icc (-δ) δ, deriv C t = deriv (physicalCornerPatch L R p δ) t) ∧
      (∀ t ∈ Icc (-δ) δ, 0 < (c * deriv C t).re) := by
  let P := physicalCornerPatch L R p δ
  have hP : ContDiff ℝ 1 P := physicalCornerPatch_contDiff hL hR p δ
  have hv := physicalCornerPatch_endpoints hδ.ne' hL0 hR0
  have hj := physicalCornerPatch_endpoint_derivatives
    (hL.differentiable (by norm_num)) (hR.differentiable (by norm_num)) p hδ.ne'
  let A := euclideanC1Glue (-δ) L P
  have hA : ContDiff ℝ 1 A := euclideanC1Glue_contDiff hL hP hv.1.symm hj.1.symm
  have hvA : A δ = R δ := (euclideanC1Glue_eq_right hv.1.symm (by linarith)).trans hv.2
  have hjA : deriv A δ = deriv R δ := by
    rw [euclideanC1Glue_deriv (hL.differentiable (by norm_num))
      (hP.differentiable (by norm_num)) hv.1.symm hj.1.symm,
      if_neg (show ¬δ ≤ -δ by linarith)]
    exact hj.2
  let C := euclideanC1Glue δ A R
  have hC : ContDiff ℝ 1 C := euclideanC1Glue_contDiff hA hR hvA hjA
  have hd (t : ℝ) (ht : t ∈ Icc (-δ) δ) : deriv C t = deriv P t := by
    rw [euclideanC1Glue_deriv (hA.differentiable (by norm_num))
      (hR.differentiable (by norm_num)) hvA hjA, if_pos ht.2,
      euclideanC1Glue_deriv (hL.differentiable (by norm_num))
      (hP.differentiable (by norm_num)) hv.1.symm hj.1.symm]
    split_ifs with hh
    · have he : t = -δ := le_antisymm hh ht.1
      simpa [he] using hj.1.symm
    · rfl
  refine ⟨C, hC, ?_, ?_, ?_, hd, ?_⟩
  · intro t ht
    change euclideanC1Glue δ A R t = L t
    rw [euclideanC1Glue_eq_left δ A R (by linarith)]
    exact euclideanC1Glue_eq_left (-δ) L P ht
  · intro t ht
    exact euclideanC1Glue_eq_right hvA ht
  · intro t ht
    change euclideanC1Glue δ A R t = P t
    rw [euclideanC1Glue_eq_left δ A R ht.2]
    exact euclideanC1Glue_eq_right hv.1.symm ht.1
  · intro t ht
    rw [hd t ht]
    exact physicalCornerPatch_positive_deriv (hL.differentiable (by norm_num))
      (hR.differentiable (by norm_num)) p c hδ hLp hRp ht

end RepulsiveCoulomb
