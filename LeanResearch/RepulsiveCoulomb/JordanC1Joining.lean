import LeanResearch.RepulsiveCoulomb.JordanEndpointReparameterization
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.OrderClosed

/-! Actual C¹ gluing at a matched value and velocity. The derivative is proved
on both half-lines and at the seam, then its continuity is established by the
pasting lemma. No C¹ gluing certificate is assumed. Records-only phase five. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

def euclideanC1Glue (c : ℝ) (f g : ℝ → ℂ) (t : ℝ) : ℂ :=
  if t ≤ c then f t else g t

theorem euclideanC1Glue_eq_left (c : ℝ) (f g : ℝ → ℂ) {t : ℝ} (ht : t ≤ c) :
    euclideanC1Glue c f g t = f t := if_pos ht

theorem euclideanC1Glue_eq_right {c : ℝ} {f g : ℝ → ℂ} (hval : f c = g c)
    {t : ℝ} (ht : c ≤ t) : euclideanC1Glue c f g t = g t := by
  by_cases htc : t ≤ c
  · have heq : t = c := le_antisymm htc ht
    subst t
    simp [euclideanC1Glue, hval]
  · exact if_neg htc

theorem euclideanC1Glue_hasDerivAt {c : ℝ} {f g : ℝ → ℂ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hval : f c = g c) (hjet : deriv f c = deriv g c) (t : ℝ) :
    HasDerivAt (euclideanC1Glue c f g)
      (if t ≤ c then deriv f t else deriv g t) t := by
  rcases lt_trichotomy t c with ht | ht | ht
  · rw [if_pos ht.le]
    apply (hf t).hasDerivAt.congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds ht] with x hx
    exact euclideanC1Glue_eq_left c f g hx.le
  · subst t
    rw [if_pos le_rfl]
    have hl : HasDerivWithinAt (euclideanC1Glue c f g) (deriv f c) (Iic c) c :=
      (hf c).hasDerivAt.hasDerivWithinAt.congr_of_mem
        (fun x hx => euclideanC1Glue_eq_left c f g hx) (mem_Iic.mpr le_rfl)
    have hr : HasDerivWithinAt (euclideanC1Glue c f g) (deriv f c) (Ici c) c := by
      rw [hjet]
      exact (hg c).hasDerivAt.hasDerivWithinAt.congr_of_mem
        (fun x hx => euclideanC1Glue_eq_right hval hx) (mem_Ici.mpr le_rfl)
    have hboth := hl.union hr
    rw [Iic_union_Ici] at hboth
    exact hasDerivWithinAt_univ.mp hboth
  · rw [if_neg (not_le.mpr ht)]
    apply (hg t).hasDerivAt.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds ht] with x hx
    exact euclideanC1Glue_eq_right hval hx.le

theorem euclideanC1Glue_deriv {c : ℝ} {f g : ℝ → ℂ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hval : f c = g c) (hjet : deriv f c = deriv g c) (t : ℝ) :
    deriv (euclideanC1Glue c f g) t = if t ≤ c then deriv f t else deriv g t :=
  (euclideanC1Glue_hasDerivAt hf hg hval hjet t).deriv

theorem euclideanC1Glue_contDiff {c : ℝ} {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hval : f c = g c) (hjet : deriv f c = deriv g c) :
    ContDiff ℝ 1 (euclideanC1Glue c f g) := by
  have hfd := hf.differentiable (by norm_num)
  have hgd := hg.differentiable (by norm_num)
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun t => (euclideanC1Glue_hasDerivAt hfd hgd hval hjet t).differentiableAt
  · have heq : deriv (euclideanC1Glue c f g) =
        fun t => if t ≤ c then deriv f t else deriv g t :=
      funext (euclideanC1Glue_deriv hfd hgd hval hjet)
    rw [heq]
    exact Continuous.if_le hf.continuous_deriv_one hg.continuous_deriv_one
      continuous_id continuous_const (fun t ht => by simpa only [ht] using hjet)

/-- Standard concatenation of actual regular arcs, after matching the actual
endpoint velocities, is globally C¹. -/
def euclideanSmoothConcatenate (f g : ℝ → ℂ) : ℝ → ℂ :=
  euclideanC1Glue (1 / 2) (fun t => f (2 * t)) (fun t => g (2 * t - 1))

@[simp] theorem euclideanSmoothConcatenate_zero (f g : ℝ → ℂ) :
    euclideanSmoothConcatenate f g 0 = f 0 := by
  simp [euclideanSmoothConcatenate, euclideanC1Glue]

@[simp] theorem euclideanSmoothConcatenate_one (f g : ℝ → ℂ) :
    euclideanSmoothConcatenate f g 1 = g 1 := by
  norm_num [euclideanSmoothConcatenate, euclideanC1Glue]

theorem euclideanSmoothConcatenate_contDiff {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hval : f 1 = g 0) (hjet : deriv f 1 = deriv g 0) :
    ContDiff ℝ 1 (euclideanSmoothConcatenate f g) := by
  apply euclideanC1Glue_contDiff (by fun_prop) (by fun_prop)
  · simpa using hval
  · have hd₁ : HasDerivAt (fun t : ℝ => f (2 * t)) ((2 : ℝ) • deriv f 1) (1 / 2) := by
      simpa [Function.comp_def, id_eq] using (((hf.differentiable (by norm_num)) (2 * (1 / 2 : ℝ))).hasDerivAt.scomp
        (1 / 2 : ℝ) ((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2))
    have hd₂ : HasDerivAt (fun t : ℝ => g (2 * t - 1)) ((2 : ℝ) • deriv g 0) (1 / 2) := by
      simpa [Function.comp_def, id_eq] using (((hg.differentiable (by norm_num)) (2 * (1 / 2 : ℝ) - 1)).hasDerivAt.scomp
        (1 / 2 : ℝ) (((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2).sub_const 1))
    rw [hd₁.deriv, hd₂.deriv, hjet]

/-- The actual derivative of the concatenation on both closed halves. -/
theorem euclideanSmoothConcatenate_deriv {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hval : f 1 = g 0) (hjet : deriv f 1 = deriv g 0) (t : ℝ) :
    deriv (euclideanSmoothConcatenate f g) t =
      if t ≤ 1 / 2 then (2 : ℝ) • deriv f (2 * t)
      else (2 : ℝ) • deriv g (2 * t - 1) := by
  have hcf : ContDiff ℝ 1 (fun t : ℝ => f (2 * t)) := by fun_prop
  have hcg : ContDiff ℝ 1 (fun t : ℝ => g (2 * t - 1)) := by fun_prop
  have hdf (x : ℝ) : deriv (fun t : ℝ => f (2 * t)) x = (2 : ℝ) • deriv f (2 * x) := by
    simpa only [Function.comp_def, id_eq, mul_one] using ((((hf.differentiable (by norm_num)) (2 * x)).hasDerivAt.scomp
      x ((hasDerivAt_id x).const_mul 2)).deriv)
  have hdg (x : ℝ) : deriv (fun t : ℝ => g (2 * t - 1)) x =
      (2 : ℝ) • deriv g (2 * x - 1) := by
    simpa only [Function.comp_def, id_eq, mul_one] using ((((hg.differentiable (by norm_num)) (2 * x - 1)).hasDerivAt.scomp
      x (((hasDerivAt_id x).const_mul 2).sub_const 1)).deriv)
  have hv : f (2 * (1 / 2)) = g (2 * (1 / 2) - 1) := by norm_num; exact hval
  have hd : deriv (fun t : ℝ => f (2 * t)) (1 / 2) =
      deriv (fun t : ℝ => g (2 * t - 1)) (1 / 2) := by
    rw [hdf, hdg]
    norm_num
    rw [hjet]
  change deriv (euclideanC1Glue (1 / 2) (fun t => f (2 * t))
    (fun t => g (2 * t - 1))) t = _
  rw [euclideanC1Glue_deriv (hcf.differentiable (by norm_num))
    (hcg.differentiable (by norm_num)) hv hd, hdf, hdg]

theorem euclideanSmoothConcatenate_regular {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hval : f 1 = g 0) (hjet : deriv f 1 = deriv g 0)
    (hfr : ∀ t ∈ Icc (0 : ℝ) 1, deriv f t ≠ 0)
    (hgr : ∀ t ∈ Icc (0 : ℝ) 1, deriv g t ≠ 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    deriv (euclideanSmoothConcatenate f g) t ≠ 0 := by
  rw [euclideanSmoothConcatenate_deriv hf hg hval hjet]
  split_ifs with hmid
  · exact smul_ne_zero (by norm_num) (hfr _ (by constructor <;> linarith [ht.1, ht.2]))
  · exact smul_ne_zero (by norm_num) (hgr _ (by constructor <;> linarith [ht.1, ht.2]))

theorem euclideanSmoothConcatenate_left (f g : ℝ → ℂ)
    {t : ℝ} (ht : t ≤ 1 / 2) : euclideanSmoothConcatenate f g t = f (2 * t) :=
  euclideanC1Glue_eq_left _ _ _ ht

theorem euclideanSmoothConcatenate_right {f g : ℝ → ℂ} (hval : f 1 = g 0)
    {t : ℝ} (ht : 1 / 2 ≤ t) : euclideanSmoothConcatenate f g t = g (2 * t - 1) := by
  apply euclideanC1Glue_eq_right (c := 1 / 2) _ ht
  norm_num
  exact hval

/-- The constructed concatenation has exactly the union of the original arc
images, including the common endpoint. -/
theorem euclideanSmoothConcatenate_image {f g : ℝ → ℂ} (hval : f 1 = g 0) :
    euclideanSmoothConcatenate f g '' Icc (0 : ℝ) 1 =
      f '' Icc (0 : ℝ) 1 ∪ g '' Icc (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    by_cases hmid : t ≤ 1 / 2
    · left
      rw [euclideanSmoothConcatenate_left f g hmid]
      exact ⟨2 * t, by constructor <;> linarith [ht.1, ht.2], rfl⟩
    · right
      rw [euclideanSmoothConcatenate_right hval (not_le.mp hmid).le]
      exact ⟨2 * t - 1, by constructor <;> linarith [ht.1, ht.2], rfl⟩
  · rintro z (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · refine ⟨t / 2, by constructor <;> linarith [ht.1, ht.2], ?_⟩
      rw [euclideanSmoothConcatenate_left f g (by linarith [ht.2])]
      congr 1
      ring
    · refine ⟨(t + 1) / 2, by constructor <;> linarith [ht.1, ht.2], ?_⟩
      rw [euclideanSmoothConcatenate_right hval (by linarith [ht.1])]
      congr 1
      ring

/-- Ordinary one-endpoint gluing preserves actual injectivity. -/
theorem euclideanSmoothConcatenate_injOn {f g : ℝ → ℂ}
    (hf : InjOn f (Icc (0 : ℝ) 1)) (hg : InjOn g (Icc (0 : ℝ) 1))
    (hval : f 1 = g 0)
    (hmeet : f '' Icc (0 : ℝ) 1 ∩ g '' Icc (0 : ℝ) 1 ⊆ {f 1}) :
    InjOn (euclideanSmoothConcatenate f g) (Icc (0 : ℝ) 1) := by
  intro s hs t ht heq
  have left_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hm : x ≤ 1 / 2) :
      2 * x ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have right_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hm : 1 / 2 ≤ x) :
      2 * x - 1 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  by_cases hsm : s ≤ 1 / 2 <;> by_cases htm : t ≤ 1 / 2
  · rw [euclideanSmoothConcatenate_left f g hsm,
      euclideanSmoothConcatenate_left f g htm] at heq
    have h := hf (left_mem hs hsm) (left_mem ht htm) heq
    linarith
  · rw [euclideanSmoothConcatenate_left f g hsm,
      euclideanSmoothConcatenate_right hval (not_le.mp htm).le] at heq
    have hcommon : f (2 * s) = f 1 := hmeet
      ⟨⟨2 * s, left_mem hs hsm, rfl⟩, ⟨2 * t - 1, right_mem ht (not_le.mp htm).le, heq.symm⟩⟩
    have hs' := hf (left_mem hs hsm) (by norm_num) hcommon
    have ht' := hg (right_mem ht (not_le.mp htm).le) (by norm_num)
      (heq.symm.trans (hcommon.trans hval))
    linarith
  · rw [euclideanSmoothConcatenate_right hval (not_le.mp hsm).le,
      euclideanSmoothConcatenate_left f g htm] at heq
    have hcommon : f (2 * t) = f 1 := hmeet
      ⟨⟨2 * t, left_mem ht htm, rfl⟩, ⟨2 * s - 1, right_mem hs (not_le.mp hsm).le, heq⟩⟩
    have ht' := hf (left_mem ht htm) (by norm_num) hcommon
    have hs' := hg (right_mem hs (not_le.mp hsm).le) (by norm_num)
      (heq.trans (hcommon.trans hval))
    linarith
  · rw [euclideanSmoothConcatenate_right hval (not_le.mp hsm).le,
      euclideanSmoothConcatenate_right hval (not_le.mp htm).le] at heq
    have h := hg (right_mem hs (not_le.mp hsm).le) (right_mem ht (not_le.mp htm).le) heq
    linarith

end RepulsiveCoulomb
