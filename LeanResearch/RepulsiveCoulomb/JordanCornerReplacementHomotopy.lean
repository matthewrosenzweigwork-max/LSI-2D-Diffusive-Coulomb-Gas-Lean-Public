module

public import LeanResearch.RepulsiveCoulomb.JordanBezierCorner

@[expose] public section

/-! The actual endpoint-fixed radial-V to quadratic-corner homotopy stays in a
small disk. It transports through a continuous chart and avoids every point
outside that chart disk. This is the local building block for preserving
actual argument increments under finitely many corner replacements.
Records-only candidate, not yet admitted or checked. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

def euclideanRadialCorner (u v : ℂ) (t : ℝ) : ℂ :=
  if t ≤ 1 / 2 then (2 * t - 1) • u else (2 * t - 1) • v

@[simp] theorem euclideanRadialCorner_zero (u v : ℂ) : euclideanRadialCorner u v 0 = -u := by
  simp [euclideanRadialCorner]

@[simp] theorem euclideanRadialCorner_one (u v : ℂ) : euclideanRadialCorner u v 1 = v := by
  norm_num [euclideanRadialCorner]

theorem euclideanRadialCorner_continuous (u v : ℂ) : Continuous (euclideanRadialCorner u v) := by
  apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
  intro t ht
  change t = 1 / 2 at ht
  subst t
  norm_num

theorem euclideanRadialCorner_norm_le {u v : ℂ} {ρ t : ℝ}
    (hρ : 0 ≤ ρ) (hu : ‖u‖ ≤ ρ) (hv : ‖v‖ ≤ ρ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖euclideanRadialCorner u v t‖ ≤ ρ := by
  have ha : |2 * t - 1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  unfold euclideanRadialCorner
  split_ifs
  · rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg u)).trans (by simpa using hu)
  · rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg v)).trans (by simpa using hv)

def euclideanCornerReplacement (u v : ℂ) (s t : ℝ) : ℂ :=
  (1 - s) • euclideanRadialCorner u v t + s • euclideanBezierCorner u v t

@[simp] theorem euclideanCornerReplacement_start (u v : ℂ) (t : ℝ) :
    euclideanCornerReplacement u v 0 t = euclideanRadialCorner u v t := by
  simp [euclideanCornerReplacement]

@[simp] theorem euclideanCornerReplacement_finish (u v : ℂ) (t : ℝ) :
    euclideanCornerReplacement u v 1 t = euclideanBezierCorner u v t := by
  simp [euclideanCornerReplacement]

@[simp] theorem euclideanCornerReplacement_zero (u v : ℂ) (s : ℝ) :
    euclideanCornerReplacement u v s 0 = -u := by
  simp only [euclideanCornerReplacement, euclideanRadialCorner_zero, euclideanBezierCorner_zero,
    ← add_smul, sub_add_cancel, one_smul]

@[simp] theorem euclideanCornerReplacement_one (u v : ℂ) (s : ℝ) :
    euclideanCornerReplacement u v s 1 = v := by
  simp only [euclideanCornerReplacement, euclideanRadialCorner_one, euclideanBezierCorner_one,
    ← add_smul, sub_add_cancel, one_smul]

theorem euclideanCornerReplacement_continuous (u v : ℂ) :
    Continuous (fun p : ℝ × ℝ => euclideanCornerReplacement u v p.1 p.2) :=
  ((continuous_const.sub continuous_fst).smul
    ((euclideanRadialCorner_continuous u v).comp continuous_snd)).add
      (continuous_fst.smul ((euclideanBezierCorner_contDiff u v).continuous.comp continuous_snd))

theorem euclideanCornerReplacement_norm_le {u v : ℂ} {ρ s t : ℝ}
    (hρ : 0 ≤ ρ) (hu : ‖u‖ ≤ ρ) (hv : ‖v‖ ≤ ρ)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖euclideanCornerReplacement u v s t‖ ≤ ρ := by
  have hV := euclideanRadialCorner_norm_le hρ hu hv ht
  have hB := euclideanBezierCorner_norm_le hρ hu hv ht
  calc
    ‖euclideanCornerReplacement u v s t‖ ≤
        ‖(1 - s) • euclideanRadialCorner u v t‖ + ‖s • euclideanBezierCorner u v t‖ := norm_add_le _ _
    _ = (1 - s) * ‖euclideanRadialCorner u v t‖ + s * ‖euclideanBezierCorner u v t‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hs.2), abs_of_nonneg hs.1]
    _ ≤ (1 - s) * ρ + s * ρ :=
      add_le_add (mul_le_mul_of_nonneg_left hV (sub_nonneg.mpr hs.2))
        (mul_le_mul_of_nonneg_left hB hs.1)
    _ = ρ := by ring

/-- The constructed chart-transported homotopy is continuous and endpoint-fixed,
and avoids a specified point outside the actual image of the chart disk. -/
theorem exists_chart_corner_replacement_homotopy {H : ℂ → ℂ} {u v p : ℂ} {ρ R : ℝ}
    (hρ : 0 ≤ ρ) (hρR : ρ < R) (hu : ‖u‖ ≤ ρ) (hv : ‖v‖ ≤ ρ)
    (hH : ContinuousOn H (ball (0 : ℂ) R))
    (hp : p ∉ H '' ball (0 : ℂ) R) :
    ∃ F : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℂ, Continuous F ∧
      (∀ t, F (0, t) = H (euclideanRadialCorner u v t)) ∧
      (∀ t, F (1, t) = H (euclideanBezierCorner u v t)) ∧
      (∀ s, F (s, 0) = H (-u)) ∧ (∀ s, F (s, 1) = H v) ∧
      ∀ q, F q ≠ p := by
  let B : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℂ :=
    fun q => euclideanCornerReplacement u v q.1 q.2
  have hparams : Continuous (fun q : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 =>
      ((q.1 : ℝ), (q.2 : ℝ))) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hB : Continuous B := (euclideanCornerReplacement_continuous u v).comp hparams
  have hball (q : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1) : B q ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    exact (euclideanCornerReplacement_norm_le hρ hu hv q.1.2 q.2.2).trans_lt hρR
  refine ⟨fun q => H (B q), hH.comp_continuous hB hball, ?_, ?_, ?_, ?_, ?_⟩
  · intro t; simp [B]
  · intro t; simp [B]
  · intro s; simp [B]
  · intro s; simp [B]
  · intro q heq
    exact hp ⟨B q, hball q, heq⟩

end RepulsiveCoulomb
