import LeanResearch.RepulsiveCoulomb.ConformalC1Gluing

/-! C1 angular support profile for the classical cone distance: cosine up to
angle pi and the constant minus one beyond it. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def coneClippedCos (t : ℝ) : ℝ := (Icc (-Real.pi) Real.pi).piecewise Real.cos (fun _ ↦ -1) t

theorem coneClippedCos_boundary_jets (t : ℝ) (ht : t ∈ frontier (Icc (-Real.pi) Real.pi)) :
    Real.cos t = -1 ∧ fderiv ℝ Real.cos t = fderiv ℝ (fun _ : ℝ ↦ (-1 : ℝ)) t := by
  rw [frontier_Icc (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] at ht
  rcases ht with h | h
  · subst t
    constructor
    · simp
    · ext
      simp [fderiv_eq_smul_deriv, Real.deriv_cos]
  · have h' : t = Real.pi := h
    subst t
    constructor
    · simp
    · ext
      simp [fderiv_eq_smul_deriv, Real.deriv_cos]

theorem coneClippedCos_contDiff : ContDiff ℝ 1 coneClippedCos :=
  contDiff_one_piecewise_equal_jets Real.contDiff_cos contDiff_const
    (fun t ht ↦ (coneClippedCos_boundary_jets t ht).1)
    (fun t ht ↦ (coneClippedCos_boundary_jets t ht).2)

theorem coneClippedCos_hasDerivAt (t : ℝ) :
    HasDerivAt coneClippedCos (if t ∈ Icc (-Real.pi) Real.pi then -Real.sin t else 0) t := by
  change HasDerivAt ((Icc (-Real.pi) Real.pi).piecewise Real.cos (fun _ ↦ (-1 : ℝ))) _ t
  have h := hasFDerivAt_piecewise_equal_frontier_jets Real.differentiable_cos (differentiable_const (-1 : ℝ))
    (fun t ht ↦ (coneClippedCos_boundary_jets t ht).1)
    (fun t ht ↦ (coneClippedCos_boundary_jets t ht).2) t
  by_cases ht : t ∈ Icc (-Real.pi) Real.pi <;>
    simpa [coneClippedCos, Set.piecewise, ht, fderiv_eq_smul_deriv, Real.deriv_cos] using h.hasDerivAt

theorem coneClippedCos_abs_le_one (t : ℝ) : |coneClippedCos t| ≤ 1 := by
  by_cases ht : t ∈ Icc (-Real.pi) Real.pi
  · simpa [coneClippedCos, ht] using Real.abs_cos_le_one t
  · simp [coneClippedCos, ht]

theorem coneClippedCos_even (t : ℝ) : coneClippedCos (-t) = coneClippedCos t := by
  have he : -t ∈ Icc (-Real.pi) Real.pi ↔ t ∈ Icc (-Real.pi) Real.pi := by
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  by_cases ht : t ∈ Icc (-Real.pi) Real.pi <;> simp [coneClippedCos, he, ht, Real.cos_neg]

theorem coneClippedCos_sq_add_deriv_sq (t : ℝ) :
    coneClippedCos t ^ 2 + deriv coneClippedCos t ^ 2 = 1 := by
  rw [(coneClippedCos_hasDerivAt t).deriv]
  by_cases ht : t ∈ Icc (-Real.pi) Real.pi
  · simp [coneClippedCos, ht]
  · simp [coneClippedCos, ht]

theorem coneClippedCos_outer_jet {t : ℝ} (h : Real.pi ≤ |t|) :
    coneClippedCos t = -1 ∧ HasDerivAt coneClippedCos 0 t := by
  have hd := coneClippedCos_hasDerivAt t
  by_cases ht : t ∈ Icc (-Real.pi) Real.pi
  · have he : t = -Real.pi ∨ t = Real.pi := by
      rcases le_or_gt 0 t with hp | hp
      · rw [abs_of_nonneg hp] at h
        exact Or.inr (le_antisymm ht.2 h)
      · rw [abs_of_neg hp] at h
        exact Or.inl (by linarith [ht.1])
    rcases he with rfl | rfl
    · exact ⟨by simp [coneClippedCos, ht], by simpa [ht] using hd⟩
    · exact ⟨by simp [coneClippedCos, ht], by simpa [ht] using hd⟩
  · exact ⟨by simp [coneClippedCos, ht], by simpa [ht] using hd⟩

end RepulsiveCoulomb
