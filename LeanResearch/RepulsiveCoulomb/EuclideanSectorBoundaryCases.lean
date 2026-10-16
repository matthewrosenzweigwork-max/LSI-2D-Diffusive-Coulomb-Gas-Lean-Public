module

public import LeanResearch.RepulsiveCoulomb.EuclideanCenteredHalfDisk

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Classify actual source boundary points. This
supplies the apex/passing-edge alternative from membership and failure of
interior membership, rather than assuming a local sector type at the image. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem mem_interior_closedEuclideanSector_of_strict_arg {β : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) {z : ℂ}
    (harg : Complex.arg z ∈ Ioo (0 : ℝ) β) :
    z ∈ interior (closedEuclideanSector β) := by
  let V : Set ℂ := {w | 0 < w.im ∧
    Real.cos β * w.im - Real.sin β * w.re < 0}
  have hV : IsOpen V := (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt
      (show Continuous (fun w : ℂ ↦ Real.cos β * w.im - Real.sin β * w.re) by fun_prop)
      continuous_const)
  have hVS : V ⊆ closedEuclideanSector β := by
    intro w hw
    rw [closedEuclideanSector_eq_halfplanes hβ hβπ]
    exact ⟨hw.1.le, hw.2.le⟩
  have hz0 : z ≠ 0 := by
    intro hz
    have hh := harg.1
    rw [hz, Complex.arg_zero] at hh
    exact lt_irrefl _ hh
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hzV : z ∈ V := by
    constructor
    · rw [← Complex.norm_mul_sin_arg]
      exact mul_pos hzn (Real.sin_pos_of_pos_of_lt_pi harg.1 (harg.2.trans_le hβπ))
    · have hside : Real.cos β * z.im - Real.sin β * z.re =
          ‖z‖ * Real.sin (Complex.arg z - β) := by
        rw [Real.sin_sub]
        rw [show ‖z‖ * (Real.sin (Complex.arg z) * Real.cos β -
          Real.cos (Complex.arg z) * Real.sin β) =
          Real.cos β * (‖z‖ * Real.sin (Complex.arg z)) -
            Real.sin β * (‖z‖ * Real.cos (Complex.arg z)) by ring]
        rw [Complex.norm_mul_sin_arg, Complex.norm_mul_cos_arg]
      rw [hside, show Complex.arg z - β = -(β - Complex.arg z) by ring, Real.sin_neg]
      exact mul_neg_of_pos_of_neg hzn (neg_neg_of_pos
        (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr harg.2) (by linarith [harg.1])))
  exact interior_mono hVS (by simpa only [hV.interior_eq] using hzV)

/-- The nonapex boundary point lies on one of the actual source rays. -/
theorem closedEuclideanSector_noninterior_cases {β : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (q : closedEuclideanSector β)
    (hq : q.1 ∉ interior (closedEuclideanSector β)) :
    q.1 = 0 ∨ ∃ r : ℝ, 0 < r ∧ ∃ top : Bool,
      q.1 = sectorPolar r (if top then β else 0) := by
  by_cases hzero : q.1 = 0
  · exact Or.inl hzero
  · right
    have hr : 0 < ‖q.1‖ := norm_pos_iff.mpr hzero
    have hedge : Complex.arg q.1 = 0 ∨ Complex.arg q.1 = β := by
      by_contra hn
      push_neg at hn
      exact hq (mem_interior_closedEuclideanSector_of_strict_arg hβ hβπ
        ⟨lt_of_le_of_ne q.2.1 hn.1.symm, lt_of_le_of_ne q.2.2 hn.2⟩)
    refine ⟨‖q.1‖, hr, ?_⟩
    rcases hedge with he | he
    · exact ⟨false, by simpa only [Bool.false_eq_true, ↓reduceIte, he] using
        (sectorPolar_norm_arg q.1).symm⟩
    · exact ⟨true, by simpa only [↓reduceIte, he] using (sectorPolar_norm_arg q.1).symm⟩

end RepulsiveCoulomb
