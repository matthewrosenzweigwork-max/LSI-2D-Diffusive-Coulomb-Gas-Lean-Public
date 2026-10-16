import LeanResearch.RepulsiveCoulomb.PointConePhase
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.IntermediateValue

/-! Actual open polar sectors cut a disk by two rays. Connectedness and the
complete complement decomposition are proved from polar coordinates. These
facts are the local topological inputs for choosing the Jordan interior side. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

def pointRadialSectorPoint (r θ : ℝ) : ℂ := (r : ℂ) * (Circle.exp θ : ℂ)

def pointOpenRadialSector (R α β : ℝ) : Set ℂ :=
  (fun x : ℝ × ℝ => pointRadialSectorPoint x.1 x.2) '' (Ioo 0 R ×ˢ Ioo α β)

def pointDiskRay (R θ : ℝ) : Set ℂ :=
  (fun r : ℝ => pointRadialSectorPoint r θ) '' Ico 0 R

theorem pointRadialSectorPoint_norm {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖pointRadialSectorPoint r θ‖ = r := by
  simp only [pointRadialSectorPoint, norm_mul, Circle.norm_coe, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

@[simp] theorem pointRadialSectorPoint_zero (θ : ℝ) : pointRadialSectorPoint 0 θ = 0 := by
  simp [pointRadialSectorPoint]

theorem pointOpenRadialSector_preconnected (R α β : ℝ) :
    IsPreconnected (pointOpenRadialSector R α β) := by
  apply (isPreconnected_Ioo.prod isPreconnected_Ioo).image
  have hc : Continuous (fun x : ℝ × ℝ => pointRadialSectorPoint x.1 x.2) := by
    simp only [pointRadialSectorPoint, Circle.coe_exp]
    fun_prop
  exact hc.continuousOn

theorem pointRadialSectorPoint_angle_injective {r s θ φ : ℝ}
    (hr : 0 < r) (hs : 0 ≤ s)
    (hθ : θ ∈ Ico (0 : ℝ) (2 * Real.pi)) (hφ : φ ∈ Ico (0 : ℝ) (2 * Real.pi))
    (he : pointRadialSectorPoint r θ = pointRadialSectorPoint s φ) : r = s ∧ θ = φ := by
  have hrs : r = s := by
    have h := congrArg norm he
    simpa only [pointRadialSectorPoint_norm hr.le, pointRadialSectorPoint_norm hs] using h
  subst s
  have hphase : (Circle.exp θ : ℂ) = (Circle.exp φ : ℂ) :=
    mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') he
  exact ⟨rfl, (Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by linarith))
    hθ hφ (Subtype.ext hphase)⟩

/-- Every nonzero point has a polar representative with angle in [0,2*pi). -/
theorem exists_pointRadialSectorPoint_angle (z : ℂ) (hz : z ≠ 0) :
    ∃ θ ∈ Ico (0 : ℝ) (2 * Real.pi), pointRadialSectorPoint ‖z‖ θ = z := by
  by_cases harg : 0 ≤ Complex.arg z
  · refine ⟨Complex.arg z, ⟨harg, ?_⟩, ?_⟩
    · linarith [Complex.arg_le_pi z, Real.pi_pos]
    · exact Complex.norm_mul_exp_arg_mul_I z
  · refine ⟨Complex.arg z + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
    · linarith [Complex.neg_pi_lt_arg z, Real.pi_pos]
    · linarith
    · unfold pointRadialSectorPoint
      rw [Circle.exp_add_two_pi]
      exact Complex.norm_mul_exp_arg_mul_I z

/-- The complement of the two rays in the disk is exactly the union of two
actual open polar sectors. No curve-side assertion is assumed. -/
theorem pointDiskRay_complement_eq_sectors {R θ : ℝ} (hR : 0 < R)
    (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi) :
    ball (0 : ℂ) R \ (pointDiskRay R 0 ∪ pointDiskRay R θ) =
      pointOpenRadialSector R 0 θ ∪ pointOpenRadialSector R θ (2 * Real.pi) := by
  have hzero : (0 : ℂ) ∈ pointDiskRay R 0 := ⟨0, ⟨le_rfl, hR⟩, by simp⟩
  have hangle0 : (0 : ℝ) ∈ Ico (0 : ℝ) (2 * Real.pi) := ⟨le_rfl, by positivity⟩
  have hangleθ : θ ∈ Ico (0 : ℝ) (2 * Real.pi) := ⟨hθ0.le, hθ2⟩
  have hsector (α β : ℝ) (hα : 0 ≤ α) (hβ : β ≤ 2 * Real.pi)
      (hno0 : ∀ φ ∈ Ioo α β, φ ≠ 0) (hnoθ : ∀ φ ∈ Ioo α β, φ ≠ θ) :
      pointOpenRadialSector R α β ⊆ ball (0 : ℂ) R \ (pointDiskRay R 0 ∪ pointDiskRay R θ) := by
    rintro z ⟨⟨r, φ⟩, ⟨hr, hφ⟩, rfl⟩
    have hangleφ : φ ∈ Ico (0 : ℝ) (2 * Real.pi) :=
      ⟨hα.trans hφ.1.le, hφ.2.trans_le hβ⟩
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hr.1.le]
      exact hr.2
    · intro hz
      rcases hz with hz | hz
      · rcases hz with ⟨s, hs, he⟩
        exact hno0 φ hφ (pointRadialSectorPoint_angle_injective hr.1 hs.1
          hangleφ hangle0 he.symm).2
      · rcases hz with ⟨s, hs, he⟩
        exact hnoθ φ hφ (pointRadialSectorPoint_angle_injective hr.1 hs.1
          hangleφ hangleθ he.symm).2
  apply Subset.antisymm
  · intro z hz
    have hz0 : z ≠ 0 := fun he => hz.2 (Or.inl (he.symm ▸ hzero))
    obtain ⟨φ, hφ, hpolar⟩ := exists_pointRadialSectorPoint_angle z hz0
    have hr : ‖z‖ ∈ Ioo (0 : ℝ) R := ⟨norm_pos_iff.mpr hz0, by
      simpa only [mem_ball, dist_zero_right] using hz.1⟩
    have hφ0 : φ ≠ 0 := by
      intro he
      apply hz.2
      exact Or.inl ⟨‖z‖, ⟨hr.1.le, hr.2⟩, by simpa only [he] using hpolar⟩
    have hφθ : φ ≠ θ := by
      intro he
      apply hz.2
      exact Or.inr ⟨‖z‖, ⟨hr.1.le, hr.2⟩, by simpa only [he] using hpolar⟩
    by_cases hlt : φ < θ
    · exact Or.inl ⟨(‖z‖, φ), ⟨hr, ⟨lt_of_le_of_ne hφ.1 (Ne.symm hφ0), hlt⟩⟩, hpolar⟩
    · exact Or.inr ⟨(‖z‖, φ), ⟨hr, ⟨lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hφθ), hφ.2⟩⟩, hpolar⟩
  · apply union_subset
    · exact hsector 0 θ le_rfl hθ2.le
        (fun φ hφ => ne_of_gt hφ.1) (fun φ hφ => ne_of_lt hφ.2)
    · exact hsector θ (2 * Real.pi) hθ0.le le_rfl
        (fun φ hφ => ne_of_gt (hθ0.trans hφ.1)) (fun φ hφ => ne_of_gt hφ.1)

/-- The two open sectors are disjoint as actual subsets of the complex plane. -/
theorem pointOpenRadialSectors_disjoint {R θ : ℝ} (hθ0 : 0 < θ)
    (hθ2 : θ < 2 * Real.pi) :
    Disjoint (pointOpenRadialSector R 0 θ) (pointOpenRadialSector R θ (2 * Real.pi)) := by
  apply disjoint_left.mpr
  rintro z ⟨⟨r, φ⟩, ⟨hr, hφ⟩, rfl⟩ ⟨⟨s, ψ⟩, ⟨hs, hψ⟩, he⟩
  have heq := (pointRadialSectorPoint_angle_injective hr.1 hs.1.le
    ⟨hφ.1.le, hφ.2.trans hθ2⟩ ⟨(hθ0.trans hψ.1).le, hψ.2⟩ he.symm).2
  linarith [hφ.2, hψ.1]

end RepulsiveCoulomb
