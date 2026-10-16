module

public import LeanResearch.RepulsiveCoulomb.JordanCornerInterpolation
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

/-! Actual physical tangent half-planes. These lemmas do not identify the
turn through a nonconformal chart with its coordinate turn. They construct
one branch on the PHYSICAL tangent vectors and retain its full increment.
Records-only draft; no Lean invocation has been made. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Positive real part after a fixed complex multiplier is a real open
half-plane through the origin. -/
def physicalHalfplane (c : ℂ) : Set ℂ := {z | 0 < (c * z).re}

theorem physicalHalfplane_ne_zero {c z : ℂ} (hz : z ∈ physicalHalfplane c) : z ≠ 0 := by
  intro he
  simpa [physicalHalfplane, he] using hz

theorem physicalHalfplane_multiplier_ne_zero {c z : ℂ}
    (hz : z ∈ physicalHalfplane c) : c ≠ 0 := by
  intro he
  simpa [physicalHalfplane, he] using hz

theorem isOpen_physicalHalfplane (c : ℂ) : IsOpen (physicalHalfplane c) := by
  exact isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.mul continuous_id))

/-- Every pair with principal quotient in the slit plane admits an actual
common positive linear functional. This also covers equal tangent rays. -/
theorem exists_physical_common_halfplane {u v : ℂ} (hu : u ≠ 0)
    (hc : v / u ∈ Complex.slitPlane) :
    ∃ c : ℂ, u ∈ physicalHalfplane c ∧ v ∈ physicalHalfplane c := by
  let q := v / u
  have hq : 0 < q.re ∨ q.im ≠ 0 := Complex.mem_slitPlane_iff.mp hc
  rcases hq with hq | hq
  · refine ⟨u⁻¹, ?_, ?_⟩
    · change 0 < (u⁻¹ * u).re
      rw [inv_mul_cancel₀ hu]
      norm_num
    · simpa [physicalHalfplane, q, div_eq_mul_inv, mul_comm] using hq
  · let k : ℝ := (q.re - 1) / q.im
    let d : ℂ := 1 + (k : ℂ) * Complex.I
    have hdre : d.re = 1 := by simp [d]
    have hdim : d.im = k := by simp [d]
    have hd : (d * q).re = 1 := by
      rw [Complex.mul_re, hdre, hdim, one_mul]
      dsimp [k]
      field_simp [hq] <;> ring
    refine ⟨d / u, ?_, ?_⟩
    · have he : d / u * u = d := div_mul_cancel₀ d hu
      change 0 < (d / u * u).re
      rw [he]
      norm_num [d]
    · have he : d / u * v = d * q := by dsimp [q]; field_simp <;> ring
      change 0 < (d / u * v).re
      rw [he, hd]
      norm_num

/-- A concrete argument branch for physical vectors in the chosen half-plane. -/
def physicalHalfplaneArg (c z : ℂ) : ℝ := Complex.arg (z / c⁻¹) + Complex.arg c⁻¹

theorem physicalHalfplaneArg_continuous {X : Type*} [TopologicalSpace X]
    {c : ℂ} {v : X → ℂ} (hv : Continuous v)
    (hpos : ∀ x, v x ∈ physicalHalfplane c) :
    Continuous (fun x => physicalHalfplaneArg c (v x)) := by
  apply Continuous.add _ continuous_const
  apply continuous_iff_continuousAt.mpr
  intro x
  have hslit : v x / c⁻¹ ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa [physicalHalfplane, div_eq_mul_inv, mul_comm] using hpos x
  exact (Complex.continuousAt_arg hslit).comp
    (f := fun x => v x / c⁻¹) (x := x) (hv.div_const _).continuousAt

theorem physicalHalfplaneArg_lift {c z : ℂ} (hpos : z ∈ physicalHalfplane c) :
    Circle.exp (physicalHalfplaneArg c z) =
      euclideanDirection z (physicalHalfplane_ne_zero hpos) := by
  have hc : c⁻¹ ≠ 0 := inv_ne_zero (physicalHalfplane_multiplier_ne_zero hpos)
  rw [physicalHalfplaneArg, Circle.exp_add,
    circle_exp_arg_vector_ratio _ _ (physicalHalfplane_ne_zero hpos) hc,
    ← euclideanDirection_arg _ hc, Circle.exp_arg]
  simp

theorem physicalHalfplane_blend {c u v : ℂ}
    (hu : u ∈ physicalHalfplane c) (hv : v ∈ physicalHalfplane c)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    euclideanCornerBlend u v t ∈ physicalHalfplane c := by
  have hu' : 0 < (c * u).re := hu
  have hv' : 0 < (c * v).re := hv
  change 0 < (c * euclideanCornerBlend u v t).re
  have he : (c * euclideanCornerBlend u v t).re =
      (1 - t) * (c * u).re + t * (c * v).re := by
    simp [euclideanCornerBlend, Complex.mul_re, Complex.mul_im]
    ring
  rw [he]
  have h₁ := mul_nonneg (sub_nonneg.mpr ht.2) hu'.le
  have h₂ := mul_nonneg ht.1 hv'.le
  by_cases ht0 : t = 0
  · simpa [ht0] using hu'
  · exact add_pos_of_nonneg_of_pos h₁
      (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hv')

/-- The local branch gives the principal corner, not merely a congruence
modulo 2π. The accepted straight-blend theorem fixes the integer. -/
theorem physicalHalfplaneArg_corner {c u v : ℂ}
    (hu : u ∈ physicalHalfplane c) (hv : v ∈ physicalHalfplane c)
    (hc : v / u ∈ Complex.slitPlane) :
    physicalHalfplaneArg c v - physicalHalfplaneArg c u = Complex.arg (v / u) := by
  have hcont : Continuous (fun t : Icc (0 : ℝ) 1 => euclideanCornerBlend u v t) := by
    unfold euclideanCornerBlend
    fun_prop
  have he := euclideanCornerBlend_lift_increment (physicalHalfplane_ne_zero hu) hc
    (physicalHalfplaneArg_continuous hcont (fun t => physicalHalfplane_blend hu hv t.2))
    (fun t => physicalHalfplaneArg_lift (physicalHalfplane_blend hu hv t.2))
  simpa only [Set.Icc.coe_zero, Set.Icc.coe_one, euclideanCornerBlend_zero, euclideanCornerBlend_one] using he

/-- Exact increment comparison with an arbitrary lift. -/
theorem physicalHalfplane_lift_increment {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {v : X → ℂ} {c : ℂ} (hv : Continuous v)
    (hpos : ∀ x, v x ∈ physicalHalfplane c) {θ : X → ℝ} (hθ : Continuous θ)
    (hlift : ∀ x, Complex.exp ((θ x : ℂ) * Complex.I) = v x / (‖v x‖ : ℂ))
    (x y : X) :
    θ y - θ x = physicalHalfplaneArg c (v y) - physicalHalfplaneArg c (v x) := by
  apply euclidean_angle_lift_increment_eq hθ (physicalHalfplaneArg_continuous hv hpos)
  intro t
  apply Circle.ext
  exact (hlift t).trans (congrArg (fun z : Circle => (z : ℂ))
    (physicalHalfplaneArg_lift (hpos t))).symm

/-- A positive physical projection derivative makes an actual arc injective. -/
theorem physical_positive_projection_strictMonoOn {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (c : ℂ) {a b : ℝ}
    (hpos : ∀ t ∈ Icc a b, deriv f t ∈ physicalHalfplane c) :
    StrictMonoOn (fun t => (c * f t).re) (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    ((Complex.continuous_re.comp (continuous_const.mul hf.continuous)).continuousOn)
  intro t ht
  have hd : HasDerivAt (fun t => (c * f t).re) (c * deriv f t).re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      (((hf.differentiable (by norm_num)) t).hasDerivAt.const_mul c)
  change 0 < deriv (fun x : ℝ => (c * f x).re) t
  rw [hd.deriv]
  exact hpos t (interior_subset ht)

theorem physical_positive_projection_injOn {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (c : ℂ) {a b : ℝ}
    (hpos : ∀ t ∈ Icc a b, deriv f t ∈ physicalHalfplane c) : InjOn f (Icc a b) := by
  intro s hs t ht heq
  exact (physical_positive_projection_strictMonoOn hf c hpos).injOn hs ht
    (congrArg (fun z : ℂ => (c * z).re) heq)

end RepulsiveCoulomb
