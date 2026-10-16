module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic

@[expose] public section

/-! Genuine prerequisites for the Euclidean total-turn problem.

The angle lifts in this file are constructed from the exponential covering map.
The finite turn is the sum of actual lifted tangent increments and principal
arguments of the actual adjacent tangent ratios.  Its quantization is proved;
no claim that its integer is `1` or `-1` is made here.  That last assertion uses
Jordan injectivity and is a separate missing geometric theorem. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

/-- The actual normalized direction of a nonzero complex vector. -/
def euclideanDirection (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / (‖z‖ : ℂ), by
    have hn : ‖z / (‖z‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self (norm_ne_zero_iff.mpr hz)]
    exact mem_sphere_zero_iff_norm.mpr hn⟩

@[simp] theorem euclideanDirection_coe (z : ℂ) (hz : z ≠ 0) :
    (euclideanDirection z hz : ℂ) = z / (‖z‖ : ℂ) := rfl

theorem euclideanDirection_arg (z : ℂ) (hz : z ≠ 0) :
    Complex.arg (euclideanDirection z hz : ℂ) = Complex.arg z := by
  change Complex.arg (z / (‖z‖ : ℂ)) = Complex.arg z
  rw [div_eq_mul_inv, ← Complex.ofReal_inv,
    Complex.arg_mul_real (inv_pos.mpr (norm_pos_iff.mpr hz))]

theorem euclideanDirection_div (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    euclideanDirection (z / w) (div_ne_zero hz hw) =
      euclideanDirection z hz / euclideanDirection w hw := by
  apply Subtype.ext
  simp only [euclideanDirection_coe, Circle.coe_div, norm_div, Complex.ofReal_div]
  field_simp

theorem circle_exp_arg_vector_ratio (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    Circle.exp (Complex.arg (z / w)) =
      euclideanDirection z hz / euclideanDirection w hw := by
  rw [← euclideanDirection_div z w hz hw,
    ← euclideanDirection_arg (z / w) (div_ne_zero hz hw), Circle.exp_arg]

theorem continuous_euclideanDirection {X : Type*} [TopologicalSpace X]
    {v : X → ℂ} (hv : Continuous v) (hne : ∀ x, v x ≠ 0) :
    Continuous (fun x => euclideanDirection (v x) (hne x)) := by
  apply Continuous.subtype_mk
  exact hv.div (Complex.continuous_ofReal.comp hv.norm)
    (fun x => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hne x)))

/-- Every continuous nonzero vector field on a simply connected, locally
path-connected domain has a real angle lift, with any permitted initial angle. -/
theorem exists_euclidean_angle_lift {X : Type*} [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {v : X → ℂ} (hv : Continuous v) (hne : ∀ x, v x ≠ 0)
    (x₀ : X) (θ₀ : ℝ)
    (hθ₀ : Circle.exp θ₀ = euclideanDirection (v x₀) (hne x₀)) :
    ∃ θ : X → ℝ, Continuous θ ∧ θ x₀ = θ₀ ∧
      ∀ x, Circle.exp (θ x) = euclideanDirection (v x) (hne x) := by
  let V : C(X, Circle) :=
    ⟨fun x => euclideanDirection (v x) (hne x), continuous_euclideanDirection hv hne⟩
  obtain ⟨θ, ⟨hbase, hlift⟩, _⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts V x₀ θ₀ hθ₀
  exact ⟨θ, θ.continuous, hbase, fun x => congrFun hlift x⟩

/-- The interval version uses path lifting directly, without asking for an
angle-lift certificate as input. -/
theorem exists_interval_euclidean_angle_lift
    {v : Icc (0 : ℝ) 1 → ℂ} (hv : Continuous v) (hne : ∀ t, v t ≠ 0) :
    ∃ θ : Icc (0 : ℝ) 1 → ℝ, Continuous θ ∧
      ∀ t, Complex.exp ((θ t : ℂ) * Complex.I) = v t / (‖v t‖ : ℂ) := by
  let V : C(Icc (0 : ℝ) 1, Circle) :=
    ⟨fun x => euclideanDirection (v x) (hne x), continuous_euclideanDirection hv hne⟩
  obtain ⟨θ, hlift, _⟩ := Circle.isCoveringMap_exp.exists_path_lifts V
    (Complex.arg (V 0 : ℂ)) (Circle.exp_arg (V 0)).symm
  refine ⟨θ, θ.continuous, fun t => ?_⟩
  exact congrArg (fun z : Circle => (z : ℂ)) (congrFun hlift t)

/-- In particular, regular `C¹` edges have the actual tangent-angle lifts
required by total-turn statements. -/
theorem exists_regular_edge_tangent_angle_lift {η : ℝ → ℂ}
    (hη : ContDiff ℝ 1 η) (hne : ∀ t ∈ Icc (0 : ℝ) 1, deriv η t ≠ 0) :
    ∃ θ : Icc (0 : ℝ) 1 → ℝ, Continuous θ ∧
      ∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
        deriv η t / (‖deriv η t‖ : ℂ) := by
  apply exists_interval_euclidean_angle_lift
  · exact hη.continuous_deriv (by norm_num) |>.comp continuous_subtype_val
  · exact fun t => hne t t.2

/-- The increment of an angle lift is intrinsic: any two continuous lifts on
a connected domain differ by a constant, so their endpoint increments agree. -/
theorem euclidean_angle_lift_increment_eq {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {θ φ : X → ℝ} (hθ : Continuous θ) (hφ : Continuous φ)
    (hexp : ∀ x, Circle.exp (θ x) = Circle.exp (φ x)) (x y : X) :
    θ y - θ x = φ y - φ x := by
  have hconst : θ y - φ y = θ x - φ x :=
    Circle.isCoveringMap_exp.const_of_comp (hθ.sub hφ)
      (by
        intro a b
        change Circle.exp (θ a - φ a) = Circle.exp (θ b - φ b)
        rw [Circle.exp_sub, Circle.exp_sub, hexp a, hexp b, div_self', div_self']) y x
  linarith

/-- Actual finite signed turn with an explicitly supplied cyclic successor.
Taking `σ` to be the usual cyclic permutation of `Fin n` gives the requested
closed-loop convention. -/
def euclideanFiniteTurn {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (v₀ v₁ : ι → ℂ) (θ₀ θ₁ : ι → ℝ) : ℝ :=
  ∑ i, (θ₁ i - θ₀ i + Complex.arg (v₀ (σ i) / v₁ i))

private theorem circle_exp_fintype_sum {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    Circle.exp (∑ i, f i) = ∏ i, Circle.exp (f i) := by
  classical
  have aux (s : Finset ι) : Circle.exp (∑ i ∈ s, f i) = ∏ i ∈ s, Circle.exp (f i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [ha, Circle.exp_add, ih]
  exact aux Finset.univ

/-- The raw sum of tangent increments and principal corners is an integer
multiple of `2π`. This is genuine closure/angle algebra, not the Jordan theorem:
immersed loops of every rotation index satisfy the same result. -/
theorem euclideanFiniteTurn_integer {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (v₀ v₁ : ι → ℂ) (θ₀ θ₁ : ι → ℝ)
    (hv₀ : ∀ i, v₀ i ≠ 0) (hv₁ : ∀ i, v₁ i ≠ 0)
    (hθ₀ : ∀ i, Circle.exp (θ₀ i) = euclideanDirection (v₀ i) (hv₀ i))
    (hθ₁ : ∀ i, Circle.exp (θ₁ i) = euclideanDirection (v₁ i) (hv₁ i)) :
    ∃ k : ℤ, euclideanFiniteTurn σ v₀ v₁ θ₀ θ₁ = k * (2 * Real.pi) := by
  apply Circle.exp_eq_one.mp
  unfold euclideanFiniteTurn
  rw [circle_exp_fintype_sum]
  have hterm (i : ι) :
      Circle.exp (θ₁ i - θ₀ i + Complex.arg (v₀ (σ i) / v₁ i)) =
        euclideanDirection (v₀ (σ i)) (hv₀ (σ i)) /
          euclideanDirection (v₀ i) (hv₀ i) := by
    rw [Circle.exp_add, Circle.exp_sub, hθ₀, hθ₁,
      circle_exp_arg_vector_ratio _ _ (hv₀ (σ i)) (hv₁ i)]
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  simp_rw [hterm]
  rw [Finset.prod_div_distrib]
  apply div_eq_one.mpr
  exact Equiv.prod_comp σ (fun i => euclideanDirection (v₀ i) (hv₀ i))

end RepulsiveCoulomb
