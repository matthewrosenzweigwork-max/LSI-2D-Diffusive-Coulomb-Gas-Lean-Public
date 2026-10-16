module

public import LeanResearch.RepulsiveCoulomb.JordanSmoothSecantSquare
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Analysis.Normed.Module.Connected

@[expose] public section

/-! Genuine angle-increment homotopy invariance and zero winding on the actual
unbounded Jordan side. Continuous square angle lifts are constructed. No
winding, flux, or sign certificate is an input. The bounded-inside value and
orientation still require a separate local boundary-crossing theorem.
Records-only phase-five candidate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- A continuous nonvanishing homotopy through closed actual vector loops
preserves the increment of any continuous real argument lifts. -/
theorem closed_vector_loop_argument_homotopy
    (F : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℂ) (hF : Continuous F)
    (hne : ∀ p, F p ≠ 0) (hclose : ∀ s, F (s, 0) = F (s, 1))
    (θ₀ θ₁ : Icc (0 : ℝ) 1 → ℝ) (hθ₀ : Continuous θ₀) (hθ₁ : Continuous θ₁)
    (hlift₀ : ∀ t, Complex.exp ((θ₀ t : ℂ) * Complex.I) = F (0, t) / (‖F (0, t)‖ : ℂ))
    (hlift₁ : ∀ t, Complex.exp ((θ₁ t : ℂ) * Complex.I) = F (1, t) / (‖F (1, t)‖ : ℂ)) :
    θ₀ 1 - θ₀ 0 = θ₁ 1 - θ₁ 0 := by
  let S := fun p => euclideanDirection (F p) (hne p)
  have hS : Continuous S := continuous_euclideanDirection hF hne
  obtain ⟨A, hA, hAlift⟩ := exists_square_circle_angle_lift S hS
  have hends (s : Icc (0 : ℝ) 1) : S (s, 1) = S (s, 0) := by
    apply Circle.ext
    simp only [S, euclideanDirection_coe, ← hclose s]
  have hDcont : Continuous (fun s : Icc (0 : ℝ) 1 => A (s, 1) - A (s, 0)) :=
    (hA.comp (continuous_id.prodMk continuous_const)).sub
      (hA.comp (continuous_id.prodMk continuous_const))
  have hDexp (s : Icc (0 : ℝ) 1) : Circle.exp (A (s, 1) - A (s, 0)) = 1 := by
    rw [Circle.exp_sub, hAlift, hAlift, hends, div_self']
  have hD := Circle.isCoveringMap_exp.const_of_comp hDcont
    (by intro a b; exact (hDexp a).trans (hDexp b).symm)
    (0 : Icc (0 : ℝ) 1) 1
  have hleft : Continuous (fun t : Icc (0 : ℝ) 1 => A (0, t)) :=
    hA.comp (continuous_const.prodMk continuous_id)
  have hright : Continuous (fun t : Icc (0 : ℝ) 1 => A (1, t)) :=
    hA.comp (continuous_const.prodMk continuous_id)
  have hi₀ := euclidean_angle_lift_increment_eq hθ₀ hleft
    (fun t => by
      change Circle.exp (θ₀ t) = Circle.exp (A (0, t))
      rw [hAlift]
      apply Circle.ext
      exact hlift₀ t) (0 : Icc (0 : ℝ) 1) 1
  have hi₁ := euclidean_angle_lift_increment_eq hθ₁ hright
    (fun t => by
      change Circle.exp (θ₁ t) = Circle.exp (A (1, t))
      rw [hAlift]
      apply Circle.ext
      exact hlift₁ t) (0 : Icc (0 : ℝ) 1) 1
  exact hi₀.trans (hD.trans hi₁.symm)

/-- The actual argument increment is constant as the observation point moves
inside a connected open subset of the curve complement. -/
theorem loop_argument_increment_constant_on_component
    (γ : Icc (0 : ℝ) 1 → ℂ) (hγ : Continuous γ) (hclose : γ 0 = γ 1)
    {V : Set ℂ} (hV : IsOpen V) (hVc : IsConnected V)
    (havoid : ∀ w ∈ V, ∀ t, γ t ≠ w)
    {w₀ w₁ : ℂ} (hw₀ : w₀ ∈ V) (hw₁ : w₁ ∈ V)
    (θ₀ θ₁ : Icc (0 : ℝ) 1 → ℝ) (hθ₀ : Continuous θ₀) (hθ₁ : Continuous θ₁)
    (hlift₀ : ∀ t, Complex.exp ((θ₀ t : ℂ) * Complex.I) =
      (γ t - w₀) / (‖γ t - w₀‖ : ℂ))
    (hlift₁ : ∀ t, Complex.exp ((θ₁ t : ℂ) * Complex.I) =
      (γ t - w₁) / (‖γ t - w₁‖ : ℂ)) :
    θ₀ 1 - θ₀ 0 = θ₁ 1 - θ₁ 0 := by
  have hj := (hV.isConnected_iff_isPathConnected.mp hVc).joinedIn w₀ hw₀ w₁ hw₁
  let δ := hj.somePath
  let F : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℂ := fun p => γ p.2 - δ p.1
  have hF : Continuous F := (hγ.comp continuous_snd).sub (δ.continuous.comp continuous_fst)
  have hFne (p : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1) : F p ≠ 0 :=
    sub_ne_zero.mpr (havoid (δ p.1) (hj.somePath_mem p.1) p.2)
  apply closed_vector_loop_argument_homotopy F hF hFne
    (fun s => by simp only [F, hclose]) θ₀ θ₁ hθ₀ hθ₁
  · intro t
    simpa only [F, Path.source] using hlift₀ t
  · intro t
    simpa only [F, Path.target] using hlift₁ t

/-- Actual zero argument increment on the outside region from Jordan
separation. Its identification uses the bounded complementary region and a
constructed far-away basepoint, not an assumed winding value. -/
theorem jordan_outside_argument_increment_zero
    (γ : Icc (0 : ℝ) 1 → ℂ) (hγ : Continuous γ) (hclose : γ 0 = γ 1)
    {U V : Set ℂ} (hK : IsCompact (closure U))
    (hV : IsOpen V) (hVc : IsConnected V)
    (hcover : U ∪ V = (range γ)ᶜ)
    {w : ℂ} (hw : w ∈ V)
    (θ : Icc (0 : ℝ) 1 → ℝ) (hθ : Continuous θ)
    (hlift : ∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
      (γ t - w) / (‖γ t - w‖ : ℂ)) : θ 1 - θ 0 = 0 := by
  obtain ⟨R, hR, hbound⟩ := (hK.union (isCompact_range hγ)).isBounded.exists_pos_norm_lt
  let w₀ : ℂ := (-R : ℝ)
  have hw₀norm : ‖w₀‖ = R := by simp [w₀, hR.le]
  have hw₀U : w₀ ∉ U := by
    intro h
    have hb := hbound w₀ (Or.inl (subset_closure h))
    rw [hw₀norm] at hb
    exact (lt_irrefl R) hb
  have hw₀C : w₀ ∉ range γ := by
    intro h
    have hb := hbound w₀ (Or.inr h)
    rw [hw₀norm] at hb
    exact (lt_irrefl R) hb
  have hw₀V : w₀ ∈ V := by
    have h : w₀ ∈ U ∪ V := hcover.symm ▸ hw₀C
    exact h.elim (fun hu => (hw₀U hu).elim) id
  have hreal (t : Icc (0 : ℝ) 1) : 0 < (γ t - w₀).re := by
    have hb := hbound (γ t) (Or.inr (mem_range_self t))
    have hre := (abs_le.mp (Complex.abs_re_le_norm (γ t))).1
    simp only [Complex.sub_re, w₀, Complex.ofReal_re]
    linarith
  have havo : ∀ z ∈ V, ∀ t, γ t ≠ z := by
    intro z hz t heq
    have hzc : z ∈ (range γ)ᶜ := hcover ▸ Or.inr hz
    exact hzc ⟨t, heq⟩
  let φ : Icc (0 : ℝ) 1 → ℝ := fun t => Complex.arg (γ t - w₀)
  have hφ : Continuous φ :=
    Complex.continuousOn_arg.comp_continuous (hγ.sub continuous_const)
      (fun t => Or.inl (hreal t))
  have hφlift (t : Icc (0 : ℝ) 1) : Complex.exp ((φ t : ℂ) * Complex.I) =
      (γ t - w₀) / (‖γ t - w₀‖ : ℂ) := by
    have hne : γ t - w₀ ≠ 0 := sub_ne_zero.mpr (havo w₀ hw₀V t)
    have h := Circle.exp_arg (euclideanDirection (γ t - w₀) hne)
    rw [euclideanDirection_arg] at h
    exact congrArg (fun z : Circle => (z : ℂ)) h
  have hinc := loop_argument_increment_constant_on_component γ hγ hclose hV hVc havo
    hw hw₀V θ φ hθ hφ hlift hφlift
  rw [hinc]
  simp only [φ, hclose, sub_self]

end RepulsiveCoulomb
