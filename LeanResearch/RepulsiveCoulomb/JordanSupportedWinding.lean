module

public import LeanResearch.RepulsiveCoulomb.JordanNormalSegmentJump
public import LeanResearch.RepulsiveCoulomb.JordanArgumentHomotopy
public import LeanResearch.RepulsiveCoulomb.JordanBoundedInsideSupport

@[expose] public section

/-! Actual signed inside/outside argument-increment classification for a
supported normalized regular simple loop. A normal observation point is forced
into the actual inside by the proved +2π crossing jump and actual outside zero.
No inward collar, boundary extension, winding or flux certificate is assumed.
Records-only phase-five candidate; compiler verification pending. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Every actual argument lift about a point in the bounded Jordan component
has increment +2π for the same supported orientation whose tangent turn is+2π.
Every actual argument lift about the outside has increment0. -/
theorem supported_loop_actual_inside_outside_winding
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) (hbase : deriv γ 0 = 1)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (γ t - γ 0).im)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V)
    (hK : IsCompact (closure U))
    (hfront : frontier U = γ '' Icc (0 : ℝ) 1)
    (hcover : U ∪ V = (γ '' Icc (0 : ℝ) 1)ᶜ) :
    (∀ w ∈ U, ∀ θ : Icc (0 : ℝ) 1 → ℝ, Continuous θ →
      (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
        (γ t - w) / (‖γ t - w‖ : ℂ)) → θ 1 - θ 0 = 2 * Real.pi) ∧
    (∀ w ∈ V, ∀ θ : Icc (0 : ℝ) 1 → ℝ, Continuous θ →
      (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
        (γ t - w) / (‖γ t - w‖ : ℂ)) → θ 1 - θ 0 = 0) := by
  let Γ : Icc (0 : ℝ) 1 → ℂ := fun t => γ t
  have hΓ : Continuous Γ := hγ.continuous.comp continuous_subtype_val
  have hΓclose : Γ 0 = Γ 1 := by simpa [Γ] using (hp 0).symm
  have himage : range Γ = γ '' Icc (0 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  have hcoverΓ : U ∪ V = (range Γ)ᶜ := by rwa [himage]
  have houtside : ∀ w ∈ V, ∀ θ : Icc (0 : ℝ) 1 → ℝ, Continuous θ →
      (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
        (Γ t - w) / (‖Γ t - w‖ : ℂ)) → θ 1 - θ 0 = 0 := by
    intro w hw θ hθ hlift
    exact jordan_outside_argument_increment_zero Γ hΓ hΓclose hK hV hVc hcoverΓ hw θ hθ hlift
  refine ⟨?_, houtside⟩
  obtain ⟨ε, hε, havp, havm, hjump⟩ :=
    exists_simple_loop_signed_normal_jump hγ hp hinj hbase
  let wp := γ 0 + (ε : ℂ) * Complex.I
  let wm := γ 0 - (ε : ℂ) * Complex.I
  have hwpC : wp ∉ range Γ := by
    rintro ⟨t, heq⟩
    exact havp t t.2 heq
  have hwmC : wm ∉ range Γ := by
    rintro ⟨t, heq⟩
    exact havm t t.2 heq
  have hwmU : wm ∉ U := by
    intro hwm
    have hside := bounded_jordan_region_above_support hU hK hfront hsupport wm hwm
    simp only [wm, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero] at hside
    linarith
  have hwmV : wm ∈ V := by
    have h : wm ∈ U ∪ V := hcoverΓ.symm ▸ hwmC
    exact h.elim (fun hu => (hwmU hu).elim) id
  obtain ⟨θp, hθp, hθplift⟩ := exists_interval_euclidean_angle_lift
    (hΓ.sub continuous_const) (fun t => sub_ne_zero.mpr (havp t t.2))
  obtain ⟨θm, hθm, hθmlift⟩ := exists_interval_euclidean_angle_lift
    (hΓ.sub continuous_const) (fun t => sub_ne_zero.mpr (havm t t.2))
  have hθmzero := houtside wm hwmV θm hθm hθmlift
  have hj := hjump θp θm hθp hθm hθplift hθmlift
  have hθpturn : θp 1 - θp 0 = 2 * Real.pi := by linarith
  have hwpU : wp ∈ U := by
    have h : wp ∈ U ∪ V := hcoverΓ.symm ▸ hwpC
    rcases h with hu | hv
    · exact hu
    · have hz := houtside wp hv θp hθp hθplift
      nlinarith [Real.pi_pos]
  have havoid : ∀ w ∈ U, ∀ t, Γ t ≠ w := by
    intro w hw t heq
    have hnot : w ∈ (range Γ)ᶜ := hcoverΓ ▸ Or.inl hw
    exact hnot ⟨t, heq⟩
  intro w hw θ hθ hlift
  have heq := loop_argument_increment_constant_on_component Γ hΓ hΓclose
    hU hUc havoid hw hwpU θ θp hθ hθp hlift hθplift
  exact heq.trans hθpturn

end RepulsiveCoulomb
