module

public import LeanResearch.RepulsiveCoulomb.JordanOrientedNormalJump
public import LeanResearch.RepulsiveCoulomb.JordanArgumentHomotopy

@[expose] public section

/-! A continuous simple periodic Jordan loop with just one regular basepoint
has actual inside argument increment +2π or -2π. The two small normal observers
must lie in opposite components: equal-component argument constancy contradicts
the constructed nonzero normal jump. This classifies a piecewise-smooth loop
BEFORE smoothing and avoids circular use of interior preservation. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Every continuous simple loop with one nonzero actual derivative has
inside winding +1 or -1. No smoothness away from that basepoint, local side
choice, winding value, or inside-preserving smoothing is an input. -/
theorem one_regular_simple_loop_inside_argument_classification
    {γ : ℝ → ℂ} (hγ : Continuous γ) (hdiff : DifferentiableAt ℝ γ 0)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hd : deriv γ 0 ≠ 0)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hK : IsCompact (closure U))
    (hcover : U ∪ V = (γ '' Icc (0 : ℝ) 1)ᶜ) :
    (∀ w ∈ U, ∀ θ : Icc (0 : ℝ) 1 → ℝ, Continuous θ →
      (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
        (γ t - w) / (‖γ t - w‖ : ℂ)) → θ 1 - θ 0 = 2 * Real.pi) ∨
    (∀ w ∈ U, ∀ θ : Icc (0 : ℝ) 1 → ℝ, Continuous θ →
      (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
        (γ t - w) / (‖γ t - w‖ : ℂ)) → θ 1 - θ 0 = -(2 * Real.pi)) := by
  let Γ : Icc (0 : ℝ) 1 → ℂ := fun t => γ t
  have hΓ : Continuous Γ := hγ.comp continuous_subtype_val
  have hclose : Γ 0 = Γ 1 := by simpa [Γ] using (hp 0).symm
  have himage : range Γ = γ '' Icc (0 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, rfl⟩
  have hcoverΓ : U ∪ V = (range Γ)ᶜ := by rwa [himage]
  have havoidU : ∀ w ∈ U, ∀ t, Γ t ≠ w := by
    intro w hw t heq
    have hn : w ∈ (range Γ)ᶜ := hcoverΓ ▸ Or.inl hw
    exact hn ⟨t, heq⟩
  obtain ⟨r, hr, hall⟩ := exists_simple_loop_oriented_normal_jump hγ hdiff hp hinj hd
  obtain ⟨hpa, hma, hjump⟩ := hall r hr le_rfl
  let wp := γ 0 + (r : ℂ) * Complex.I * deriv γ 0
  let wm := γ 0 - (r : ℂ) * Complex.I * deriv γ 0
  have hwpC : wp ∈ (range Γ)ᶜ := by rintro ⟨t, ht⟩; exact hpa t t.2 ht
  have hwmC : wm ∈ (range Γ)ᶜ := by rintro ⟨t, ht⟩; exact hma t t.2 ht
  obtain ⟨θp, hθp, hθplift⟩ := exists_interval_euclidean_angle_lift
    (hΓ.sub continuous_const) (fun t => sub_ne_zero.mpr (hpa t t.2))
  obtain ⟨θm, hθm, hθmlift⟩ := exists_interval_euclidean_angle_lift
    (hΓ.sub continuous_const) (fun t => sub_ne_zero.mpr (hma t t.2))
  have hj := hjump θp θm hθp hθm hθplift hθmlift
  have hwp : wp ∈ U ∪ V := hcoverΓ.symm ▸ hwpC
  have hwm : wm ∈ U ∪ V := hcoverΓ.symm ▸ hwmC
  rcases hwp with hpu | hpv <;> rcases hwm with hmu | hmv
  · have heq := loop_argument_increment_constant_on_component Γ hΓ hclose
      hU hUc havoidU hpu hmu θp θm hθp hθm hθplift hθmlift
    nlinarith [Real.pi_pos]
  · have hmzero := jordan_outside_argument_increment_zero Γ hΓ hclose hK hV hVc
      hcoverΓ hmv θm hθm hθmlift
    have hpinc : θp 1 - θp 0 = 2 * Real.pi := by linarith
    left
    intro w hw θ hθ hlift
    have heq := loop_argument_increment_constant_on_component Γ hΓ hclose
      hU hUc havoidU hw hpu θ θp hθ hθp hlift hθplift
    exact heq.trans hpinc
  · have hpzero := jordan_outside_argument_increment_zero Γ hΓ hclose hK hV hVc
      hcoverΓ hpv θp hθp hθplift
    have hminc : θm 1 - θm 0 = -(2 * Real.pi) := by linarith
    right
    intro w hw θ hθ hlift
    have heq := loop_argument_increment_constant_on_component Γ hΓ hclose
      hU hUc havoidU hw hmu θ θm hθ hθm hlift hθmlift
    exact heq.trans hminc
  · have hpzero := jordan_outside_argument_increment_zero Γ hΓ hclose hK hV hVc
      hcoverΓ hpv θp hθp hθplift
    have hmzero := jordan_outside_argument_increment_zero Γ hΓ hclose hK hV hVc
      hcoverΓ hmv θm hθm hθmlift
    nlinarith [Real.pi_pos]

/-- Choosing the positive orientation by one actual inside argument lift
forces every sufficiently small left normal point inside and right normal
point outside. This is the actual local side identification used at edges. -/
theorem positive_inside_argument_forces_left_normal
    {γ : ℝ → ℂ} (hγ : Continuous γ) (hdiff : DifferentiableAt ℝ γ 0)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hd : deriv γ 0 ≠ 0)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hK : IsCompact (closure U))
    (hcover : U ∪ V = (γ '' Icc (0 : ℝ) 1)ᶜ)
    {w : ℂ} (hw : w ∈ U) {θ : Icc (0 : ℝ) 1 → ℝ} (hθ : Continuous θ)
    (hlift : ∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
      (γ t - w) / (‖γ t - w‖ : ℂ)) (hturn : θ 1 - θ 0 = 2 * Real.pi) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      γ 0 + (ε : ℂ) * Complex.I * deriv γ 0 ∈ U ∧
      γ 0 - (ε : ℂ) * Complex.I * deriv γ 0 ∈ V := by
  let Γ : Icc (0 : ℝ) 1 → ℂ := fun t => γ t
  have hΓ : Continuous Γ := hγ.comp continuous_subtype_val
  have hclose : Γ 0 = Γ 1 := by simpa [Γ] using (hp 0).symm
  have himage : range Γ = γ '' Icc (0 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, rfl⟩
  have hcoverΓ : U ∪ V = (range Γ)ᶜ := by rwa [himage]
  have havoidU : ∀ z ∈ U, ∀ t, Γ t ≠ z := by
    intro z hz t heq
    have hn : z ∈ (range Γ)ᶜ := hcoverΓ ▸ Or.inl hz
    exact hn ⟨t, heq⟩
  have hins : ∀ z ∈ U, ∀ ψ : Icc (0 : ℝ) 1 → ℝ, Continuous ψ →
      (∀ t, Complex.exp ((ψ t : ℂ) * Complex.I) =
        (Γ t - z) / (‖Γ t - z‖ : ℂ)) → ψ 1 - ψ 0 = 2 * Real.pi := by
    intro z hz ψ hψ hψlift
    exact (loop_argument_increment_constant_on_component Γ hΓ hclose
      hU hUc havoidU hz hw ψ θ hψ hθ hψlift hlift).trans hturn
  obtain ⟨r, hr, hall⟩ := exists_simple_loop_oriented_normal_jump hγ hdiff hp hinj hd
  refine ⟨r, hr, ?_⟩
  intro ε hε hεr
  obtain ⟨hpa, hma, hjump⟩ := hall ε hε hεr
  let wp := γ 0 + (ε : ℂ) * Complex.I * deriv γ 0
  let wm := γ 0 - (ε : ℂ) * Complex.I * deriv γ 0
  have hwpC : wp ∈ (range Γ)ᶜ := by rintro ⟨t, ht⟩; exact hpa t t.2 ht
  have hwmC : wm ∈ (range Γ)ᶜ := by rintro ⟨t, ht⟩; exact hma t t.2 ht
  obtain ⟨θp, hθp, hθplift⟩ := exists_interval_euclidean_angle_lift
    (hΓ.sub continuous_const) (fun t => sub_ne_zero.mpr (hpa t t.2))
  obtain ⟨θm, hθm, hθmlift⟩ := exists_interval_euclidean_angle_lift
    (hΓ.sub continuous_const) (fun t => sub_ne_zero.mpr (hma t t.2))
  have hj := hjump θp θm hθp hθm hθplift hθmlift
  have hwp : wp ∈ U ∪ V := hcoverΓ.symm ▸ hwpC
  have hwm : wm ∈ U ∪ V := hcoverΓ.symm ▸ hwmC
  rcases hwp with hpu | hpv <;> rcases hwm with hmu | hmv
  · have hpi := hins wp hpu θp hθp hθplift
    have hmi := hins wm hmu θm hθm hθmlift
    nlinarith [Real.pi_pos]
  · exact ⟨hpu, hmv⟩
  · have hpzero := jordan_outside_argument_increment_zero Γ hΓ hclose hK hV hVc
      hcoverΓ hpv θp hθp hθplift
    have hmi := hins wm hmu θm hθm hθmlift
    nlinarith [Real.pi_pos]
  · have hpzero := jordan_outside_argument_increment_zero Γ hΓ hclose hK hV hVc
      hcoverΓ hpv θp hθp hθplift
    have hmzero := jordan_outside_argument_increment_zero Γ hΓ hclose hK hV hVc
      hcoverΓ hmv θm hθm hθmlift
    nlinarith [Real.pi_pos]

end RepulsiveCoulomb
