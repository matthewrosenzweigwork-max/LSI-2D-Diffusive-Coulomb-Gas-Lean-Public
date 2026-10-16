import LeanResearch.RepulsiveCoulomb.JordanOneRegularPointWinding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Records-only, uncompiled. At an actual counterclockwise circle basepoint,
the right normal is outside the enclosing disk. The accepted signed normal
jump therefore CONSTRUCTS positive winding. No winding, side, or turn equality
is an input. This adapter still needs the literal cap-periodization interface. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem lineCap_right_normal_outside_circle {p : ℂ} {R k ε : ℝ}
    (hR : 0 < R) (hp : ‖p‖ = R) (hk : 0 < k) (hε : 0 < ε) :
    R < ‖p - (ε : ℂ) * Complex.I * (k • (Complex.I * p))‖ := by
  have he : p - (ε : ℂ) * Complex.I * (k • (Complex.I * p)) =
      ((1 + ε * k : ℝ) : ℂ) * p := by
    apply Complex.ext <;>
      simp [Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 + ε * k), hp]
  nlinarith [mul_pos hε hk]

/-- Actual positive winding of any simple periodic cap realization whose
basepoint is on the positively traversed circle and whose bounded region is
inside that circle. All other points of the loop may be nonsmooth. -/
theorem lineCap_positive_inside_winding_of_circle_basepoint
    {γ : ℝ → ℂ} (hγ : Continuous γ) (hdiff : DifferentiableAt ℝ γ 0)
    (hp : Function.Periodic γ 1) (hi : InjOn γ (Ico (0 : ℝ) 1))
    (hd : deriv γ 0 ≠ 0) {R k : ℝ} (hR : 0 < R) (hk : 0 < k)
    (hnorm : ‖γ 0‖ = R) (hvel : deriv γ 0 = k • (Complex.I * γ 0))
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hK : IsCompact (closure U))
    (hcover : U ∪ V = (γ '' Icc (0 : ℝ) 1)ᶜ)
    (hball : U ⊆ ball (0 : ℂ) R) :
    ∀ w ∈ U, ∀ θ : Icc (0 : ℝ) 1 → ℝ, Continuous θ →
      (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
        (γ t - w) / (‖γ t - w‖ : ℂ)) → θ 1 - θ 0 = 2 * Real.pi := by
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
    intro w hw t he
    have hn : w ∈ (range Γ)ᶜ := hcoverΓ ▸ (show w ∈ U ∪ V from Or.inl hw)
    exact hn ⟨t, he⟩
  obtain ⟨r, hr, hall⟩ := exists_simple_loop_oriented_normal_jump hγ hdiff hp hi hd
  obtain ⟨hpa, hma, hjump⟩ := hall r hr le_rfl
  let wp := γ 0 + (r : ℂ) * Complex.I * deriv γ 0
  let wm := γ 0 - (r : ℂ) * Complex.I * deriv γ 0
  have hwpC : wp ∈ (range Γ)ᶜ := by rintro ⟨t, ht⟩; exact hpa t t.2 ht
  have hwmC : wm ∈ (range Γ)ᶜ := by rintro ⟨t, ht⟩; exact hma t t.2 ht
  have hwmN : wm ∉ U := by
    intro hw
    have hlt : ‖wm‖ < R := by simpa only [mem_ball, dist_zero_right] using hball hw
    have hgt : R < ‖wm‖ := by
      dsimp [wm]
      rw [hvel]
      exact lineCap_right_normal_outside_circle hR hnorm hk hr
    exact (not_lt_of_ge hgt.le) hlt
  have hwmV : wm ∈ V := (hcoverΓ.symm ▸ hwmC : wm ∈ U ∪ V).resolve_left hwmN
  obtain ⟨θp, hθp, hθplift⟩ := exists_interval_euclidean_angle_lift
    (hΓ.sub continuous_const) (fun t => sub_ne_zero.mpr (hpa t t.2))
  obtain ⟨θm, hθm, hθmlift⟩ := exists_interval_euclidean_angle_lift
    (hΓ.sub continuous_const) (fun t => sub_ne_zero.mpr (hma t t.2))
  have hj := hjump θp θm hθp hθm hθplift hθmlift
  have hmzero := jordan_outside_argument_increment_zero Γ hΓ hclose hK hV hVc
    hcoverΓ hwmV θm hθm hθmlift
  have hpinc : θp 1 - θp 0 = 2 * Real.pi := by linarith
  have hwpU : wp ∈ U := by
    rcases (hcoverΓ.symm ▸ hwpC : wp ∈ U ∪ V) with h | h
    · exact h
    · have hpzero := jordan_outside_argument_increment_zero Γ hΓ hclose hK hV hVc
        hcoverΓ h θp hθp hθplift
      nlinarith [Real.pi_pos]
  intro w hw θ hθ hθlift
  exact (loop_argument_increment_constant_on_component Γ hΓ hclose hU hUc havoidU
    hw hwpU θ θp hθ hθp hθlift hθplift).trans hpinc

/-- Independently obtained positive-normal intervals at the same oriented
regular point overlap. Their allowed radii may depend on the cap. -/
theorem lineCap_common_left_normal {p v : ℂ} {U W : Set ℂ}
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hU : ∀ ε, 0 < ε → ε ≤ r → p + (ε : ℂ) * Complex.I * v ∈ U)
    (hW : ∀ ε, 0 < ε → ε ≤ s → p + (ε : ℂ) * Complex.I * v ∈ W) :
    (U ∩ W).Nonempty := by
  refine ⟨p + ((min r s : ℝ) : ℂ) * Complex.I * v, ?_, ?_⟩
  · exact hU _ (lt_min hr hs) (min_le_left _ _)
  · exact hW _ (lt_min hr hs) (min_le_right _ _)

/-- Once both actual caps have the derived common normal, their actual
connected-component choices must agree. -/
theorem lineCap_same_line_side_of_common_normal {A B U W : Set ℂ}
    (hAB : Disjoint A B) (hUA : U ⊆ A) (hW : W ⊆ A ∨ W ⊆ B)
    (hmeet : (U ∩ W).Nonempty) : W ⊆ A := by
  rcases hW with h | h
  · exact h
  · obtain ⟨z, hzU, hzW⟩ := hmeet
    exact False.elim (disjoint_left.mp hAB (hUA hzU) (h hzW))

end RepulsiveCoulomb
