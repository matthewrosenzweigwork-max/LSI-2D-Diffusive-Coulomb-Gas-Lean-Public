import LeanResearch.RepulsiveCoulomb.JordanPositiveSpeedWinding
import LeanResearch.RepulsiveCoulomb.JordanSmoothTotalTurn

/-! Actual inside winding agrees with actual tangent turn for every regular
C¹ periodic simple loop. A support point is constructed, its two possible
horizontal orientations are treated by actual reversal, and basepoint shifts
are handled by covering-lift uniqueness. No orientation certificate, ambient
homeomorphism or Jordan winding value is assumed. Records-only draft. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem periodic_loop_closed_image_eq_range {γ : ℝ → ℂ}
    (hp : Function.Periodic γ 1) : γ '' Icc (0 : ℝ) 1 = range γ := by
  apply Subset.antisymm (image_subset_range _ _)
  rintro z ⟨t, rfl⟩
  obtain ⟨s, hs, hts⟩ := hp.exists_mem_Ico₀ (by norm_num) t
  exact ⟨s, ⟨hs.1, hs.2.le⟩, hts.symm⟩

theorem periodic_loop_shift_closed_image {γ : ℝ → ℂ}
    (hp : Function.Periodic γ 1) (a : ℝ) :
    (fun t => γ (t + a)) '' Icc (0 : ℝ) 1 = γ '' Icc (0 : ℝ) 1 := by
  have hp' : Function.Periodic (fun t => γ (t + a)) 1 := by
    intro t
    change γ (t + 1 + a) = γ (t + a)
    rw [show t + 1 + a = (t + a) + 1 by ring, hp]
  rw [periodic_loop_closed_image_eq_range hp', periodic_loop_closed_image_eq_range hp]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t + a, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t - a, by congr 1; ring⟩

theorem loop_reverse_closed_image (γ : ℝ → ℂ) :
    (fun t => γ (1 - t)) '' Icc (0 : ℝ) 1 = γ '' Icc (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    exact ⟨1 - t, by constructor <;> linarith [ht.1, ht.2], rfl⟩
  · rintro z ⟨t, ht, rfl⟩
    refine ⟨1 - t, by constructor <;> linarith [ht.1, ht.2], ?_⟩
    congr 1
    ring

/-- Covering uniqueness gives basepoint-independent increments for actual
periodic nonzero vector fields, including position-minus-observation vectors. -/
theorem periodic_vector_argument_increment {v : ℝ → ℂ}
    (hp : Function.Periodic v 1) {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hlift : ∀ t, Complex.exp ((Ψ t : ℂ) * Complex.I) = v t / (‖v t‖ : ℂ))
    (a : ℝ) : Ψ (a + 1) - Ψ a = Ψ 1 - Ψ 0 := by
  have hper (t : ℝ) : Circle.exp (Ψ (t + 1)) = Circle.exp (Ψ t) := by
    apply Circle.ext
    change Complex.exp ((Ψ (t + 1) : ℂ) * Complex.I) = Complex.exp ((Ψ t : ℂ) * Complex.I)
    rw [hlift, hlift, hp]
  have hc : Continuous (fun t => Ψ (t + 1) - Ψ t) :=
    (hΨ.comp (continuous_id.add continuous_const)).sub hΨ
  have he (t : ℝ) : Circle.exp (Ψ (t + 1) - Ψ t) = 1 := by
    rw [Circle.exp_sub, hper, div_self']
  have h := Circle.isCoveringMap_exp.const_of_comp hc
    (by intro x y; exact (he x).trans (he y).symm) a 0
  simpa only [zero_add] using h

private def argumentReverseUnit (t : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

private theorem argumentReverseUnit_continuous : Continuous argumentReverseUnit :=
  (continuous_const.sub continuous_subtype_val).subtype_mk _

/-- At a constructed horizontal support, either traversal direction gives
exact agreement between inside argument increment and tangent increment. -/
theorem supported_loop_inside_argument_eq_tangent
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    {c : ℝ} (hc : c ≠ 0) (hbase : deriv γ 0 = (c : ℂ))
    (hsupport : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (γ t - γ 0).im)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hK : IsCompact (closure U))
    (hfront : frontier U = γ '' Icc (0 : ℝ) 1)
    (hcover : U ∪ V = (γ '' Icc (0 : ℝ) 1)ᶜ)
    {w : ℂ} (hw : w ∈ U)
    {θ ψ : Icc (0 : ℝ) 1 → ℝ} (hθ : Continuous θ) (hψ : Continuous ψ)
    (hθlift : ∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
      deriv γ t / (‖deriv γ t‖ : ℂ))
    (hψlift : ∀ t, Complex.exp ((ψ t : ℂ) * Complex.I) =
      (γ t - w) / (‖γ t - w‖ : ℂ)) :
    ψ 1 - ψ 0 = θ 1 - θ 0 := by
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · let η : ℝ → ℂ := fun t => γ (1 - t)
    have hη : ContDiff ℝ 1 η := by dsimp [η]; fun_prop
    have hpη : Function.Periodic η 1 := by
      intro t
      change γ (1 - (t + 1)) = γ (1 - t)
      rw [show 1 - (t + 1) = (1 - t) - 1 by ring, hp.sub_eq]
    have hinjη : InjOn η (Ico (0 : ℝ) 1) := by
      intro s hs t ht heq
      have he := periodic_simple_loop_injOn_Ioc hp hinj
        (show 1 - s ∈ Ioc (0 : ℝ) 1 by constructor <;> linarith [hs.1, hs.2])
        (show 1 - t ∈ Ioc (0 : ℝ) 1 by constructor <;> linarith [ht.1, ht.2]) heq
      linarith
    have hderiv (t : ℝ) : deriv η t = -deriv γ (1 - t) := deriv_comp_const_sub _ _ _
    have hbaseη : 0 < (deriv η 0).re := by
      rw [hderiv, sub_zero, periodic_loop_deriv_one_eq_zero hp, hbase]
      simpa only [Complex.neg_re, Complex.ofReal_re] using neg_pos.mpr hneg
    have h10 : γ 1 = γ 0 := by simpa using hp 0
    have hsupη : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (η t - η 0).im := by
      intro t ht
      simp only [η, sub_zero, h10]
      exact hsupport _ (by constructor <;> linarith [ht.1, ht.2])
    have himage : η '' Icc (0 : ℝ) 1 = γ '' Icc (0 : ℝ) 1 := loop_reverse_closed_image γ
    let ψr : Icc (0 : ℝ) 1 → ℝ := fun t => ψ (argumentReverseUnit t)
    have hψr : Continuous ψr := hψ.comp argumentReverseUnit_continuous
    have hψrlift (t : Icc (0 : ℝ) 1) : Complex.exp ((ψr t : ℂ) * Complex.I) =
        (η t - w) / (‖η t - w‖ : ℂ) := hψlift (argumentReverseUnit t)
    have hwr := (positive_real_supported_loop_actual_winding hη hpη hinjη hbaseη hsupη
      hU hUc hV hVc hK (hfront.trans himage.symm) (by rwa [himage])).1
      w hw ψr hψr hψrlift
    have hr0 : argumentReverseUnit 0 = 1 := by apply Subtype.ext; simp [argumentReverseUnit]
    have hr1 : argumentReverseUnit 1 = 0 := by apply Subtype.ext; simp [argumentReverseUnit]
    change ψ (argumentReverseUnit 1) - ψ (argumentReverseUnit 0) = _ at hwr
    rw [hr0, hr1] at hwr
    have htr := regular_simple_supported_loop_total_turn_negative_speed hγ hp hinj hreg
      hneg hbase hsupport hθ hθlift
    linarith
  · have hwinding := (positive_real_supported_loop_actual_winding hγ hp hinj
      (by simpa only [hbase, Complex.ofReal_re] using hpos) hsupport
      hU hUc hV hVc hK hfront hcover).1 w hw ψ hψ hψlift
    have hturn := regular_simple_supported_loop_total_turn_positive_speed hγ hp hinj hreg
      hpos hbase hsupport hθ hθlift
    exact hwinding.trans hturn.symm

/-- The signed actual winding about every point of the bounded Jordan region
is the actual tangent turn of an arbitrary regular simple periodic C¹ loop.
The orientation is derived from the curve, rather than supplied as a sign. -/
theorem regular_simple_periodic_loop_inside_argument_eq_turn
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hregular : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hK : IsCompact (closure U))
    (hfront : frontier U = γ '' Icc (0 : ℝ) 1)
    (hcover : U ∪ V = (γ '' Icc (0 : ℝ) 1)ᶜ)
    {w : ℂ} (hw : w ∈ U)
    {θ ψ : Icc (0 : ℝ) 1 → ℝ} (hθ : Continuous θ) (hψ : Continuous ψ)
    (hθlift : ∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
      deriv γ t / (‖deriv γ t‖ : ℂ))
    (hψlift : ∀ t, Complex.exp ((ψ t : ℂ) * Complex.I) =
      (γ t - w) / (‖γ t - w‖ : ℂ)) :
    ψ 1 - ψ 0 = θ 1 - θ 0 := by
  have hreg := periodic_loop_regular_everywhere hp hregular
  have havo : ∀ t : ℝ, γ t - w ≠ 0 := by
    intro t hzero
    have hwC : w ∈ (γ '' Icc (0 : ℝ) 1)ᶜ := hcover ▸ Or.inl hw
    apply hwC
    rw [periodic_loop_closed_image_eq_range hp]
    exact ⟨t, sub_eq_zero.mp hzero⟩
  obtain ⟨Φ, hΦ, _, hΦlift⟩ := exists_euclidean_angle_lift hγ.continuous_deriv_one hreg
    0 (Complex.arg (deriv γ 0)) (by
      rw [← euclideanDirection_arg (deriv γ 0) (hreg 0)]
      exact Circle.exp_arg _)
  obtain ⟨Ψ, hΨ, _, hΨlift⟩ := exists_euclidean_angle_lift
    (hγ.continuous.sub continuous_const) havo 0 (Complex.arg (γ 0 - w)) (by
      rw [← euclideanDirection_arg (γ 0 - w) (havo 0)]
      exact Circle.exp_arg _)
  have hΨraw (t : ℝ) : Complex.exp ((Ψ t : ℂ) * Complex.I) =
      (γ t - w) / (‖γ t - w‖ : ℂ) :=
    congrArg (fun z : Circle => (z : ℂ)) (hΨlift t)
  have hθΦ : θ 1 - θ 0 = Φ 1 - Φ 0 := by
    have h := euclidean_angle_lift_increment_eq hθ (hΦ.comp continuous_subtype_val)
      (fun t => by
        change Circle.exp (θ t) = Circle.exp (Φ t)
        rw [hΦlift]
        apply Circle.ext
        exact hθlift t) (0 : Icc (0 : ℝ) 1) 1
    simpa using h
  have hψΨ : ψ 1 - ψ 0 = Ψ 1 - Ψ 0 := by
    have h := euclidean_angle_lift_increment_eq hψ (hΨ.comp continuous_subtype_val)
      (fun t => by
        change Circle.exp (ψ t) = Circle.exp (Ψ t)
        rw [hΨlift]
        apply Circle.ext
        exact hψlift t) (0 : Icc (0 : ℝ) 1) 1
    simpa using h
  obtain ⟨a, ha, him, hre, hsupport⟩ := exists_regular_periodic_horizontal_support hγ hp hregular
  let η : ℝ → ℂ := fun t => γ (t + a)
  have hη : ContDiff ℝ 1 η := by dsimp [η]; fun_prop
  have hpη : Function.Periodic η 1 := by
    intro t
    change γ (t + 1 + a) = γ (t + a)
    rw [show t + 1 + a = t + a + 1 by ring, hp]
  have hderiv (t : ℝ) : deriv η t = deriv γ (t + a) := deriv_comp_add_const _ _ _
  have hregη : ∀ t ∈ Icc (0 : ℝ) 1, deriv η t ≠ 0 := by
    intro t _
    rw [hderiv]
    exact hreg _
  have hbase : deriv η 0 = ((deriv γ a).re : ℂ) := by
    rw [hderiv, zero_add]
    apply Complex.ext <;> simp [him]
  have hsupη : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (η t - η 0).im := by
    intro t _
    simpa only [η, zero_add] using hsupport (t + a)
  let φ : Icc (0 : ℝ) 1 → ℝ := fun t => Φ (t + a)
  let χ : Icc (0 : ℝ) 1 → ℝ := fun t => Ψ (t + a)
  have hφ : Continuous φ := hΦ.comp (continuous_subtype_val.add continuous_const)
  have hχ : Continuous χ := hΨ.comp (continuous_subtype_val.add continuous_const)
  have hφlift (t : Icc (0 : ℝ) 1) : Complex.exp ((φ t : ℂ) * Complex.I) =
      deriv η t / (‖deriv η t‖ : ℂ) := by
    rw [hderiv]
    exact congrArg (fun z : Circle => (z : ℂ)) (hΦlift (t + a))
  have hχlift (t : Icc (0 : ℝ) 1) : Complex.exp ((χ t : ℂ) * Complex.I) =
      (η t - w) / (‖η t - w‖ : ℂ) := hΨraw (t + a)
  have himage : η '' Icc (0 : ℝ) 1 = γ '' Icc (0 : ℝ) 1 := periodic_loop_shift_closed_image hp a
  have hshift := supported_loop_inside_argument_eq_tangent hη hpη
    (periodic_simple_loop_shift_injOn hp hinj ha) hregη hre hbase hsupη
    hU hUc hV hVc hK (hfront.trans himage.symm) (by rwa [himage]) hw hφ hχ hφlift hχlift
  have hiΦ : φ 1 - φ 0 = Φ 1 - Φ 0 := by
    simpa [φ, add_comm] using periodic_tangent_angle_increment hp hreg hΦ hΦlift a
  have hpv : Function.Periodic (fun t => γ t - w) 1 := by
    intro t
    change γ (t + 1) - w = γ t - w
    rw [hp]
  have hiΨ : χ 1 - χ 0 = Ψ 1 - Ψ 0 := by
    simpa [χ, add_comm] using periodic_vector_argument_increment hpv hΨ hΨraw a
  exact hψΨ.trans (hiΨ.symm.trans (hshift.trans (hiΦ.trans hθΦ.symm)))

end RepulsiveCoulomb
