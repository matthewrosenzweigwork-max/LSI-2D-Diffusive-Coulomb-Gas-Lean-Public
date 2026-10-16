import LeanResearch.RepulsiveCoulomb.JordanFiniteCornerLoop
import LeanResearch.RepulsiveCoulomb.JordanFiniteC1OrientedTurn
import LeanResearch.RepulsiveCoulomb.JordanOneRegularPointWinding

/-! The literal original finite family, before smoothing, has its actual
point-argument sum equal to the increment of every lift of the constructed
periodic loop. A continuous shift homotopy transports the increment to the
regular midpoint basepoint. Inside/outside values are proved from the actual
Jordan components, without a winding or orientation certificate.

Records-only candidate. No accepted source edits or compiler invocation. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

/-- Every closed equal slot is literally its original arc, including endpoints. -/
theorem euclideanFiniteCornerArc_slot
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0)
    (k : ℕ) (hk : k ≤ n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    euclideanFiniteCornerArc f n (((k : ℝ) + t) / (n + 1 : ℝ)) = f k t := by
  have hm : (n + 1 : ℝ) ≠ 0 := by positivity
  have htimes : (n + 1 : ℝ) * (((k : ℝ) + t) / (n + 1 : ℝ)) = k + t := by
    field_simp
  change euclideanFiniteC1Paste f n ((n + 1 : ℝ) *
    (((k : ℝ) + t) / (n + 1 : ℝ))) = f k t
  rw [htimes, (euclideanFinitePaste_continuous_properties f n hf hv).2.2 k hk
    _ (by constructor <;> linarith [ht.1, ht.2]), add_sub_cancel_left]

theorem euclideanFiniteCornerArc_continuous
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) :
    Continuous (euclideanFiniteCornerArc f n) :=
  (euclideanFinitePaste_continuous_properties f n hf hv).1.comp (by fun_prop)

theorem euclideanFiniteCornerArc_endpoints
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) :
    euclideanFiniteCornerArc f n 0 = f 0 0 ∧
      euclideanFiniteCornerArc f n 1 = f n 1 := by
  constructor
  · simpa using euclideanFiniteCornerArc_slot f n hf hv 0 (Nat.zero_le n) 0 (by norm_num)
  · have hm : (n + 1 : ℝ) ≠ 0 := by positivity
    simpa only [div_self hm] using euclideanFiniteCornerArc_slot f n hf hv n le_rfl 1 (by norm_num)

theorem euclideanFiniteCornerArc_closed
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0) :
    euclideanFiniteCornerArc f n 0 = euclideanFiniteCornerArc f n 1 := by
  obtain ⟨h0, h1⟩ := euclideanFiniteCornerArc_endpoints f n hf hv
  rw [h0, h1, hclose]

/-- Joint half-open injectivity passes to the original arc with no matched jets. -/
theorem euclideanFiniteCornerArc_injOn
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t) :
    InjOn (euclideanFiniteCornerArc f n) (Ico (0 : ℝ) 1) := by
  obtain ⟨_, _, hslots⟩ := euclideanFinitePaste_continuous_properties f n hf hv
  let m : ℝ := n + 1
  have hm : 0 < m := by dsimp [m]; positivity
  intro s hs t ht heq
  have hs' : m * s ∈ Ico (0 : ℝ) (n + 1 : ℝ) :=
    ⟨mul_nonneg hm.le hs.1, by change m * s < m; nlinarith [hs.2]⟩
  have ht' : m * t ∈ Ico (0 : ℝ) (n + 1 : ℝ) :=
    ⟨mul_nonneg hm.le ht.1, by change m * t < m; nlinarith [ht.2]⟩
  obtain ⟨i, hi, hsi⟩ := exists_nat_unit_slot hs'
  obtain ⟨j, hj, htj⟩ := exists_nat_unit_slot ht'
  change euclideanFiniteC1Paste f n (m * s) = euclideanFiniteC1Paste f n (m * t) at heq
  rw [hslots i hi _ (Ico_subset_Icc_self hsi),
    hslots j hj _ (Ico_subset_Icc_self htj)] at heq
  obtain ⟨hij, he⟩ := hinj i j hi hj (m * s - i) (m * t - j)
    (by constructor <;> linarith [hsi.1, hsi.2])
    (by constructor <;> linarith [htj.1, htj.2]) heq
  subst j
  exact mul_left_cancel₀ hm.ne' (by linarith : m * s = m * t)

/-- The unshifted periodization preserves all original closed equal slots. -/
theorem euclideanFiniteCornerPeriodize_slot
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (k : ℕ) (hk : k ≤ n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    pointContinuousPeriodize (euclideanFiniteCornerArc f n)
      (((k : ℝ) + t) / (n + 1 : ℝ)) = f k t := by
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  rw [pointContinuousPeriodize_eq_Icc
    (euclideanFiniteCornerArc_closed f n hf hv hclose)
    (show ((k : ℝ) + t) / (n + 1 : ℝ) ∈ Icc (0 : ℝ) 1 from
      ⟨div_nonneg (add_nonneg (Nat.cast_nonneg k) ht.1) (by positivity),
       (div_le_one (by positivity : 0 < (n + 1 : ℝ))).mpr (by linarith [ht.2])⟩)]
  exact euclideanFiniteCornerArc_slot f n hf hv k hk t ht

/-- The original corner seam is retained at zero; no regular-point shift is
used in this interface. It is suitable for boundary observers at that vertex. -/
theorem euclideanFiniteCornerPeriodize_properties
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t) :
    Continuous (pointContinuousPeriodize (euclideanFiniteCornerArc f n)) ∧
      Function.Periodic (pointContinuousPeriodize (euclideanFiniteCornerArc f n)) 1 ∧
      InjOn (pointContinuousPeriodize (euclideanFiniteCornerArc f n)) (Ico (0 : ℝ) 1) ∧
      pointContinuousPeriodize (euclideanFiniteCornerArc f n) 0 = f 0 0 ∧
      pointContinuousPeriodize (euclideanFiniteCornerArc f n) '' Icc (0 : ℝ) 1 =
        ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 := by
  have hF := euclideanFiniteCornerArc_continuous f n hf hv
  have hFc := euclideanFiniteCornerArc_closed f n hf hv hclose
  refine ⟨pointContinuousPeriodize_continuous hF.continuousOn hFc,
    pointContinuousPeriodize_periodic _,
    pointContinuousPeriodize_injOn (euclideanFiniteCornerArc_injOn f n hf hv hinj), ?_, ?_⟩
  · rw [pointContinuousPeriodize_eq_Icc hFc (by norm_num)]
    exact (euclideanFiniteCornerArc_endpoints f n hf hv).1
  · have heq : EqOn (pointContinuousPeriodize (euclideanFiniteCornerArc f n))
        (euclideanFiniteCornerArc f n) (Icc (0 : ℝ) 1) :=
      fun _ ht => pointContinuousPeriodize_eq_Icc hFc ht
    exact heq.image_eq.trans (euclideanFiniteCornerArc_image f n hf hv)

/-- The specifically constructed midpoint-based loop has one actual regular
basepoint and exactly the original carrier. All arc derivatives may be
unmatched at the original vertices. -/
theorem euclideanFiniteCornerLoop_half_properties
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t)
    (hreg : deriv (f 0) (1 / 2) ≠ 0) :
    Continuous (euclideanFiniteCornerLoop f n (1 / 2)) ∧
      Function.Periodic (euclideanFiniteCornerLoop f n (1 / 2)) 1 ∧
      InjOn (euclideanFiniteCornerLoop f n (1 / 2)) (Ico (0 : ℝ) 1) ∧
      DifferentiableAt ℝ (euclideanFiniteCornerLoop f n (1 / 2)) 0 ∧
      deriv (euclideanFiniteCornerLoop f n (1 / 2)) 0 ≠ 0 ∧
      euclideanFiniteCornerLoop f n (1 / 2) 0 = f 0 (1 / 2) ∧
      euclideanFiniteCornerLoop f n (1 / 2) '' Icc (0 : ℝ) 1 =
        ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 := by
  obtain ⟨hc, hp, hi, hd, hn, hb⟩ := euclideanFiniteCornerLoop_regular_basepoint
    f n hf hv hclose hinj (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1) hreg
  exact ⟨hc, hp, hi, hd, hn, hb,
    euclideanFiniteCornerLoop_image f n (fun k hk => (hf k hk).continuous) hv hclose _⟩

/-- Moving the basepoint around the same actual continuous periodic curve is
an explicit nonvanishing closed homotopy, so it preserves actual increments. -/
theorem periodic_point_argument_increment_shift
    (γ : ℝ → ℂ) (hγ : Continuous γ) (hp : Function.Periodic γ 1)
    (a : ℝ) {w : ℂ} (hw : w ∉ γ '' Icc (0 : ℝ) 1)
    (θ₀ θa : Icc (0 : ℝ) 1 → ℝ) (hθ₀ : Continuous θ₀) (hθa : Continuous θa)
    (hlift₀ : ∀ t, Complex.exp ((θ₀ t : ℂ) * Complex.I) =
      (γ t - w) / (‖γ t - w‖ : ℂ))
    (hlifta : ∀ t, Complex.exp ((θa t : ℂ) * Complex.I) =
      (γ (t + a) - w) / (‖γ (t + a) - w‖ : ℂ)) :
    θ₀ 1 - θ₀ 0 = θa 1 - θa 0 := by
  let F : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℂ :=
    fun p => γ ((p.2 : ℝ) + (p.1 : ℝ) * a) - w
  have hF : Continuous F :=
    (hγ.comp ((continuous_subtype_val.comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).mul_const a))).sub continuous_const
  have hne (p : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1) : F p ≠ 0 := by
    intro hz
    obtain ⟨t, ht, heq⟩ := hp.exists_mem_Ico₀ (by norm_num)
      ((p.2 : ℝ) + (p.1 : ℝ) * a)
    exact hw ⟨t, Ico_subset_Icc_self ht, heq.symm.trans (sub_eq_zero.mp hz)⟩
  have hclosed : ∀ s, F (s, 0) = F (s, 1) := by
    intro s
    change γ (0 + (s : ℝ) * a) - w = γ (1 + (s : ℝ) * a) - w
    rw [zero_add, add_comm (1 : ℝ), hp]
  apply closed_vector_loop_argument_homotopy F hF hne hclosed θ₀ θa hθ₀ hθa
  · intro t
    change Complex.exp ((θ₀ t : ℂ) * Complex.I) =
      (γ ((t : ℝ) + 0 * a) - w) / (‖γ ((t : ℝ) + 0 * a) - w‖ : ℂ)
    simpa only [zero_mul, add_zero] using hlift₀ t
  · intro t
    change Complex.exp ((θa t : ℂ) * Complex.I) =
      (γ ((t : ℝ) + 1 * a) - w) / (‖γ ((t : ℝ) + 1 * a) - w‖ : ℂ)
    simpa only [one_mul] using hlifta t

/-- Actual finite point lifts telescope along the literal unperiodized arc. -/
theorem finite_corner_arc_point_increment_sum
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (w : ℂ)
    (ψ : ℕ → Icc (0 : ℝ) 1 → ℝ) (Ψ : Icc (0 : ℝ) 1 → ℝ)
    (hψ : ∀ k ≤ n, Continuous (ψ k)) (hΨ : Continuous Ψ)
    (hψlift : ∀ k ≤ n, ∀ t, Complex.exp ((ψ k t : ℂ) * Complex.I) =
      (f k t - w) / (‖f k t - w‖ : ℂ))
    (hΨlift : ∀ t, Complex.exp ((Ψ t : ℂ) * Complex.I) =
      (euclideanFiniteCornerArc f n t - w) / (‖euclideanFiniteCornerArc f n t - w‖ : ℂ)) :
    (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) = Ψ 1 - Ψ 0 := by
  apply finite_unit_slot_angle_increment_sum n ψ Ψ hψ hΨ
  intro k hk t
  apply Circle.ext
  change Complex.exp ((ψ k t : ℂ) * Complex.I) = Complex.exp ((Ψ _ : ℂ) * Complex.I)
  rw [hψlift k hk, hΨlift, euclideanFiniteCornerArc_slot f n hf hv k hk t t.2]

/-- For every observer off the original carrier, the original arc sum is the
increment of every actual lift of every shifted periodic realization. -/
theorem finite_corner_periodic_point_increment_sum
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (a : ℝ) {w : ℂ} (hw : w ∉ ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)
    (ψ : ℕ → Icc (0 : ℝ) 1 → ℝ) (Θ : Icc (0 : ℝ) 1 → ℝ)
    (hψ : ∀ k ≤ n, Continuous (ψ k)) (hΘ : Continuous Θ)
    (hψlift : ∀ k ≤ n, ∀ t, Complex.exp ((ψ k t : ℂ) * Complex.I) =
      (f k t - w) / (‖f k t - w‖ : ℂ))
    (hΘlift : ∀ t, Complex.exp ((Θ t : ℂ) * Complex.I) =
      (euclideanFiniteCornerLoop f n a t - w) / (‖euclideanFiniteCornerLoop f n a t - w‖ : ℂ)) :
    (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) = Θ 1 - Θ 0 := by
  let F := euclideanFiniteCornerArc f n
  let P := pointContinuousPeriodize F
  have hF : Continuous F := euclideanFiniteCornerArc_continuous f n hf hv
  have hFc : F 0 = F 1 := euclideanFiniteCornerArc_closed f n hf hv hclose
  have hFP : EqOn P F (Icc (0 : ℝ) 1) :=
    fun _ ht => pointContinuousPeriodize_eq_Icc hFc ht
  have himage : F '' Icc (0 : ℝ) 1 = ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 :=
    euclideanFiniteCornerArc_image f n hf hv
  have havoid (t : Icc (0 : ℝ) 1) : F t - w ≠ 0 := by
    intro hz
    apply hw
    rw [← himage]
    exact ⟨t, t.2, sub_eq_zero.mp hz⟩
  obtain ⟨Ψ, hΨ, hΨlift⟩ := exists_interval_euclidean_angle_lift
    ((hF.comp continuous_subtype_val).sub continuous_const) havoid
  have hsum := finite_corner_arc_point_increment_sum f n hf hv w ψ Ψ hψ hΨ hψlift hΨlift
  have hwP : w ∉ P '' Icc (0 : ℝ) 1 := by rwa [hFP.image_eq, himage]
  have hshift := periodic_point_argument_increment_shift P
    (pointContinuousPeriodize_continuous hF.continuousOn hFc)
    (pointContinuousPeriodize_periodic F) (a / (n + 1 : ℝ)) hwP Ψ Θ hΨ hΘ
    (fun t => by rw [hFP t.2]; exact hΨlift t) hΘlift
  exact hsum.trans hshift

/-- The same sign works for every actual inside observer and every actual
choice of the finitely many point-angle lifts. The sign is derived from the
one-regular-point Jordan theorem, never supplied as input. -/
theorem finite_corner_inside_point_sum_classification
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t)
    (hreg : deriv (f 0) (1 / 2) ≠ 0)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hK : IsCompact (closure U))
    (hcover : U ∪ V = (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)ᶜ) :
    (∀ w ∈ U, ∀ ψ : ℕ → Icc (0 : ℝ) 1 → ℝ,
      (∀ k ≤ n, Continuous (ψ k)) →
      (∀ k ≤ n, ∀ t, Complex.exp ((ψ k t : ℂ) * Complex.I) =
        (f k t - w) / (‖f k t - w‖ : ℂ)) →
      (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) = 2 * Real.pi) ∨
    (∀ w ∈ U, ∀ ψ : ℕ → Icc (0 : ℝ) 1 → ℝ,
      (∀ k ≤ n, Continuous (ψ k)) →
      (∀ k ≤ n, ∀ t, Complex.exp ((ψ k t : ℂ) * Complex.I) =
        (f k t - w) / (‖f k t - w‖ : ℂ)) →
      (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) = -(2 * Real.pi)) := by
  obtain ⟨hΓ, hp, hi, hd, hn, _, himage⟩ :=
    euclideanFiniteCornerLoop_half_properties f n hf hv hclose hinj hreg
  have hcoverΓ : U ∪ V =
      (euclideanFiniteCornerLoop f n (1 / 2) '' Icc (0 : ℝ) 1)ᶜ := by rwa [himage]
  have htransfer (w : ℂ) (hw : w ∈ U) (ψ : ℕ → Icc (0 : ℝ) 1 → ℝ)
      (hψ : ∀ k ≤ n, Continuous (ψ k))
      (hψlift : ∀ k ≤ n, ∀ t, Complex.exp ((ψ k t : ℂ) * Complex.I) =
        (f k t - w) / (‖f k t - w‖ : ℂ)) :
      ∃ Θ : Icc (0 : ℝ) 1 → ℝ, Continuous Θ ∧
        (∀ t, Complex.exp ((Θ t : ℂ) * Complex.I) =
          (euclideanFiniteCornerLoop f n (1 / 2) t - w) /
            (‖euclideanFiniteCornerLoop f n (1 / 2) t - w‖ : ℂ)) ∧
        (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) = Θ 1 - Θ 0 := by
    have hwC : w ∉ ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 := by
      have hwUV : w ∈ U ∪ V := Or.inl hw
      rw [hcover] at hwUV
      exact hwUV
    have havoid (t : Icc (0 : ℝ) 1) : euclideanFiniteCornerLoop f n (1 / 2) t - w ≠ 0 := by
      intro hz
      apply hwC
      rw [← himage]
      exact ⟨t, t.2, sub_eq_zero.mp hz⟩
    obtain ⟨Θ, hΘ, hΘlift⟩ := exists_interval_euclidean_angle_lift
      ((hΓ.comp continuous_subtype_val).sub continuous_const) havoid
    exact ⟨Θ, hΘ, hΘlift, finite_corner_periodic_point_increment_sum
      f n (fun k hk => (hf k hk).continuous) hv hclose (1 / 2) hwC ψ Θ hψ hΘ hψlift hΘlift⟩
  rcases one_regular_simple_loop_inside_argument_classification hΓ hd hp hi hn
    hU hUc hV hVc hK hcoverΓ with hplus | hminus
  · left
    intro w hw ψ hψ hψlift
    obtain ⟨Θ, hΘ, hΘlift, hsum⟩ := htransfer w hw ψ hψ hψlift
    exact hsum.trans (hplus w hw Θ hΘ hΘlift)
  · right
    intro w hw ψ hψ hψlift
    obtain ⟨Θ, hΘ, hΘlift, hsum⟩ := htransfer w hw ψ hψ hψlift
    exact hsum.trans (hminus w hw Θ hΘ hΘlift)

/-- The actual outside value is zero, already at the original finite family.
This part requires only continuity and endpoint matching. -/
theorem finite_corner_outside_point_sum_zero
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    {U V : Set ℂ} (hK : IsCompact (closure U)) (hV : IsOpen V) (hVc : IsConnected V)
    (hcover : U ∪ V = (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)ᶜ)
    {w : ℂ} (hw : w ∈ V) (ψ : ℕ → Icc (0 : ℝ) 1 → ℝ)
    (hψ : ∀ k ≤ n, Continuous (ψ k))
    (hψlift : ∀ k ≤ n, ∀ t, Complex.exp ((ψ k t : ℂ) * Complex.I) =
      (f k t - w) / (‖f k t - w‖ : ℂ)) :
    (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) = 0 := by
  let F : Icc (0 : ℝ) 1 → ℂ := fun t => euclideanFiniteCornerArc f n t
  have hF : Continuous F := (euclideanFiniteCornerArc_continuous f n hf hv).comp continuous_subtype_val
  have hFc : F 0 = F 1 := euclideanFiniteCornerArc_closed f n hf hv hclose
  have himage : range F = ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 := by
    rw [show range F = euclideanFiniteCornerArc f n '' Icc (0 : ℝ) 1 by
      ext z
      constructor
      · rintro ⟨t, rfl⟩; exact ⟨t, t.2, rfl⟩
      · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, rfl⟩]
    exact euclideanFiniteCornerArc_image f n hf hv
  have hcoverF : U ∪ V = (range F)ᶜ := by rwa [himage]
  have havoid (t : Icc (0 : ℝ) 1) : F t - w ≠ 0 := by
    intro hz
    have hwC : w ∉ range F := by
      have hwUV : w ∈ U ∪ V := Or.inr hw
      rw [hcoverF] at hwUV
      exact hwUV
    exact hwC ⟨t, sub_eq_zero.mp hz⟩
  obtain ⟨Ψ, hΨ, hΨlift⟩ := exists_interval_euclidean_angle_lift
    (hF.sub continuous_const) havoid
  exact (finite_corner_arc_point_increment_sum f n hf hv w ψ Ψ hψ hΨ hψlift hΨlift).trans
    (jordan_outside_argument_increment_zero F hF hFc hK hV hVc hcoverF hw Ψ hΨ hΨlift)

end RepulsiveCoulomb
