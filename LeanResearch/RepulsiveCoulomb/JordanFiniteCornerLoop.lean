module

public import LeanResearch.RepulsiveCoulomb.JordanFiniteC1Loop
public import LeanResearch.RepulsiveCoulomb.PointContinuousLoopPeriodization

@[expose] public section

/-! The original unmatched-corner family has a constructed C0 periodic
parametrization on equal slots. Shifting to a chosen interior point of the
first regular edge gives a genuine nonzero derivative at the basepoint before
any smoothing. The literal global formula is retained for finite transport.
Records-only successor, outside the current admission set. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem euclideanC0Glue_continuous {c : ℝ} {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hval : f c = g c) :
    Continuous (euclideanC1Glue c f g) := by
  apply Continuous.if_le hf hg continuous_id continuous_const
  intro t ht
  change t = c at ht
  simpa only [ht] using hval

/-- The same explicit pasting function is continuous without matching jets;
every closed slot still agrees with its literal original curve. -/
theorem euclideanFinitePaste_continuous_properties (f : ℕ → ℝ → ℂ) (n : ℕ)
    (hf : ∀ k ≤ n, Continuous (f k)) (hv : ∀ k < n, f k 1 = f (k + 1) 0) :
    Continuous (euclideanFiniteC1Paste f n) ∧
      (∀ t : ℝ, (n : ℝ) ≤ t → euclideanFiniteC1Paste f n t = f n (t - n)) ∧
      ∀ k ≤ n, ∀ t ∈ Icc (k : ℝ) (k + 1 : ℝ),
        euclideanFiniteC1Paste f n t = f k (t - k) := by
  induction n with
  | zero =>
    refine ⟨hf 0 le_rfl, ?_, ?_⟩
    · intro t _; simp [euclideanFiniteC1Paste]
    · intro k hk t _
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp [euclideanFiniteC1Paste]
  | succ n ih =>
    obtain ⟨hP, htail, hslots⟩ := ih (fun k hk => hf k (by omega)) (fun k hk => hv k (by omega))
    let g : ℝ → ℂ := fun t => f (n + 1) (t - (n + 1 : ℕ))
    have hg : Continuous g := by
      have hfn := hf (n + 1) le_rfl
      dsimp [g]
      fun_prop
    have hval : euclideanFiniteC1Paste f n (n + 1 : ℕ) = g (n + 1 : ℕ) := by
      rw [htail _ (by exact_mod_cast Nat.le_succ n)]
      have hc : ((n + 1 : ℕ) : ℝ) - n = 1 := by push_cast; ring
      simpa only [hc, g, sub_self] using hv n (Nat.lt_succ_self n)
    have hlast (t : ℝ) (ht : ((n + 1 : ℕ) : ℝ) ≤ t) :
        euclideanFiniteC1Paste f (n + 1) t = f (n + 1) (t - (n + 1 : ℕ)) :=
      euclideanC1Glue_eq_right hval ht
    refine ⟨euclideanC0Glue_continuous hP hg hval, hlast, ?_⟩
    intro k hk t ht
    by_cases hkn : k = n + 1
    · subst k
      exact hlast t (by exact_mod_cast ht.1)
    · have hkle : k ≤ n := by omega
      have htc : t ≤ ((n + 1 : ℕ) : ℝ) := by
        have hkR : (k : ℝ) ≤ n := by exact_mod_cast hkle
        push_cast
        linarith [ht.2]
      change euclideanC1Glue ((n + 1 : ℕ) : ℝ) (euclideanFiniteC1Paste f n) g t = _
      rw [euclideanC1Glue_eq_left _ _ _ htc]
      exact hslots k hkle t ht

def euclideanFiniteCornerArc (f : ℕ → ℝ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  euclideanFiniteC1Paste f n ((n + 1 : ℝ) * t)

def euclideanFiniteCornerLoop (f : ℕ → ℝ → ℂ) (n : ℕ) (a t : ℝ) : ℂ :=
  pointContinuousPeriodize (euclideanFiniteCornerArc f n) (t + a / (n + 1 : ℝ))

/-- Literal continuous-loop realization before rounding. Its basepoint lies
at parameter a on the first actual edge, and has nonzero actual derivative. -/
theorem euclideanFiniteCornerLoop_regular_basepoint
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t, s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hreg : deriv (f 0) a ≠ 0) :
    Continuous (euclideanFiniteCornerLoop f n a) ∧
      Function.Periodic (euclideanFiniteCornerLoop f n a) 1 ∧
      InjOn (euclideanFiniteCornerLoop f n a) (Ico (0 : ℝ) 1) ∧
      DifferentiableAt ℝ (euclideanFiniteCornerLoop f n a) 0 ∧
      deriv (euclideanFiniteCornerLoop f n a) 0 ≠ 0 ∧
      euclideanFiniteCornerLoop f n a 0 = f 0 a := by
  obtain ⟨hP, _, hslots⟩ := euclideanFinitePaste_continuous_properties f n
    (fun k hk => (hf k hk).continuous) hv
  let m : ℝ := n + 1
  have hm : 0 < m := by dsimp [m]; positivity
  have hm1 : 1 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (α := ℝ) n]
  let F := euclideanFiniteCornerArc f n
  have hF : Continuous F := hP.comp (by fun_prop)
  have hF0 : F 0 = f 0 0 := by
    change euclideanFiniteC1Paste f n (m * 0) = _
    rw [mul_zero]
    simpa only [Nat.cast_zero, sub_zero] using hslots 0 (Nat.zero_le n) 0 (by norm_num)
  have hF1 : F 1 = f n 1 := by
    change euclideanFiniteC1Paste f n (m * 1) = _
    rw [mul_one]
    have hs : m ∈ Icc (n : ℝ) (n + 1 : ℝ) := by dsimp [m]; constructor <;> linarith
    simpa only [m, add_sub_cancel_left] using hslots n le_rfl m hs
  have hFc : F 0 = F 1 := by rw [hF0, hF1, hclose]
  have hFi : InjOn F (Ico (0 : ℝ) 1) := by
    intro s hs t ht heq
    have hs' : m * s ∈ Ico (0 : ℝ) (n + 1 : ℝ) :=
      ⟨mul_nonneg hm.le hs.1, by change m * s < m; nlinarith [hs.2]⟩
    have ht' : m * t ∈ Ico (0 : ℝ) (n + 1 : ℝ) :=
      ⟨mul_nonneg hm.le ht.1, by change m * t < m; nlinarith [ht.2]⟩
    obtain ⟨i, hi, hsi⟩ := exists_nat_unit_slot hs'
    obtain ⟨j, hj, htj⟩ := exists_nat_unit_slot ht'
    change euclideanFiniteC1Paste f n (m * s) = euclideanFiniteC1Paste f n (m * t) at heq
    rw [hslots i hi _ (Ico_subset_Icc_self hsi), hslots j hj _ (Ico_subset_Icc_self htj)] at heq
    obtain ⟨hij, he⟩ := hinj i j hi hj (m * s - i) (m * t - j)
      (by constructor <;> linarith [hsi.1, hsi.2])
      (by constructor <;> linarith [htj.1, htj.2]) heq
    subst j
    have hmt : m * s = m * t := by linarith
    exact mul_left_cancel₀ hm.ne' hmt
  have haI : a / m ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos ha.1 hm, (div_lt_one hm).mpr (ha.2.trans_le hm1)⟩
  have htimes : m * (a / m) = a := by field_simp
  have hlocal : F =ᶠ[𝓝 (a / m)] (fun t => f 0 (m * t)) := by
    have hmap : Tendsto (fun t : ℝ => m * t) (𝓝 (a / m)) (𝓝 a) := by
      have hcont : Continuous (fun t : ℝ => m * t) := by fun_prop
      simpa only [htimes] using hcont.tendsto (a / m)
    filter_upwards [hmap (Ioo_mem_nhds ha.1 ha.2)] with t ht
    change euclideanFiniteC1Paste f n (m * t) = f 0 (m * t)
    have hmt : m * t ∈ Ioo (0 : ℝ) 1 := ht
    simpa only [Nat.cast_zero, sub_zero] using hslots 0 (Nat.zero_le n) (m * t)
      (by simpa only [Nat.cast_zero, zero_add] using Ioo_subset_Icc_self hmt)
  have hd0 : HasDerivAt (f 0) (deriv (f 0) a) (m * (a / m)) := by
    simpa only [htimes] using ((hf 0 (Nat.zero_le n)).differentiable (by norm_num) a).hasDerivAt
  have hD : HasDerivAt F (m • deriv (f 0) a) (a / m) := by
    have hlin : HasDerivAt (fun t : ℝ => m * t) m (a / m) := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id (a / m)).const_mul m
    exact (hd0.scomp (a / m) hlin).congr_of_eventuallyEq hlocal
  have hperiod := pointContinuousPeriodize_periodic F
  have hcontinuous := pointContinuousPeriodize_continuous hF.continuousOn hFc
  have hbaseeq : euclideanFiniteCornerLoop f n a =ᶠ[𝓝 (0 : ℝ)] (fun t => F (t + a / m)) := by
    have hmap : Tendsto (fun t : ℝ => t + a / m) (𝓝 0) (𝓝 (a / m)) := by
      simpa only [id_eq, zero_add] using (continuous_id.add_const (a / m)).tendsto 0
    exact (pointContinuousPeriodize_eventually_eq F haI).comp_tendsto hmap
  have hDa : HasDerivAt F (m • deriv (f 0) a) (0 + a / m) := by
    simpa only [zero_add] using hD
  have hLoopD := (hDa.comp_add_const 0 (a / m)).congr_of_eventuallyEq hbaseeq
  refine ⟨hcontinuous.comp (continuous_id.add_const (a / m)), ?_,
    periodic_simple_loop_shift_injOn hperiod (pointContinuousPeriodize_injOn hFi)
      (Ioo_subset_Icc_self haI), hLoopD.differentiableAt, ?_, ?_⟩
  · intro t
    change pointContinuousPeriodize F (t + 1 + a / m) = pointContinuousPeriodize F (t + a / m)
    rw [show t + 1 + a / m = (t + a / m) + 1 by ring, hperiod]
  · rw [hLoopD.deriv]
    exact smul_ne_zero hm.ne' hreg
  · calc
      euclideanFiniteCornerLoop f n a 0 = F (0 + a / m) := hbaseeq.self_of_nhds
      _ = F (a / m) := by rw [zero_add]
      _ = f 0 a := by simpa only [htimes] using hlocal.self_of_nhds


/-- The constructed original finite arc has exactly the original carrier. -/
theorem euclideanFiniteCornerArc_image
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) :
    euclideanFiniteCornerArc f n '' Icc (0 : ℝ) 1 = ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 := by
  obtain ⟨_, _, hslots⟩ := euclideanFinitePaste_continuous_properties f n hf hv
  let m : ℝ := n + 1
  have hm : 0 < m := by dsimp [m]; positivity
  apply Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    have hmt : m * t ∈ Icc (0 : ℝ) (n + 1 : ℝ) :=
      ⟨mul_nonneg hm.le ht.1, by change m * t ≤ m; nlinarith [ht.2]⟩
    obtain ⟨k, hk, hs⟩ := exists_nat_closed_unit_slot hmt
    refine mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, ?_⟩⟩
    exact ⟨m * t - k, by constructor <;> linarith [hs.1, hs.2], (hslots k hk _ hs).symm⟩
  · intro z hz
    obtain ⟨k, hk, t, ht, rfl⟩ := (by simpa only [mem_iUnion, mem_image] using hz :
      ∃ k, ∃ hk : k ≤ n, ∃ t ∈ Icc (0 : ℝ) 1, f k t = z)
    have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
    refine ⟨((k : ℝ) + t) / m, ?_, ?_⟩
    · exact ⟨div_nonneg (add_nonneg (Nat.cast_nonneg k) ht.1) hm.le,
        (div_le_one hm).mpr (by dsimp [m]; linarith [ht.2])⟩
    · change euclideanFiniteC1Paste f n (m * (((k : ℝ) + t) / m)) = f k t
      have htimes : m * (((k : ℝ) + t) / m) = k + t := by field_simp
      rw [htimes, hslots k hk _ (by constructor <;> linarith [ht.1, ht.2]), add_sub_cancel_left]

/-- Periodization and the explicit basepoint shift preserve exact coverage. -/
theorem euclideanFiniteCornerLoop_image
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0) (a : ℝ) :
    euclideanFiniteCornerLoop f n a '' Icc (0 : ℝ) 1 = ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 := by
  obtain ⟨_, _, hslots⟩ := euclideanFinitePaste_continuous_properties f n hf hv
  let F := euclideanFiniteCornerArc f n
  have hF0 : F 0 = f 0 0 := by
    change euclideanFiniteC1Paste f n ((n + 1 : ℝ) * 0) = _
    rw [mul_zero]
    simpa only [Nat.cast_zero, sub_zero] using hslots 0 (Nat.zero_le n) 0 (by norm_num)
  have hF1 : F 1 = f n 1 := by
    change euclideanFiniteC1Paste f n ((n + 1 : ℝ) * 1) = _
    rw [mul_one]
    simpa only [add_sub_cancel_left] using hslots n le_rfl (n + 1 : ℝ) (by constructor <;> linarith)
  have hFc : F 0 = F 1 := by rw [hF0, hF1, hclose]
  change (fun t => pointContinuousPeriodize F (t + a / (n + 1 : ℝ))) '' Icc (0 : ℝ) 1 = _
  rw [periodic_closed_interval_image_shift (pointContinuousPeriodize_periodic F)]
  have heq : EqOn (pointContinuousPeriodize F) F (Icc (0 : ℝ) 1) :=
    fun t ht => pointContinuousPeriodize_eq_Icc hFc ht
  rw [heq.image_eq]
  exact euclideanFiniteCornerArc_image f n hf hv

end RepulsiveCoulomb
