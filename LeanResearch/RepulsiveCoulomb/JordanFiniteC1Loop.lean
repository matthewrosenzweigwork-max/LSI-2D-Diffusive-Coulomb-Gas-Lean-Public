import LeanResearch.RepulsiveCoulomb.JordanFiniteC1Pasting
import LeanResearch.RepulsiveCoulomb.JordanC1Periodization
import Mathlib.Algebra.Order.Floor.Semiring

/-! Construct an actual closed regular simple C¹ parametrization of a finite
matched-jet cyclic family. Simplicity comes from literal half-open arc images;
regularity and exact coverage come from the finite pasting formula. There is
no assumed global smooth parametrization. Records-only candidate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_nat_unit_slot {n : ℕ} {x : ℝ} (hx : x ∈ Ico (0 : ℝ) (n + 1 : ℝ)) :
    ∃ k : ℕ, k ≤ n ∧ x ∈ Ico (k : ℝ) (k + 1 : ℝ) := by
  have hlt : ⌊x⌋₊ < n + 1 := (Nat.floor_lt hx.1).mpr (by exact_mod_cast hx.2)
  exact ⟨⌊x⌋₊, by omega, Nat.floor_le hx.1, Nat.lt_floor_add_one x⟩

theorem exists_nat_closed_unit_slot {n : ℕ} {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (n + 1 : ℝ)) :
    ∃ k : ℕ, k ≤ n ∧ x ∈ Icc (k : ℝ) (k + 1 : ℝ) := by
  by_cases hxlast : x = n + 1
  · exact ⟨n, le_rfl, by rw [hxlast]; constructor <;> linarith⟩
  · obtain ⟨k, hk, hslot⟩ := exists_nat_unit_slot (n := n) ⟨hx.1, lt_of_le_of_ne hx.2 hxlast⟩
    exact ⟨k, hk, Ico_subset_Icc_self hslot⟩

theorem euclideanFiniteC1Paste_regular (f : ℕ → ℝ → ℂ) (n : ℕ)
    (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0)
    (hd : ∀ k < n, deriv (f k) 1 = deriv (f (k + 1)) 0)
    (hreg : ∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1, deriv (f k) t ≠ 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (n + 1 : ℝ)) :
    deriv (euclideanFiniteC1Paste f n) t ≠ 0 := by
  obtain ⟨k, hk, hslot⟩ := exists_nat_closed_unit_slot ht
  rw [(euclideanFiniteC1Paste_properties f n hf hv hd).2.2.2.2 k hk t hslot]
  exact hreg k hk _ (by constructor <;> linarith [hslot.1, hslot.2])

/-- Actual half-open image disjointness and actual edge injectivity give
injectivity of the constructed whole loop away from its closing endpoint. -/
theorem euclideanFiniteC1Paste_injOn (f : ℕ → ℝ → ℂ) (n : ℕ)
    (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0)
    (hd : ∀ k < n, deriv (f k) 1 = deriv (f (k + 1)) 0)
    (hinj : ∀ k ≤ n, InjOn (f k) (Ico (0 : ℝ) 1))
    (hdisj : ∀ i ≤ n, ∀ j ≤ n, i ≠ j →
      Disjoint (f i '' Ico (0 : ℝ) 1) (f j '' Ico (0 : ℝ) 1)) :
    InjOn (euclideanFiniteC1Paste f n) (Ico (0 : ℝ) (n + 1 : ℝ)) := by
  intro s hs t ht heq
  obtain ⟨i, hi, hsi⟩ := exists_nat_unit_slot hs
  obtain ⟨j, hj, htj⟩ := exists_nat_unit_slot ht
  have hslot := (euclideanFiniteC1Paste_properties f n hf hv hd).2.2.2.1
  rw [hslot i hi s (Ico_subset_Icc_self hsi), hslot j hj t (Ico_subset_Icc_self htj)] at heq
  have hsp : s - i ∈ Ico (0 : ℝ) 1 := by constructor <;> linarith [hsi.1, hsi.2]
  have htp : t - j ∈ Ico (0 : ℝ) 1 := by constructor <;> linarith [htj.1, htj.2]
  by_cases hij : i = j
  · subst j
    have h := hinj i hi hsp htp heq
    linarith
  · exact (Set.disjoint_left.mp (hdisj i hi j hj hij)
      ⟨s - i, hsp, rfl⟩ ⟨t - j, htp, heq.symm⟩).elim

/-- A finite actual matched-jet cyclic family produces a genuine closed C¹
simple regular curve on the standard interval, with exact image coverage. -/
theorem exists_finite_matched_regular_C1_loop (f : ℕ → ℝ → ℂ) (n : ℕ)
    (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0)
    (hd : ∀ k < n, deriv (f k) 1 = deriv (f (k + 1)) 0)
    (hclose : f n 1 = f 0 0) (hcloseD : deriv (f n) 1 = deriv (f 0) 0)
    (hreg : ∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1, deriv (f k) t ≠ 0)
    (hinj : ∀ k ≤ n, InjOn (f k) (Ico (0 : ℝ) 1))
    (hdisj : ∀ i ≤ n, ∀ j ≤ n, i ≠ j →
      Disjoint (f i '' Ico (0 : ℝ) 1) (f j '' Ico (0 : ℝ) 1)) :
    ∃ Γ : ℝ → ℂ, ContDiff ℝ 1 Γ ∧ Γ 0 = Γ 1 ∧ deriv Γ 0 = deriv Γ 1 ∧
      InjOn Γ (Ico (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, deriv Γ t ≠ 0) ∧
      Γ '' Icc (0 : ℝ) 1 = ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 ∧
      ∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1,
        Γ (((k : ℝ) + t) / (n + 1 : ℝ)) = f k t ∧
        deriv Γ (((k : ℝ) + t) / (n + 1 : ℝ)) = (n + 1 : ℝ) • deriv (f k) t := by
  let P := euclideanFiniteC1Paste f n
  let m : ℝ := n + 1
  have hm : 0 < m := by dsimp [m]; positivity
  obtain ⟨hP, _, _, hvalslots, hderslots⟩ := euclideanFiniteC1Paste_properties f n hf hv hd
  let Γ : ℝ → ℂ := fun t => P (m * t)
  have hΓ : ContDiff ℝ 1 Γ := by dsimp [Γ]; fun_prop
  have hD (t : ℝ) : deriv Γ t = m • deriv P (m * t) := by
    simpa only [Γ, Function.comp_def, id_eq, mul_one] using
      ((((hP.differentiable (by norm_num)) (m * t)).hasDerivAt).scomp t
        ((hasDerivAt_id t).const_mul m)).deriv
  have hval0 : P 0 = f 0 0 := by
    simpa only [Nat.cast_zero, sub_zero] using hvalslots 0 (Nat.zero_le n) 0 (by norm_num)
  have hval1 : P m = f n 1 := by
    have hslot : m ∈ Icc (n : ℝ) (n + 1 : ℝ) := by dsimp [m]; constructor <;> linarith
    simpa only [m, add_sub_cancel_left] using hvalslots n le_rfl m hslot
  have hder0 : deriv P 0 = deriv (f 0) 0 := by
    simpa only [Nat.cast_zero, sub_zero] using hderslots 0 (Nat.zero_le n) 0 (by norm_num)
  have hder1 : deriv P m = deriv (f n) 1 := by
    have hslot : m ∈ Icc (n : ℝ) (n + 1 : ℝ) := by dsimp [m]; constructor <;> linarith
    simpa only [m, add_sub_cancel_left] using hderslots n le_rfl m hslot
  have hΓclose : Γ 0 = Γ 1 := by simp only [Γ, mul_zero, mul_one, hval0, hval1, hclose]
  have hΓcloseD : deriv Γ 0 = deriv Γ 1 := by
    rw [hD, hD, mul_zero, mul_one, hder0, hder1, hcloseD]
  have hΓinj : InjOn Γ (Ico (0 : ℝ) 1) := by
    intro s hs t ht heq
    have he := euclideanFiniteC1Paste_injOn f n hf hv hd hinj hdisj
      (show m * s ∈ Ico (0 : ℝ) (n + 1 : ℝ) from
        ⟨mul_nonneg hm.le hs.1, by change m * s < m; nlinarith [hs.2]⟩)
      (show m * t ∈ Ico (0 : ℝ) (n + 1 : ℝ) from
        ⟨mul_nonneg hm.le ht.1, by change m * t < m; nlinarith [ht.2]⟩) heq
    exact (mul_left_cancel₀ hm.ne') he
  have hΓreg : ∀ t ∈ Icc (0 : ℝ) 1, deriv Γ t ≠ 0 := by
    intro t ht
    rw [hD]
    apply smul_ne_zero hm.ne'
    apply euclideanFiniteC1Paste_regular f n hf hv hd hreg
    exact ⟨mul_nonneg hm.le ht.1, by change m * t ≤ m; nlinarith [ht.2]⟩
  have hslots (k : ℕ) (hk : k ≤ n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Γ (((k : ℝ) + t) / m) = f k t ∧
        deriv Γ (((k : ℝ) + t) / m) = m • deriv (f k) t := by
    have htimes : m * (((k : ℝ) + t) / m) = k + t := by field_simp
    have hslot : (k : ℝ) + t ∈ Icc (k : ℝ) (k + 1 : ℝ) := by constructor <;> linarith [ht.1, ht.2]
    constructor
    · change P (m * (((k : ℝ) + t) / m)) = _
      rw [htimes]
      change euclideanFiniteC1Paste f n ((k : ℝ) + t) = f k t
      rw [hvalslots k hk _ hslot, add_sub_cancel_left]
    · rw [hD, htimes, hderslots k hk _ hslot, add_sub_cancel_left]
  refine ⟨Γ, hΓ, hΓclose, hΓcloseD, hΓinj, hΓreg, ?_, hslots⟩
  apply Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    have hmt : m * t ∈ Icc (0 : ℝ) (n + 1 : ℝ) :=
      ⟨mul_nonneg hm.le ht.1, by change m * t ≤ m; nlinarith [ht.2]⟩
    obtain ⟨k, hk, hs⟩ := exists_nat_closed_unit_slot hmt
    refine mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, ?_⟩⟩
    refine ⟨m * t - k, by constructor <;> linarith [hs.1, hs.2], ?_⟩
    exact (hvalslots k hk _ hs).symm
  · intro z hz
    obtain ⟨k, hk, t, ht, rfl⟩ := (by simpa only [mem_iUnion, mem_image] using hz :
      ∃ k, ∃ hk : k ≤ n, ∃ t ∈ Icc (0 : ℝ) 1, f k t = z)
    have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
    refine ⟨((k : ℝ) + t) / m, ?_, (hslots k hk t ht).1⟩
    exact ⟨div_nonneg (add_nonneg (Nat.cast_nonneg k) ht.1) hm.le,
      (div_le_one hm).mpr (by dsimp [m]; linarith [ht.2])⟩

end RepulsiveCoulomb
