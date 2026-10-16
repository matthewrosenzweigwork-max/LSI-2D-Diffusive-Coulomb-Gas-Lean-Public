import LeanResearch.RepulsiveCoulomb.JordanFiniteCornerPointWinding
import LeanResearch.RepulsiveCoulomb.PointRadialSectorTopology

/-! Keep the original corner as the period seam. Endpoint-extended point
arguments need only satisfy the actual normalized chord identity on the open
arc: no division by zero is imposed at the observed vertex. The finite sum
is transported to the genuinely constructed boundary-point lift, and the
original first/last radial collars give the full, possibly reflex sector.
Records-only next-batch candidate. The final boundary-atom application is
kept in its own module so these geometric interfaces do not depend on it. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

/-- Continuous endpoint extensions have equal circle directions at the
endpoints as soon as they agree on the open unit interval. -/
theorem unit_interval_circle_exp_eq_of_open
    (θ φ : Icc (0 : ℝ) 1 → ℝ) (hθ : Continuous θ) (hφ : Continuous φ)
    (hopen : ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Circle.exp (θ t) = Circle.exp (φ t)) :
    ∀ t, Circle.exp (θ t) = Circle.exp (φ t) := by
  let Eθ : ℝ → Circle := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) (fun t => Circle.exp (θ t))
  let Eφ : ℝ → Circle := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) (fun t => Circle.exp (φ t))
  have hEθ : Continuous Eθ := continuous_IccExtend_iff.mpr (Circle.exp.continuous.comp hθ)
  have hEφ : Continuous Eφ := continuous_IccExtend_iff.mpr (Circle.exp.continuous.comp hφ)
  have heq : EqOn Eθ Eφ (Ioo (0 : ℝ) 1) := by
    intro t ht
    dsimp only [Eθ, Eφ]
    rw [IccExtend_of_mem _ _ (Ioo_subset_Icc_self ht),
      IccExtend_of_mem _ _ (Ioo_subset_Icc_self ht)]
    exact hopen ⟨t, Ioo_subset_Icc_self ht⟩ ht
  have hclosed := heq.closure hEθ hEφ
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hclosed
  intro t
  simpa only [Eθ, Eφ, IccExtend_val] using hclosed t.2

/-- The equal-slot telescope also works when local point arguments have only
open-arc lift identities, as is necessary at a boundary observation point. -/
theorem finite_unit_slot_angle_increment_sum_of_open
    (n : ℕ) (ψ : ℕ → Icc (0 : ℝ) 1 → ℝ) (Ψ : Icc (0 : ℝ) 1 → ℝ)
    (hψ : ∀ k ≤ n, Continuous (ψ k)) (hΨ : Continuous Ψ)
    (hlift : ∀ k (hk : k ≤ n) (t : Icc (0 : ℝ) 1),
      t.1 ∈ Ioo (0 : ℝ) 1 → Circle.exp (ψ k t) = Circle.exp (Ψ
        ⟨((k : ℝ) + t) / (n + 1 : ℝ),
          div_nonneg (add_nonneg (Nat.cast_nonneg k) t.2.1) (by positivity),
          (div_le_one (by positivity : 0 < (n + 1 : ℝ))).mpr
            (by have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
                linarith [t.2.2])⟩)) :
    (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) = Ψ 1 - Ψ 0 := by
  apply finite_unit_slot_angle_increment_sum n ψ Ψ hψ hΨ
  intro k hk
  let σ : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun t =>
    ⟨((k : ℝ) + t) / (n + 1 : ℝ),
      div_nonneg (add_nonneg (Nat.cast_nonneg k) t.2.1) (by positivity),
      (div_le_one (by positivity : 0 < (n + 1 : ℝ))).mpr
        (by have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
            linarith [t.2.2])⟩
  have hσ : Continuous σ :=
    ((continuous_const.add continuous_subtype_val).div_const (n + 1 : ℝ)).subtype_mk _
  exact unit_interval_circle_exp_eq_of_open (ψ k) (fun t => Ψ (σ t))
    (hψ k hk) (hΨ.comp hσ) (hlift k hk)

/-- Boundary observers are allowed here: local and global identities are
required only on open arcs and are extended to endpoints by continuity. -/
theorem finite_corner_punctured_point_increment_sum
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0) (w : ℂ)
    (ψ : ℕ → Icc (0 : ℝ) 1 → ℝ) (Ψ : Icc (0 : ℝ) 1 → ℝ)
    (hψ : ∀ k ≤ n, Continuous (ψ k)) (hΨ : Continuous Ψ)
    (hψlift : ∀ k ≤ n, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ k t : ℂ) * Complex.I) = (f k t - w) / (‖f k t - w‖ : ℂ))
    (hΨlift : ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((Ψ t : ℂ) * Complex.I) =
        (pointContinuousPeriodize (euclideanFiniteCornerArc f n) t - w) /
          (‖pointContinuousPeriodize (euclideanFiniteCornerArc f n) t - w‖ : ℂ)) :
    (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) = Ψ 1 - Ψ 0 := by
  apply finite_unit_slot_angle_increment_sum_of_open n ψ Ψ hψ hΨ
  intro k hk t ht
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hslot : ((k : ℝ) + t) / (n + 1 : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (by linarith [Nat.cast_nonneg (α := ℝ) k, ht.1]) (by positivity),
      (div_lt_one (by positivity : 0 < (n + 1 : ℝ))).mpr (by linarith [ht.2])⟩
  apply Circle.ext
  change Complex.exp ((ψ k t : ℂ) * Complex.I) = Complex.exp ((Ψ _ : ℂ) * Complex.I)
  rw [hψlift k hk t ht, hΨlift _ hslot,
    euclideanFiniteCornerPeriodize_slot f n hf hv hclose k hk t t.2]

/-- Literal first closed slot of the unshifted periodization. -/
theorem euclideanFiniteCornerPeriodize_first_slot
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (htslot : (n + 1 : ℝ) * t ≤ 1) :
    pointContinuousPeriodize (euclideanFiniteCornerArc f n) t = f 0 ((n + 1 : ℝ) * t) := by
  rw [pointContinuousPeriodize_eq_Icc (euclideanFiniteCornerArc_closed f n hf hv hclose) ht]
  change euclideanFiniteC1Paste f n ((n + 1 : ℝ) * t) = f 0 ((n + 1 : ℝ) * t)
  simpa only [Nat.cast_zero, sub_zero] using
    (euclideanFinitePaste_continuous_properties f n hf hv).2.2 0 (Nat.zero_le n) _
      (by constructor
          · simpa only [Nat.cast_zero] using mul_nonneg (by positivity : (0 : ℝ) ≤ n + 1) ht.1
          · simpa only [Nat.cast_zero, zero_add] using htslot)

/-- Literal last closed slot, reaching the original seam at parameter one. -/
theorem euclideanFiniteCornerPeriodize_last_slot
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (htslot : (n : ℝ) ≤ (n + 1 : ℝ) * t) :
    pointContinuousPeriodize (euclideanFiniteCornerArc f n) t =
      f n ((n + 1 : ℝ) * t - n) := by
  rw [pointContinuousPeriodize_eq_Icc (euclideanFiniteCornerArc_closed f n hf hv hclose) ht]
  exact (euclideanFinitePaste_continuous_properties f n hf hv).2.2 n le_rfl _
    ⟨htslot, by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left ht.2 (by positivity : (0 : ℝ) ≤ n + 1)⟩

/-- Original radial collars are preserved with an explicitly rescaled
parameter and speed. No local equality near a regular midpoint is substituted
for the actual corner seam. -/
theorem euclideanFiniteCornerPeriodize_radial_collars
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (H : ℂ → ℂ) (θ : ℝ) {δ cL cR : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hcL : 0 < cL) (hcR : 0 < cR)
    (hleft : ∀ s ∈ Icc (0 : ℝ) 1, s ≤ δ →
      f 0 s = H (pointRadialSectorPoint (cL * s) 0))
    (hright : ∀ s ∈ Icc (0 : ℝ) 1, 1 - δ ≤ s →
      f n s = H (pointRadialSectorPoint (cR * (1 - s)) θ)) :
    0 < δ / (n + 1 : ℝ) ∧
      δ / (n + 1 : ℝ) < 1 - δ / (n + 1 : ℝ) ∧
      1 - δ / (n + 1 : ℝ) < 1 ∧
      0 < (n + 1 : ℝ) * cL ∧ 0 < (n + 1 : ℝ) * cR ∧
      (∀ t : Icc (0 : ℝ) 1, t.1 ≤ δ / (n + 1 : ℝ) →
        pointContinuousPeriodize (euclideanFiniteCornerArc f n) t =
          H (pointRadialSectorPoint (((n + 1 : ℝ) * cL) * t.1) 0)) ∧
      (∀ t : Icc (0 : ℝ) 1, 1 - δ / (n + 1 : ℝ) ≤ t.1 →
        pointContinuousPeriodize (euclideanFiniteCornerArc f n) t =
          H (pointRadialSectorPoint (((n + 1 : ℝ) * cR) * (1 - t.1)) θ)) := by
  let m : ℝ := n + 1
  have hm : 0 < m := by dsimp [m]; positivity
  have hm1 : 1 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hq : 0 < δ / m := div_pos hδ hm
  have hqhalf : δ / m < 1 / 2 := (div_lt_iff₀ hm).mpr (by nlinarith)
  refine ⟨hq, by linarith, by linarith, mul_pos hm hcL, mul_pos hm hcR, ?_, ?_⟩
  · intro t ht
    have hmt : m * (t : ℝ) ≤ δ := by
      have h := (le_div_iff₀ hm).mp ht
      nlinarith
    have hmtn : 0 ≤ m * (t : ℝ) := mul_nonneg hm.le t.2.1
    rw [euclideanFiniteCornerPeriodize_first_slot f n hf hv hclose t t.2 (by change m * _ ≤ 1; linarith)]
    rw [hleft _ ⟨hmtn, by linarith⟩ hmt]
    congr 2
    dsimp [m]
    ring
  · intro t ht
    have hmt : m - δ ≤ m * (t : ℝ) := by
      have hq' : 1 - (t : ℝ) ≤ δ / m := by linarith
      have h := (le_div_iff₀ hm).mp hq'
      nlinarith
    have hmt1 : m * (t : ℝ) ≤ m := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left t.2.2 hm.le
    have hlocal : m * (t : ℝ) - n ∈ Icc (0 : ℝ) 1 := by
      dsimp [m] at hmt hmt1 ⊢
      constructor <;> linarith
    rw [euclideanFiniteCornerPeriodize_last_slot f n hf hv hclose t t.2
      (by change (n : ℝ) ≤ m * _; dsimp [m] at hmt; linarith)]
    rw [hright _ hlocal (by dsimp [m] at hmt; linarith)]
    congr 2
    dsimp [m]
    ring

end RepulsiveCoulomb
