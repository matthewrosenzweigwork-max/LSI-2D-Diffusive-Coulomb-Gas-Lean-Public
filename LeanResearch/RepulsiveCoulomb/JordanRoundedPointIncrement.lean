module

public import LeanResearch.RepulsiveCoulomb.JordanCornerHomotopyIncrements
public import LeanResearch.RepulsiveCoulomb.JordanRadialRoundingWindows

@[expose] public section

/-! The actual finite local corner homotopies preserve the total physical
point-argument increment. There is no assumed global winding equality or
inside-preservation assertion. Half-corner and retained-middle increments
are compared from actual image equations and then summed by the permutation. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

def unitIntervalAffine (a b t : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨a + (b - a) * t, by
    have h₁ := mul_nonneg (sub_nonneg.mpr t.2.2) a.2.1
    have h₂ := mul_nonneg t.2.1 b.2.1
    have h₃ := mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr a.2.2)
    have h₄ := mul_nonneg t.2.1 (sub_nonneg.mpr b.2.2)
    constructor <;> nlinarith⟩

theorem unitIntervalAffine_continuous (a b : Icc (0 : ℝ) 1) :
    Continuous (unitIntervalAffine a b) :=
  (continuous_const.add (continuous_const.mul continuous_subtype_val)).subtype_mk _

@[simp] theorem unitIntervalAffine_zero (a b : Icc (0 : ℝ) 1) :
    unitIntervalAffine a b 0 = a := by apply Subtype.ext; simp [unitIntervalAffine]

@[simp] theorem unitIntervalAffine_one (a b : Icc (0 : ℝ) 1) :
    unitIntervalAffine a b 1 = b := by apply Subtype.ext; simp [unitIntervalAffine]

private theorem radialCorner_first_half (u v : ℂ) (t : Icc (0 : ℝ) 1) :
    euclideanRadialCorner u v (cornerFirstHalf t) = ((t : ℝ) - 1) • u := by
  change euclideanRadialCorner u v ((t : ℝ) / 2) = _
  rw [euclideanRadialCorner, if_pos (by linarith [t.2.2])]
  congr 1
  ring

private theorem radialCorner_second_half (u v : ℂ) (t : Icc (0 : ℝ) 1) :
    euclideanRadialCorner u v (cornerSecondHalf t) = (t : ℝ) • v := by
  change euclideanRadialCorner u v (((t : ℝ) + 1) / 2) = _
  unfold euclideanRadialCorner
  split_ifs with h
  · have ht : (t : ℝ) = 0 := by linarith [t.2.1]
    simp [ht]
  · congr 1
    ring

/-- Actual radial formulas and actual split-patch formulas identify all four
half-arcs of the constructed local homotopy. -/
theorem radial_rounding_homotopy_half_arcs
    {ι : Type*} (σ : Equiv.Perm ι) (f C E : ι → ℝ → ℂ)
    (H : ι → ℂ → ℂ) (u v : ι → ℂ) {δ : ℝ} (hδ : 0 < δ) (hδq : δ < 1 / 4)
    (hrad : ∀ i t, |t| ≤ δ →
      f (σ.symm i) (1 + t) = H i (t • u i) ∧ f i t = H i (t • v i))
    (hC : ∀ i t, t ∈ Icc (-δ) δ →
      C i t = H i (euclideanSymmetricCornerPatch δ (u i) (v i) t))
    (hEL : ∀ i t, t ∈ Icc (0 : ℝ) δ → E i t = C i t)
    (hER : ∀ i t, t ∈ Icc (1 - δ) 1 → E i t = C (σ i) (t - 1))
    (F : ι → Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℂ)
    (hF0 : ∀ i t, F i (0, t) = H i (euclideanRadialCorner (δ • u i) (δ • v i) t))
    (hF1 : ∀ i t, F i (1, t) = H i (euclideanBezierCorner (δ • u i) (δ • v i) t))
    (a b : Icc (0 : ℝ) 1) (ha : (a : ℝ) = δ) (hb : (b : ℝ) = 1 - δ) :
    ∀ i t,
      F i (0, cornerFirstHalf t) = f (σ.symm i) (unitIntervalAffine b 1 t) ∧
      F i (0, cornerSecondHalf t) = f i (unitIntervalAffine 0 a t) ∧
      F i (1, cornerFirstHalf t) = E (σ.symm i) (unitIntervalAffine b 1 t) ∧
      F i (1, cornerSecondHalf t) = E i (unitIntervalAffine 0 a t) := by
  intro i t
  have hinval : (unitIntervalAffine b 1 t : ℝ) = 1 + δ * ((t : ℝ) - 1) := by
    change (b : ℝ) + (1 - (b : ℝ)) * (t : ℝ) = _
    rw [hb]
    norm_num
    ring
  have houtval : (unitIntervalAffine 0 a t : ℝ) = δ * (t : ℝ) := by
    simp only [unitIntervalAffine, Set.Icc.coe_zero, zero_add, sub_zero, ha]
  have hinbounds : δ * ((t : ℝ) - 1) ∈ Icc (-δ) (0 : ℝ) := by
    constructor <;> nlinarith [t.2.1, t.2.2]
  have houtbounds : δ * (t : ℝ) ∈ Icc (0 : ℝ) δ := by
    constructor <;> nlinarith [t.2.1, t.2.2]
  have hinabs : |δ * ((t : ℝ) - 1)| ≤ δ := abs_le.mpr ⟨hinbounds.1, by linarith [hinbounds.2]⟩
  have houtabs : |δ * (t : ℝ)| ≤ δ := abs_le.mpr ⟨by linarith [houtbounds.1], houtbounds.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hF0, radialCorner_first_half, smul_smul, hinval,
      (hrad i _ hinabs).1]
    congr 2
    ring
  · rw [hF0, radialCorner_second_half, smul_smul, houtval,
      (hrad i _ houtabs).2]
    congr 2
    ring
  · rw [hER (σ.symm i) _ (by rw [hinval]; constructor <;> linarith [hinbounds.1, hinbounds.2]),
      σ.apply_symm_apply, hinval,
      show 1 + δ * ((t : ℝ) - 1) - 1 = δ * ((t : ℝ) - 1) by ring,
      hC i _ ⟨hinbounds.1, by linarith [hinbounds.2]⟩, hF1]
    congr 1
    unfold euclideanSymmetricCornerPatch
    congr 1
    change (t : ℝ) / 2 = (δ * ((t : ℝ) - 1) + δ) / (2 * δ)
    field_simp [hδ.ne']
    ring
  · rw [hEL i _ (by rw [houtval]; exact houtbounds), houtval,
      hC i _ ⟨by linarith [houtbounds.1], houtbounds.2⟩, hF1]
    congr 1
    unfold euclideanSymmetricCornerPatch
    congr 1
    change ((t : ℝ) + 1) / 2 = (δ * (t : ℝ) + δ) / (2 * δ)
    field_simp [hδ.ne']

/-- Full finite preservation of actual point argument under simultaneous
rounding. The witnesses are exactly the actual outputs of the constructed
rounding theorem, plus actual argument lifts. No turn/winding identity is
among the assumptions. -/
theorem finite_radial_rounding_preserves_point_argument_sum
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (f C E : ι → ℝ → ℂ)
    (H : ι → ℂ → ℂ) (u v : ι → ℂ) {δ : ℝ} (hδ : 0 < δ) (hδq : δ < 1 / 4)
    (hrad : ∀ i t, |t| ≤ δ →
      f (σ.symm i) (1 + t) = H i (t • u i) ∧ f i t = H i (t • v i))
    (hC : ∀ i t, t ∈ Icc (-δ) δ →
      C i t = H i (euclideanSymmetricCornerPatch δ (u i) (v i) t))
    (hEL : ∀ i t, t ∈ Icc (0 : ℝ) δ → E i t = C i t)
    (hER : ∀ i t, t ∈ Icc (1 - δ) 1 → E i t = C (σ i) (t - 1))
    (hmid : ∀ i t, t ∈ Icc δ (1 - δ) → E i t = f i t)
    (F : ι → Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℂ)
    (hF : ∀ i, Continuous (F i))
    (hF0 : ∀ i t, F i (0, t) = H i (euclideanRadialCorner (δ • u i) (δ • v i) t))
    (hF1 : ∀ i t, F i (1, t) = H i (euclideanBezierCorner (δ • u i) (δ • v i) t))
    (hFs : ∀ i s, F i (s, 0) = F i (0, 0))
    (hFt : ∀ i s, F i (s, 1) = F i (0, 1))
    (w : ℂ) (havoid : ∀ i q, F i q ≠ w)
    (θ ψ : ι → Icc (0 : ℝ) 1 → ℝ)
    (hθ : ∀ i, Continuous (θ i)) (hψ : ∀ i, Continuous (ψ i))
    (hθl : ∀ i t, Complex.exp ((θ i t : ℂ) * Complex.I) =
      (f i t - w) / (‖f i t - w‖ : ℂ))
    (hψl : ∀ i t, Complex.exp ((ψ i t : ℂ) * Complex.I) =
      (E i t - w) / (‖E i t - w‖ : ℂ)) :
    (∑ i, (ψ i 1 - ψ i 0)) = ∑ i, (θ i 1 - θ i 0) := by
  let a : Icc (0 : ℝ) 1 := ⟨δ, hδ.le, by linarith⟩
  let b : Icc (0 : ℝ) 1 := ⟨1 - δ, by constructor <;> linarith⟩
  have hab : (a : ℝ) < b := by dsimp [a, b]; linarith
  have hhalves := radial_rounding_homotopy_half_arcs σ f C E H u v hδ hδq
    hrad hC hEL hER F hF0 hF1 a b rfl rfl
  have hcorner (i : ι) :
      (θ (σ.symm i) 1 - θ (σ.symm i) b) + (θ i a - θ i 0) =
      (ψ (σ.symm i) 1 - ψ (σ.symm i) b) + (ψ i a - ψ i 0) := by
    have he := corner_homotopy_preserves_incident_point_increments (F i) (hF i)
      (hFs i) (hFt i) w (havoid i)
      (θ (σ.symm i) ∘ unitIntervalAffine b 1) (θ i ∘ unitIntervalAffine 0 a)
      (ψ (σ.symm i) ∘ unitIntervalAffine b 1) (ψ i ∘ unitIntervalAffine 0 a)
      ((hθ _).comp (unitIntervalAffine_continuous _ _))
      ((hθ _).comp (unitIntervalAffine_continuous _ _))
      ((hψ _).comp (unitIntervalAffine_continuous _ _))
      ((hψ _).comp (unitIntervalAffine_continuous _ _))
      (fun t => by rw [(hhalves i t).1]; exact hθl _ _)
      (fun t => by rw [(hhalves i t).2.1]; exact hθl _ _)
      (fun t => by rw [(hhalves i t).2.2.1]; exact hψl _ _)
      (fun t => by rw [(hhalves i t).2.2.2]; exact hψl _ _)
    simpa only [Function.comp_apply, unitIntervalAffine_zero, unitIntervalAffine_one] using he
  have hmiddle (i : ι) : θ i b - θ i a = ψ i b - ψ i a := by
    have hmaps (t : Icc (0 : ℝ) 1) : (unitIntervalAffine a b t : ℝ) ∈ Icc δ (1 - δ) := by
      change δ ≤ δ + ((1 - δ) - δ) * (t : ℝ) ∧
        δ + ((1 - δ) - δ) * (t : ℝ) ≤ 1 - δ
      constructor <;> nlinarith [t.2.1, t.2.2]
    have he := euclidean_angle_lift_increment_eq
      ((hθ i).comp (unitIntervalAffine_continuous a b))
      ((hψ i).comp (unitIntervalAffine_continuous a b))
      (fun t => by
        apply Circle.ext
        change Complex.exp ((θ i (unitIntervalAffine a b t) : ℂ) * Complex.I) =
          Complex.exp ((ψ i (unitIntervalAffine a b t) : ℂ) * Complex.I)
        rw [hθl, hψl, hmid i _ (hmaps t)]) (0 : Icc (0 : ℝ) 1) 1
    simpa only [Function.comp_apply, unitIntervalAffine_zero, unitIntervalAffine_one] using he
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hcorner i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    σ.symm.sum_comp (fun i => θ i 1 - θ i b),
    σ.symm.sum_comp (fun i => ψ i 1 - ψ i b)] at hsum
  have hmidsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hmiddle i)
  simp only [Finset.sum_sub_distrib] at hsum hmidsum ⊢
  linarith

end RepulsiveCoulomb
