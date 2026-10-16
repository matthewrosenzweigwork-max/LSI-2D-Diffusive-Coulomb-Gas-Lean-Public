module

public import LeanResearch.RepulsiveCoulomb.JordanRadialCornerTangentAccounting
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section

/-! Actual finite tangent-turn preservation under simultaneous radial
rounding. Every chart disk, physical radial trace, positive source clock,
endpoint derivative comparison and permutation sum is used explicitly. -/
noncomputable section
open Set Metric
open scoped BigOperators
namespace RepulsiveCoulomb

theorem radial_corner_curves_mem_ball {u v : ℂ} {R : ℝ}
    (hu : ‖u‖ < R) (hv : ‖v‖ < R) :
    MapsTo (euclideanIncomingRadius u) (Icc (0 : ℝ) 1) (ball (0 : ℂ) R) ∧
      MapsTo (euclideanOutgoingRadius v) (Icc (0 : ℝ) 1) (ball (0 : ℂ) R) ∧
      MapsTo (euclideanBezierCorner u v) (Icc (0 : ℝ) 1) (ball (0 : ℂ) R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [mem_ball_zero_iff, euclideanIncomingRadius, norm_smul, Real.norm_eq_abs]
    have ha : |t - 1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg u)).trans_lt (by simpa using hu)
  · intro t ht
    rw [mem_ball_zero_iff, euclideanOutgoingRadius, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans_lt (by simpa using hv)
  · intro t ht
    rw [mem_ball_zero_iff]
    exact (euclideanBezierCorner_norm_le
      (le_max_of_le_left (norm_nonneg u)) (le_max_left _ _) (le_max_right _ _) ht).trans_lt
      (max_lt hu hv)

/-- The sum of the actual rounded turns equals the old actual arc turns plus
all actual principal corner turns. This theorem uses the concrete output
properties of the constructed rounding, not an angle-sum certificate. -/
theorem finite_radial_rounding_preserves_tangent_turn_sum
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (f C E : ι → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (hE : ∀ i, ContDiff ℝ 1 (E i))
    (hfr : ∀ i t, t ∈ Icc (0 : ℝ) 1 → deriv (f i) t ≠ 0)
    (hEr : ∀ i t, t ∈ Icc (0 : ℝ) 1 → deriv (E i) t ≠ 0)
    (V : ι → Set ℂ) (H : ι → ℂ → ℂ)
    (hH : ∀ i, AnalyticOnNhd ℂ (H i) (V i))
    (hHreg : ∀ i z, z ∈ V i → deriv (H i) z ≠ 0)
    (hHinj : ∀ i, InjOn (H i) (V i))
    (u v : ι → ℂ) (hu : ∀ i, u i ≠ 0) (hc : ∀ i, v i / u i ∈ Complex.slitPlane)
    {δ R : ℝ} (hδ : 0 < δ) (hδq : δ < 1 / 4) (hR : 0 < R)
    (hRV : ∀ i, closedBall (0 : ℂ) R ⊆ V i)
    (hnorm : ∀ i, ‖δ • u i‖ < R ∧ ‖δ • v i‖ < R)
    (hrad : ∀ i t, |t| ≤ δ →
      f (σ.symm i) (1 + t) = H i (t • u i) ∧ f i t = H i (t • v i))
    (hC : ∀ i t, t ∈ Icc (-δ) δ →
      C i t = H i (euclideanSymmetricCornerPatch δ (u i) (v i) t))
    (hEL : ∀ i t, t ∈ Icc (0 : ℝ) δ → E i t = C i t)
    (hER : ∀ i t, t ∈ Icc (1 - δ) 1 → E i t = C (σ i) (t - 1))
    (hmid : ∀ i t, t ∈ Icc δ (1 - δ) → E i t = f i t)
    (θ ψ : ι → Icc (0 : ℝ) 1 → ℝ)
    (hθ : ∀ i, Continuous (θ i)) (hψ : ∀ i, Continuous (ψ i))
    (hθl : ∀ i t, Complex.exp ((θ i t : ℂ) * Complex.I) = deriv (f i) t / (‖deriv (f i) t‖ : ℂ))
    (hψl : ∀ i t, Complex.exp ((ψ i t : ℂ) * Complex.I) = deriv (E i) t / (‖deriv (E i) t‖ : ℂ)) :
    (∑ i, (ψ i 1 - ψ i 0)) = (∑ i, (θ i 1 - θ i 0)) +
      ∑ i, Complex.arg (deriv (f i) 0 / deriv (f (σ.symm i)) 1) := by
  let a : Icc (0 : ℝ) 1 := ⟨δ, hδ.le, by linarith⟩
  let b : Icc (0 : ℝ) 1 := ⟨1 - δ, by constructor <;> linarith⟩
  let F : ι → Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℂ :=
    fun i q => H i (euclideanCornerReplacement (δ • u i) (δ • v i) q.1 q.2)
  have hF0 (i : ι) (t : Icc (0 : ℝ) 1) :
      F i (0, t) = H i (euclideanRadialCorner (δ • u i) (δ • v i) t) := by simp [F]
  have hF1 (i : ι) (t : Icc (0 : ℝ) 1) :
      F i (1, t) = H i (euclideanBezierCorner (δ • u i) (δ • v i) t) := by simp [F]
  have hhalves := radial_rounding_homotopy_half_arcs σ f C E H u v hδ hδq
    hrad hC hEL hER F hF0 hF1 a b rfl rfl
  have hballV (i : ι) : ball (0 : ℂ) R ⊆ V i := ball_subset_closedBall.trans (hRV i)
  have hsimply : IsSimplyConnected (ball (0 : ℂ) R) := by
    letI : ContractibleSpace (ball (0 : ℂ) R) :=
      (convex_ball (0 : ℂ) R).contractibleSpace ⟨0, mem_ball_self hR⟩
    change SimplyConnectedSpace (ball (0 : ℂ) R)
    infer_instance
  have hcorner (i : ι) :
      (ψ (σ.symm i) 1 - ψ (σ.symm i) b) + (ψ i a - ψ i 0) =
      (θ (σ.symm i) 1 - θ (σ.symm i) b) + (θ i a - θ i 0) +
        Complex.arg (deriv (f i) 0 / deriv (f (σ.symm i)) 1) := by
    have hcutu : δ • u i ≠ 0 := smul_ne_zero hδ.ne' (hu i)
    have hcutratio : (δ • v i) / (δ • u i) ∈ Complex.slitPlane := by
      have hδc : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
      have he : (δ • v i) / (δ • u i) = v i / u i := by
        simp only [Complex.real_smul]
        field_simp [hδc, hu i]
      rw [he]
      exact hc i
    obtain ⟨hLU, hRU, hBU⟩ := radial_corner_curves_mem_ball (hnorm i).1 (hnorm i).2
    have holdL (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        f (σ.symm i) ((1 - δ) + δ * t) = H i (euclideanIncomingRadius (δ • u i) t) := by
      have habs : |δ * (t - 1)| ≤ δ := abs_le.mpr (by constructor <;> nlinarith [ht.1, ht.2])
      rw [show (1 - δ) + δ * t = 1 + δ * (t - 1) by ring, (hrad i _ habs).1]
      congr 1
      simp only [euclideanIncomingRadius, smul_smul]
      congr 1
      ring
    have holdR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        f i (δ * t) = H i (euclideanOutgoingRadius (δ • v i) t) := by
      have habs : |δ * t| ≤ δ := abs_le.mpr (by constructor <;> nlinarith [ht.1, ht.2])
      rw [(hrad i _ habs).2]
      congr 1
      simp only [euclideanOutgoingRadius, smul_smul]
      congr 1
      ring
    have hnewL (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        E (σ.symm i) ((1 - δ) + δ * t) =
          H i (euclideanBezierCorner (δ • u i) (δ • v i) (t / 2)) := by
      have he := (hhalves i ⟨t, ht⟩).2.2.1
      rw [hF1] at he
      change H i (euclideanBezierCorner (δ • u i) (δ • v i) (t / 2)) =
        E (σ.symm i) ((1 - δ) + (1 - (1 - δ)) * t) at he
      simpa only [show 1 - (1 - δ) = δ by ring] using he.symm
    have hnewR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        E i (δ * t) =
          H i (euclideanBezierCorner (δ • u i) (δ • v i) ((t + 1) / 2)) := by
      have he := (hhalves i ⟨t, ht⟩).2.2.2
      rw [hF1] at he
      change H i (euclideanBezierCorner (δ • u i) (δ • v i) ((t + 1) / 2)) =
        E i (0 + (δ - 0) * t) at he
      simpa only [sub_zero, zero_add] using he.symm
    exact radial_corner_rounding_tangent_accounting isOpen_ball hsimply
      ((hH i).mono (hballV i)) (fun z hz => hHreg i z (hballV i hz))
      ((hHinj i).mono (hballV i)) hcutu hcutratio hLU hRU hBU
      (f (σ.symm i)) (f i) (E (σ.symm i)) (E i)
      (hf _) (hf _) (hE _) (hE _) (hfr _) (hfr _) (hEr _) (hEr _)
      hδ hδq holdL holdR hnewL hnewR a b rfl rfl
      (θ _) (θ _) (ψ _) (ψ _) (hθ _) (hθ _) (hψ _) (hψ _)
      (hθl _) (hθl _) (hψl _) (hψl _)
  have hmiddle (i : ι) : ψ i b - ψ i a = θ i b - θ i a := by
    have hcpos : 0 < (1 - δ) - δ := by linarith
    have hmaps (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        δ + ((1 - δ) - δ) * t ∈ Icc δ (1 - δ) := by
      constructor <;> nlinarith [ht.1, ht.2]
    have hmapunit (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        δ + ((1 - δ) - δ) * t ∈ Icc (0 : ℝ) 1 :=
      ⟨hδ.le.trans (hmaps t ht).1, (hmaps t ht).2.trans (by linarith)⟩
    have he := euclidean_angle_lift_increment_eq
      ((hψ i).comp (unitIntervalAffine_continuous a b))
      ((hθ i).comp (unitIntervalAffine_continuous a b))
      (fun t => by
        apply Circle.ext
        change Complex.exp ((ψ i (unitIntervalAffine a b t) : ℂ) * Complex.I) =
          Complex.exp ((θ i (unitIntervalAffine a b t) : ℂ) * Complex.I)
        rw [hψl, hθl]
        exact positive_affine_trace_tangent_direction ((hE i).differentiable (by norm_num))
          ((hf i).differentiable (by norm_num)) hcpos hcpos t.2
          (fun s hs => hmid i _ (hmaps s hs)) (hEr i _ (hmapunit t t.2))
          (hfr i _ (hmapunit t t.2))) (0 : Icc (0 : ℝ) 1) 1
    simpa only [Function.comp_apply, unitIntervalAffine_zero, unitIntervalAffine_one] using he
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hcorner i)
  simp only [Finset.sum_add_distrib] at hsum
  rw [σ.symm.sum_comp (fun i => ψ i 1 - ψ i b),
    σ.symm.sum_comp (fun i => θ i 1 - θ i b)] at hsum
  have hmidsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hmiddle i)
  simp only [Finset.sum_sub_distrib] at hsum hmidsum ⊢
  linarith

end RepulsiveCoulomb
