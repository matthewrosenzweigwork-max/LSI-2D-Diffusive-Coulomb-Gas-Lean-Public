import LeanResearch.RepulsiveCoulomb.JordanFiniteC1OrientedTurn
import LeanResearch.RepulsiveCoulomb.PlaneJordanSeparation

/-! Nonzero ACTUAL point winding identifies the actual bounded component of
a constructed finite regular simple matched-jet loop. In particular this
bridge does not assume that local rounding preserves the inside component. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

theorem finite_matched_regular_arc_nonzero_argument_eq_turn
    (f : ℕ → ℝ → ℂ) (n : ℕ)
    (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0)
    (hd : ∀ k < n, deriv (f k) 1 = deriv (f (k + 1)) 0)
    (hclose : f n 1 = f 0 0) (hcloseD : deriv (f n) 1 = deriv (f 0) 0)
    (hreg : ∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1, deriv (f k) t ≠ 0)
    (hinj : ∀ k ≤ n, InjOn (f k) (Ico (0 : ℝ) 1))
    (hdisj : ∀ i ≤ n, ∀ j ≤ n, i ≠ j →
      Disjoint (f i '' Ico (0 : ℝ) 1) (f j '' Ico (0 : ℝ) 1))
    (w : ℂ) (hw : w ∉ ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)
    (θ ψ : ℕ → Icc (0 : ℝ) 1 → ℝ)
    (hθ : ∀ k ≤ n, Continuous (θ k)) (hψ : ∀ k ≤ n, Continuous (ψ k))
    (hθlift : ∀ k ≤ n, ∀ t, Complex.exp ((θ k t : ℂ) * Complex.I) =
      deriv (f k) t / (‖deriv (f k) t‖ : ℂ))
    (hψlift : ∀ k ≤ n, ∀ t, Complex.exp ((ψ k t : ℂ) * Complex.I) =
      (f k t - w) / (‖f k t - w‖ : ℂ))
    (hpoint : (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) ≠ 0) :
    (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) =
      ∑ k ∈ Finset.range (n + 1), (θ k 1 - θ k 0) := by
  obtain ⟨Γ, hΓ, hΓclose, _, hΓinj, _, himage, hslots⟩ :=
    exists_finite_matched_regular_C1_loop f n hf hv hd hclose hcloseD hreg hinj hdisj
  obtain ⟨U, V, hU, hV, hUc, hVc, _, hcover, hfront, _, hK, _, _⟩ :=
    jordan_separation_of_homeomorph Complex.orthonormalBasisOneI.repr.toHomeomorph
      Γ hΓ.continuous.continuousOn hΓclose hΓinj
  have hW (t : Icc (0 : ℝ) 1) : Γ t - w ≠ 0 := by
    intro hz
    apply hw
    rw [← himage]
    exact ⟨t, t.2, sub_eq_zero.mp hz⟩
  obtain ⟨Ψ, hΨ, hΨlift⟩ := exists_interval_euclidean_angle_lift
    ((hΓ.continuous.comp continuous_subtype_val).sub continuous_const) hW
  have hsum : (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) = Ψ 1 - Ψ 0 := by
    apply finite_unit_slot_angle_increment_sum n ψ Ψ hψ hΨ
    intro k hk t
    apply Circle.ext
    change Complex.exp ((ψ k t : ℂ) * Complex.I) = Complex.exp ((Ψ _ : ℂ) * Complex.I)
    rw [hψlift k hk, hΨlift]
    simp only [Pi.sub_apply, Function.comp_apply]
    rw [(hslots k hk t t.2).1]
  have hwC : w ∈ (Γ '' Icc (0 : ℝ) 1)ᶜ := by rwa [himage]
  have hwUV : w ∈ U ∪ V := hcover.symm ▸ hwC
  have hwU : w ∈ U := by
    rcases hwUV with hi | ho
    · exact hi
    · have hrange : range (fun t : Icc (0 : ℝ) 1 => Γ t) = Γ '' Icc (0 : ℝ) 1 := by
        ext z
        simp only [mem_range, mem_image]
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨t, t.2, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨⟨t, ht⟩, rfl⟩
      have hz := jordan_outside_argument_increment_zero
        (fun t : Icc (0 : ℝ) 1 => Γ t) (hΓ.continuous.comp continuous_subtype_val)
        hΓclose hK hV hVc (by rwa [hrange]) ho Ψ hΨ hΨlift
      exact (hpoint (hsum.trans hz)).elim
  exact finite_matched_regular_arc_inside_argument_eq_turn f n hf hv hd hclose hcloseD
    hreg hinj hdisj hU hUc hV hVc hK (hfront.trans himage)
    (by simpa only [himage] using hcover) hwU θ ψ hθ hψ hθlift hψlift

/-- Reindex an actual finite cycle by its explicitly enumerated distinct
slots. This works without a preferred cyclic index representation. -/
theorem finite_cycle_enumeration_sum {ι : Type*} [Fintype ι]
    (n : ℕ) (e : ℕ → ι)
    (hinj : ∀ j ≤ n, ∀ k ≤ n, e j = e k → j = k)
    (hsurj : ∀ i, ∃ k ≤ n, e k = i) (g : ι → ℝ) :
    (∑ k ∈ Finset.range (n + 1), g (e k)) = ∑ i, g i := by
  classical
  apply Finset.sum_bij (fun k _ => e k) (fun _ _ => Finset.mem_univ _)
  · intro j hj k hk heq
    exact hinj j (by have h := Finset.mem_range.mp hj; omega)
      k (by have h := Finset.mem_range.mp hk; omega) heq
  · intro i _
    obtain ⟨k, hk, he⟩ := hsurj i
    exact ⟨k, Finset.mem_range.mpr (by omega), he⟩
  · intro _ _
    rfl

/-- An actually enumerated regular simple matched-jet family has its tangent
sum equal to every nonzero actual point-argument sum. The whole smooth loop
and the bounded component containing the observer are constructed internally. -/
theorem enumerated_matched_regular_cycle_nonzero_argument_eq_turn
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (n : ℕ) (e : ℕ → ι)
    (heinj : ∀ j ≤ n, ∀ k ≤ n, e j = e k → j = k)
    (hesurj : ∀ i, ∃ k ≤ n, e k = i)
    (henext : ∀ k < n, σ (e k) = e (k + 1)) (heclose : σ (e n) = e 0)
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 1 (f i))
    (hv : ∀ i, f i 1 = f (σ i) 0)
    (hd : ∀ i, deriv (f i) 1 = deriv (f (σ i)) 0)
    (hreg : ∀ i t, t ∈ Icc (0 : ℝ) 1 → deriv (f i) t ≠ 0)
    (hinj : ∀ i j s t, s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t)
    (w : ℂ) (hw : ∀ i t, t ∈ Icc (0 : ℝ) 1 → f i t ≠ w)
    (θ ψ : ι → Icc (0 : ℝ) 1 → ℝ)
    (hθ : ∀ i, Continuous (θ i)) (hψ : ∀ i, Continuous (ψ i))
    (hθl : ∀ i t, Complex.exp ((θ i t : ℂ) * Complex.I) = deriv (f i) t / (‖deriv (f i) t‖ : ℂ))
    (hψl : ∀ i t, Complex.exp ((ψ i t : ℂ) * Complex.I) = (f i t - w) / (‖f i t - w‖ : ℂ))
    (hpoint : (∑ i, (ψ i 1 - ψ i 0)) ≠ 0) :
    (∑ i, (ψ i 1 - ψ i 0)) = ∑ i, (θ i 1 - θ i 0) := by
  have hv' (k : ℕ) (hk : k < n) : f (e k) 1 = f (e (k + 1)) 0 := by rw [hv, henext k hk]
  have hd' (k : ℕ) (hk : k < n) : deriv (f (e k)) 1 = deriv (f (e (k + 1))) 0 := by
    rw [hd, henext k hk]
  have hclose : f (e n) 1 = f (e 0) 0 := by rw [hv, heclose]
  have hcloseD : deriv (f (e n)) 1 = deriv (f (e 0)) 0 := by rw [hd, heclose]
  have hinj' (k : ℕ) (_ : k ≤ n) : InjOn (f (e k)) (Ico (0 : ℝ) 1) :=
    fun s hs t ht he => (hinj _ _ s t hs ht he).2
  have hdisj : ∀ j ≤ n, ∀ k ≤ n, j ≠ k →
      Disjoint (f (e j) '' Ico (0 : ℝ) 1) (f (e k) '' Ico (0 : ℝ) 1) := by
    intro j hj k hk hne
    apply Set.disjoint_left.mpr
    rintro z ⟨s, hs, hsz⟩ ⟨t, ht, htz⟩
    exact hne (heinj j hj k hk (hinj _ _ s t hs ht (hsz.trans htz.symm)).1)
  have hw' : w ∉ ⋃ k ≤ n, f (e k) '' Icc (0 : ℝ) 1 := by
    simp only [mem_iUnion, mem_image]
    rintro ⟨k, hk, t, ht, he⟩
    exact hw (e k) t ht he
  have hsum := finite_cycle_enumeration_sum n e heinj hesurj
  have he := finite_matched_regular_arc_nonzero_argument_eq_turn (fun k => f (e k)) n
    (fun k _ => hf (e k)) hv' hd' hclose hcloseD (fun k _ => hreg (e k)) hinj' hdisj
    w hw' (fun k => θ (e k)) (fun k => ψ (e k))
    (fun k _ => hθ (e k)) (fun k _ => hψ (e k))
    (fun k _ => hθl (e k)) (fun k _ => hψl (e k))
    (by rwa [hsum (fun i => ψ i 1 - ψ i 0)])
  rwa [hsum (fun i => ψ i 1 - ψ i 0), hsum (fun i => θ i 1 - θ i 0)] at he

end RepulsiveCoulomb
