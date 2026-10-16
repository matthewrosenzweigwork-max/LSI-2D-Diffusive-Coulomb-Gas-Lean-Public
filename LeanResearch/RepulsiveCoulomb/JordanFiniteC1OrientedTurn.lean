import LeanResearch.RepulsiveCoulomb.JordanFiniteC1TurnSum
import LeanResearch.RepulsiveCoulomb.JordanSmoothWindingOrientation

/-! The oriented finite turn sum for a genuinely constructed matched-jet
simple loop. The sign is identified with the actual argument increment about
the actual bounded Jordan component. No orientation or turn-sum certificate
is an input. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

/-- Actual local lifts agreeing with the restriction of one global lift have
the global increment as their finite sum. No choice of additive constants is
needed. This is the concrete equal-slot subdivision used by finite pasting. -/
theorem finite_unit_slot_angle_increment_sum
    (n : ℕ) (θ : ℕ → Icc (0 : ℝ) 1 → ℝ) (Θ : Icc (0 : ℝ) 1 → ℝ)
    (hθ : ∀ k ≤ n, Continuous (θ k)) (hΘ : Continuous Θ)
    (hlift : ∀ k (hk : k ≤ n) (t : Icc (0 : ℝ) 1),
      Circle.exp (θ k t) = Circle.exp (Θ
        ⟨((k : ℝ) + t) / (n + 1 : ℝ),
          div_nonneg (add_nonneg (Nat.cast_nonneg k) t.2.1) (by positivity),
          (div_le_one (by positivity : 0 < (n + 1 : ℝ))).mpr
            (by have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
                linarith [t.2.2])⟩)) :
    (∑ k ∈ Finset.range (n + 1), (θ k 1 - θ k 0)) = Θ 1 - Θ 0 := by
  let m : ℝ := n + 1
  have hm : 0 < m := by dsimp [m]; positivity
  let Q := Set.IccExtend (show (0 : ℝ) ≤ 1 by norm_num) Θ
  have hincrement (k : ℕ) (hk : k ≤ n) :
      θ k 1 - θ k 0 = Q (((k : ℝ) + 1) / m) - Q ((k : ℝ) / m) := by
    have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
    let σ : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun t =>
      ⟨((k : ℝ) + t) / m, div_nonneg (add_nonneg (Nat.cast_nonneg k) t.2.1) hm.le,
        (div_le_one hm).mpr (by dsimp [m]; linarith [t.2.2])⟩
    have hσ : Continuous σ :=
      ((continuous_const.add continuous_subtype_val).div_const m).subtype_mk _
    have hi := euclidean_angle_lift_increment_eq (hθ k hk) (hΘ.comp hσ)
      (hlift k hk) (0 : Icc (0 : ℝ) 1) 1
    have hQ0 : Q ((k : ℝ) / m) = Θ (σ 0) := by
      have hkm : (k : ℝ) / m ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (Nat.cast_nonneg k) hm.le,
          (div_le_one hm).mpr (by dsimp [m]; linarith)⟩
      dsimp only [Q]
      rw [Set.IccExtend_of_mem (show (0 : ℝ) ≤ 1 by norm_num) Θ hkm]
      congr 1
      apply Subtype.ext
      simp [σ]
    have hQ1 : Q (((k : ℝ) + 1) / m) = Θ (σ 1) := by
      have hkm : ((k : ℝ) + 1) / m ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (by positivity) hm.le,
          (div_le_one hm).mpr (by dsimp [m]; linarith)⟩
      dsimp only [Q]
      rw [Set.IccExtend_of_mem (show (0 : ℝ) ≤ 1 by norm_num) Θ hkm]
      congr 1
    rw [hQ0, hQ1]
    exact hi
  calc
    (∑ k ∈ Finset.range (n + 1), (θ k 1 - θ k 0)) =
        ∑ k ∈ Finset.range (n + 1), (Q (((k : ℝ) + 1) / m) - Q ((k : ℝ) / m)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hincrement k (by have h := Finset.mem_range.mp hk; omega)
    _ = Q (((n + 1 : ℕ) : ℝ) / m) - Q (0 / m) := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
        Finset.sum_range_sub (fun k : ℕ => Q ((k : ℝ) / m)) (n + 1)
    _ = Θ 1 - Θ 0 := by
      have hnm : ((n + 1 : ℕ) : ℝ) = m := by simp [m]
      rw [hnm, div_self hm.ne', zero_div]
      simp [Q]

/-- The actual bounded-component point-argument sum equals the actual signed
tangent-turn sum of every finite regular simple matched-jet cyclic family.
The constructed global parametrization and its argument lifts are internal
to the proof. In particular the two sums cannot acquire unrelated signs. -/
theorem finite_matched_regular_arc_inside_argument_eq_turn
    (f : ℕ → ℝ → ℂ) (n : ℕ)
    (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0)
    (hd : ∀ k < n, deriv (f k) 1 = deriv (f (k + 1)) 0)
    (hclose : f n 1 = f 0 0) (hcloseD : deriv (f n) 1 = deriv (f 0) 0)
    (hreg : ∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1, deriv (f k) t ≠ 0)
    (hinj : ∀ k ≤ n, InjOn (f k) (Ico (0 : ℝ) 1))
    (hdisj : ∀ i ≤ n, ∀ j ≤ n, i ≠ j →
      Disjoint (f i '' Ico (0 : ℝ) 1) (f j '' Ico (0 : ℝ) 1))
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hK : IsCompact (closure U))
    (hfront : frontier U = ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)
    (hcover : U ∪ V = (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)ᶜ)
    {w : ℂ} (hw : w ∈ U)
    (θ ψ : ℕ → Icc (0 : ℝ) 1 → ℝ)
    (hθ : ∀ k ≤ n, Continuous (θ k)) (hψ : ∀ k ≤ n, Continuous (ψ k))
    (hθlift : ∀ k ≤ n, ∀ t, Complex.exp ((θ k t : ℂ) * Complex.I) =
      deriv (f k) t / (‖deriv (f k) t‖ : ℂ))
    (hψlift : ∀ k ≤ n, ∀ t, Complex.exp ((ψ k t : ℂ) * Complex.I) =
      (f k t - w) / (‖f k t - w‖ : ℂ)) :
    (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) =
      ∑ k ∈ Finset.range (n + 1), (θ k 1 - θ k 0) := by
  obtain ⟨Γ, hΓ, hΓclose, hΓjet, hΓinj, hΓreg, himage, hslots⟩ :=
    exists_finite_matched_regular_C1_loop f n hf hv hd hclose hcloseD hreg hinj hdisj
  obtain ⟨Θ, hΘ, hΘlift⟩ := exists_regular_edge_tangent_angle_lift hΓ hΓreg
  have hW (t : Icc (0 : ℝ) 1) : Γ t - w ≠ 0 := by
    intro hz
    have hwC : w ∈ (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)ᶜ := hcover ▸ Or.inl hw
    apply hwC
    rw [← himage]
    exact ⟨t, t.2, sub_eq_zero.mp hz⟩
  obtain ⟨Ψ, hΨ, hΨlift⟩ := exists_interval_euclidean_angle_lift
    ((hΓ.continuous.comp continuous_subtype_val).sub continuous_const) hW
  let γ := euclideanC1Periodize Γ
  have hγ : ContDiff ℝ 1 γ := euclideanC1Periodize_contDiff hΓ hΓjet
  have hp : Function.Periodic γ 1 := euclideanC1Periodize_periodic hΓ hΓclose hΓjet
  have hvalue (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t = Γ t :=
    euclideanC1Periodize_eq hΓ hΓjet ht
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : deriv γ t = deriv Γ t := by
    rw [euclideanC1Periodize_deriv hΓ hΓjet, euclideanPeriodicTangent_eq hΓjet ht]
  have hγinj : InjOn γ (Ico (0 : ℝ) 1) := by
    intro s hs t ht heq
    apply hΓinj hs ht
    simpa only [hvalue s (Ico_subset_Icc_self hs), hvalue t (Ico_subset_Icc_self ht)] using heq
  have hγreg : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0 := by
    intro t ht
    rw [hderiv t ht]
    exact hΓreg t ht
  have hγimage : γ '' Icc (0 : ℝ) 1 = ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 :=
    (show EqOn γ Γ (Icc (0 : ℝ) 1) from hvalue).image_eq.trans himage
  have horient : Ψ 1 - Ψ 0 = Θ 1 - Θ 0 :=
    regular_simple_periodic_loop_inside_argument_eq_turn hγ hp hγinj hγreg
      hU hUc hV hVc hK (hfront.trans hγimage.symm) (by rwa [hγimage]) hw hΘ hΨ
      (fun t => by rw [hderiv t t.2]; exact hΘlift t)
      (fun t => by rw [hvalue t t.2]; exact hΨlift t)
  have hsumθ : (∑ k ∈ Finset.range (n + 1), (θ k 1 - θ k 0)) = Θ 1 - Θ 0 := by
    apply finite_unit_slot_angle_increment_sum n θ Θ hθ hΘ
    intro k hk t
    apply Circle.ext
    change Complex.exp ((θ k t : ℂ) * Complex.I) = Complex.exp ((Θ _ : ℂ) * Complex.I)
    rw [hθlift k hk, hΘlift, (hslots k hk t t.2).2]
    exact (congrArg (fun z : Circle => (z : ℂ))
      (euclideanDirection_smul_pos (hreg k hk t t.2) (by positivity : 0 < (n + 1 : ℝ)))).symm
  have hsumψ : (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) = Ψ 1 - Ψ 0 := by
    apply finite_unit_slot_angle_increment_sum n ψ Ψ hψ hΨ
    intro k hk t
    apply Circle.ext
    change Complex.exp ((ψ k t : ℂ) * Complex.I) = Complex.exp ((Ψ _ : ℂ) * Complex.I)
    rw [hψlift k hk, hΨlift]
    simp only [Pi.sub_apply, Function.comp_apply]
    rw [(hslots k hk t t.2).1]
  exact hsumψ.trans (horient.trans hsumθ.symm)

end RepulsiveCoulomb
