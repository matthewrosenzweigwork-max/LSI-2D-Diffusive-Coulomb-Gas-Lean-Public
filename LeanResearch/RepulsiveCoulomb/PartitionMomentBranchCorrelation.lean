module

public import LeanResearch.RepulsiveCoulomb.PartitionMomentBranchExpansion
public import LeanResearch.RepulsiveCoulomb.PartitionMomentBranchSupportSum

@[expose] public section

/-! Derived centered finite-product ordered-pair correlation moments.
The proof follows the finite-word expansion, absolute integrability, signed
singleton cancellation, support-count split, and vertex-wise padded Hölder
mechanism of Delgadino--Gvalani Lemma 3.2. No statement from that paper is
postulated. Constants and normalization are explicit. Records-only. -/

noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace RepulsiveCoulomb

variable {X : Type*} [MeasurableSpace X]

/-- Only loop-free words without singleton active labels survive. -/
def partitionMomentSurvivors (N p : ℕ) : Finset (Fin p → Fin N × Fin N) :=
  Finset.univ.filter (fun e => (∀ j, (e j).1 ≠ (e j).2) ∧
    (∀ v, equilibriumDiagramDegree e v ≠ 1))

/-- Exact deletion of the signed singleton diagrams after absolute
integrability has been derived for every loop-free diagram. -/
theorem partitionMoment_sum_words_eq_survivors {N p : ℕ}
    {μ : Measure X} [IsProbabilityMeasure μ]
    (G : X → X → ℝ) (hG : Measurable (Function.uncurry G))
    (hsymm : ∀ x y, G x y = G y x)
    (hcenter : ∀ z, (∫ y, G z y ∂μ) = 0) (hp : 0 < p)
    (Bp : ℝ) (hrowInt : ∀ z, Integrable (fun y => |G z y| ^ p) μ)
    (hrow : ∀ z, (∫ y, |G z y| ^ p ∂μ) ≤ Bp) :
    (∑ e : Fin p → Fin N × Fin N,
      ∫ x, partitionMomentWord G e x ∂Measure.pi (fun _ : Fin N => μ)) =
      ∑ e ∈ partitionMomentSurvivors N p,
        ∫ x, partitionMomentDiagram G e x ∂Measure.pi (fun _ : Fin N => μ) := by
  classical
  calc
    _ = ∑ e ∈ partitionMomentSurvivors N p,
        ∫ x, partitionMomentWord G e x ∂Measure.pi (fun _ : Fin N => μ) := by
      apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro e _ he
      by_cases hloop : ∀ j, (e j).1 ≠ (e j).2
      · have hnot : ¬ ∀ v, equilibriumDiagramDegree e v ≠ 1 := by
          intro hno
          exact he (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hloop, hno⟩)
        push_neg at hnot
        obtain ⟨v, hv⟩ := hnot
        simp only [partitionMomentWord, if_pos hloop]
        exact partitionMomentDiagram_integral_zero_singleton G hG hsymm hcenter e hloop
          hp Bp hrowInt hrow v hv
      · simp only [partitionMomentWord, if_neg hloop, integral_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      have hloop := (Finset.mem_filter.mp he).2.1
      simp only [partitionMomentWord, if_pos hloop]

/-- Generic even-order form. Low active count means v≤p−2m and contributes
Bp/N^(2m). High active count forces every original degree≤4m, after which
successive integrations remove each edge once and contribute Bq^(p/(4m)). -/
theorem partitionMoment_centered_ordered_bound_of_even {N p m : ℕ}
    {μ : Measure X} [IsProbabilityMeasure μ]
    (hN : 2 ≤ N) (hp : 0 < p) (heven : Even p) (hm : 1 ≤ m) (hmp : 2 * m ≤ p)
    (G : X → X → ℝ) (hG : Measurable (Function.uncurry G))
    (hsymm : ∀ x y, G x y = G y x)
    (hrowIntegrable : ∀ z, Integrable (G z) μ)
    (hcenter : ∀ z, (∫ y, G z y ∂μ) = 0)
    (Bp Bq : ℝ) (hBp : 0 ≤ Bp) (hBq : 0 ≤ Bq)
    (hpInt : ∀ z, Integrable (fun y => |G z y| ^ p) μ)
    (hpBound : ∀ z, (∫ y, |G z y| ^ p ∂μ) ≤ Bp)
    (hqInt : ∀ z, Integrable (fun y => |G z y| ^ (4 * m)) μ)
    (hqBound : ∀ z, (∫ y, |G z y| ^ (4 * m) ∂μ) ≤ Bq) :
    Integrable (fun x : Fin N → X => |partitionMomentOrderedStatistic G x| ^ p)
      (Measure.pi (fun _ : Fin N => μ)) ∧
    (∫ x : Fin N → X, |partitionMomentOrderedStatistic G x| ^ p
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
      (p : ℝ) ^ (2 * p + 1) *
        (Bp / (N : ℝ) ^ (2 * m) + Bq ^ ((p : ℝ) / (4 * m : ℝ))) := by
  refine ⟨partitionMomentOrderedStatistic_moment_integrable G hG hsymm hp heven
    Bp hpInt hpBound, ?_⟩
  have hq : 0 < 4 * m := by omega
  let s := partitionMomentSurvivors N p
  let a := fun e : Fin p → Fin N × Fin N =>
    ∫ x, partitionMomentDiagram G e x ∂Measure.pi (fun _ : Fin N => μ)
  have hs (e : Fin p → Fin N × Fin N) (he : e ∈ s) :
      (∀ j, (e j).1 ≠ (e j).2) ∧ (∀ v, equilibriumDiagramDegree e v ≠ 1) :=
    (Finset.mem_filter.mp he).2
  have hmin (e : Fin p → Fin N × Fin N) (he : e ∈ s) :
      ∀ v ∈ equilibriumDiagramActive e, 2 ≤ equilibriumDiagramDegree e v :=
    equilibriumDiagram_min_degree_of_no_singleton e (hs e he).2
  have hsupp : ∀ e ∈ s, 1 ≤ (equilibriumDiagramActive e).card ∧
      (equilibriumDiagramActive e).card ≤ p := by
    intro e he
    exact ⟨partitionMoment_active_card_pos hp e,
      equilibriumDiagram_active_card_le e (hmin e he)⟩
  have hlo : ∀ e ∈ s, (equilibriumDiagramActive e).card ≤ p - 2 * m → a e ≤ Bp := by
    intro e he _
    have h := partitionMomentDiagram_integral_abs_le G hG hsymm e (hs e he).1
      hp (equilibriumDiagram_degree_le_order e (hs e he).1) Bp hBp hpInt hpBound
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
    rw [div_self hp0, Real.rpow_one] at h
    exact (le_abs_self _).trans (abs_integral_le_integral_abs.trans h)
  have hhi : ∀ e ∈ s, p - 2 * m < (equilibriumDiagramActive e).card →
      a e ≤ Bq ^ ((p : ℝ) / (4 * m : ℝ)) := by
    intro e he hcount
    have hdegree : ∀ v, equilibriumDiagramDegree e v ≤ 4 * m :=
      equilibriumDiagram_high_count_degree_le e (hmin e he) (by omega)
    have h := partitionMomentDiagram_integral_abs_le G hG hsymm e (hs e he).1
      hq hdegree Bq hBq hqInt hqBound
    have h' : (∫ x, |partitionMomentDiagram G e x|
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ Bq ^ ((p : ℝ) / (4 * m : ℝ)) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
    exact (le_abs_self _).trans (abs_integral_le_integral_abs.trans h')
  have hsum := partitionMoment_support_sum_le (r := 2 * m) (by omega : 1 ≤ N)
    s hsupp a Bp (Bq ^ ((p : ℝ) / (4 * m : ℝ))) hBp (Real.rpow_nonneg hBq _) hlo hhi
  rw [partitionMomentOrderedStatistic_moment_eq_sum G hG hsymm hp heven Bp hpInt hpBound,
    partitionMoment_sum_words_eq_survivors G hG hsymm hcenter hp Bp hpInt hpBound]
  calc
    (1 / (N : ℝ)) ^ p * (∑ e ∈ s, a e) ≤
        (1 / (N : ℝ)) ^ p * ((p : ℝ) ^ (2 * p + 1) *
          ((N : ℝ) ^ (p - 2 * m) * Bp +
            (N : ℝ) ^ p * Bq ^ ((p : ℝ) / (4 * m : ℝ)))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := partitionMoment_normalize_support_bound (by omega : 0 < N) hmp _ _

/-- The requested p=2*k*m, q=4*m centered ordered-pair moment theorem, valid
for every N≥2 under the actual product probability measure. -/
theorem partitionMoment_centered_ordered_bound {N k m : ℕ}
    {μ : Measure X} [IsProbabilityMeasure μ]
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (G : X → X → ℝ) (hG : Measurable (Function.uncurry G))
    (hsymm : ∀ x y, G x y = G y x)
    (hrowIntegrable : ∀ z, Integrable (G z) μ)
    (hcenter : ∀ z, (∫ y, G z y ∂μ) = 0)
    (Bp Bq : ℝ) (hBp : 0 ≤ Bp) (hBq : 0 ≤ Bq)
    (hpInt : ∀ z, Integrable (fun y => |G z y| ^ (2 * k * m)) μ)
    (hpBound : ∀ z, (∫ y, |G z y| ^ (2 * k * m) ∂μ) ≤ Bp)
    (hqInt : ∀ z, Integrable (fun y => |G z y| ^ (4 * m)) μ)
    (hqBound : ∀ z, (∫ y, |G z y| ^ (4 * m) ∂μ) ≤ Bq) :
    Integrable (fun x : Fin N → X => |partitionMomentOrderedStatistic G x| ^ (2 * k * m))
      (Measure.pi (fun _ : Fin N => μ)) ∧
    (∫ x : Fin N → X, |partitionMomentOrderedStatistic G x| ^ (2 * k * m)
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
      (2 * k * m : ℝ) ^ (2 * (2 * k * m) + 1) *
        (Bp / (N : ℝ) ^ (2 * m) + Bq ^ ((2 * k * m : ℝ) / (4 * m : ℝ))) := by
  have hkpos : 0 < k := by omega
  have hmpos : 0 < m := by omega
  have hp : 0 < 2 * k * m := mul_pos (mul_pos (by decide) hkpos) hmpos
  have hev : Even (2 * k * m) := ⟨k * m, by ring⟩
  have hmp : 2 * m ≤ 2 * k * m := by
    have h := Nat.mul_le_mul_right m (Nat.mul_le_mul_left 2 (by omega : 1 ≤ k))
    simpa only [mul_one] using h
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    partitionMoment_centered_ordered_bound_of_even hN hp hev hm hmp G hG hsymm
      hrowIntegrable hcenter Bp Bq hBp hBq hpInt hpBound hqInt hqBound

/-- Paper-compatible weakening of the first N power, preserving the same
explicit constant and all continuous-product hypotheses. -/
theorem partitionMoment_weaken_particle_power {N m p : ℕ}
    (hN : 1 ≤ N) (Bp Bq I : ℝ) (hBp : 0 ≤ Bp)
    (h : I ≤ (p : ℝ) ^ (2 * p + 1) *
      (Bp / (N : ℝ) ^ (2 * m) + Bq)) :
    I ≤ (p : ℝ) ^ (2 * p + 1) *
      (Bp / (N : ℝ) ^ (2 * m - 1) + Bq) := by
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add _ le_rfl
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (2 * m - 1) ≤ (N : ℝ) ^ (2 * m) :=
    pow_le_pow_right₀ hNr (Nat.sub_le _ _)
  exact div_le_div_of_nonneg_left hBp
    (pow_pos (lt_of_lt_of_le zero_lt_one hNr) _) hpow

end RepulsiveCoulomb
