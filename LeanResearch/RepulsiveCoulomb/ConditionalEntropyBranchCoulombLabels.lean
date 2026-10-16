module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchCoulombCore
public import LeanResearch.RepulsiveCoulomb.CoulombPermutationCore

@[expose] public section

/-!
Actual all-label conditional charts and integrated core KL upper bound.
The outside coordinates are explicitly a permutation of the complement of the
selected label. No symmetry of the observable or competitor is assumed.
The final gradient is the full original real Euclidean physical gradient.
Records-only draft, not staged or checked.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

def conditionalEntropyBranchCoulombChart {N : ℕ} (i : Fin (N + 1)) :
    CoulombConfig (N + 1) ≃ᵐ CoulombConfig N × ℂ :=
  (coulombPermute (Equiv.swap 0 i)).toMeasurableEquiv.trans (coulombFrozenFirst N)

theorem conditionalEntropyBranchCoulombChart_site {N : ℕ} (i : Fin (N + 1))
    (z : CoulombConfig (N + 1)) : (conditionalEntropyBranchCoulombChart i z).2 = z i := by
  change coulombPermute (Equiv.swap 0 i) z 0 = z i
  rw [coulombPermute_apply, Equiv.swap_apply_left]

theorem conditionalEntropyBranchCoulombChart_outside {N : ℕ} (i : Fin (N + 1))
    (z : CoulombConfig (N + 1)) (j : Fin N) :
    (conditionalEntropyBranchCoulombChart i z).1 j = z (Equiv.swap 0 i j.succ) := rfl

theorem conditionalEntropyBranchCoulombChart_outside_ne {N : ℕ}
    (i : Fin (N + 1)) (j : Fin N) : Equiv.swap 0 i j.succ ≠ i := by
  intro h
  have he : Equiv.swap 0 i j.succ = Equiv.swap 0 i 0 := by
    simpa only [Equiv.swap_apply_left] using h
  exact Fin.succ_ne_zero j ((Equiv.swap 0 i).injective he)

/-- This is the actual Gibbs disintegration in the selected-label chart. -/
theorem conditionalEntropyBranch_coulomb_chart_law {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (i : Fin (N + 1)) :
    (coulombMeasure (N + 1) β).map (conditionalEntropyBranchCoulombChart i) =
      coulombOneSiteMarginal N β ⊗ₘ coulombOneSiteKernel N β hβ := by
  change (coulombMeasure (N + 1) β).map
    ((coulombFrozenFirst N) ∘ (coulombPermute (Equiv.swap 0 i))) = _
  rw [← Measure.map_map (coulombFrozenFirst N).measurable
      (coulombPermute (Equiv.swap 0 i)).continuous.measurable,
    (coulombPermute_gibbs_preserving hβ.le (Equiv.swap 0 i)).map_eq,
    coulomb_one_site_joint_law hβ]

def conditionalEntropyBranchCoulombSiteCost {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (Q : Measure (CoulombConfig (N + 1))) (i : Fin (N + 1)) : ℝ≥0∞ :=
  klDiv (Q.map (conditionalEntropyBranchCoulombChart i))
    ((Q.map (conditionalEntropyBranchCoulombChart i)).fst ⊗ₘ coulombOneSiteKernel N β hβ)

theorem conditionalEntropyBranch_coulomb_core_site_cost {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤) (i : Fin (N + 1)) :
    conditionalEntropyBranchCoulombSiteCost hβ (conditionalEntropyBranchCoulombCoreLaw β φ) i =
      conditionalEntropyBranchCoulombFirstCost hβ (coulombPermuteCore (Equiv.swap 0 i) φ) := by
  let σ := Equiv.swap (0 : Fin (N + 1)) i
  have hpres : (coulombMeasure (N + 1) β).map
      (coulombPermute σ).toMeasurableEquiv = coulombMeasure (N + 1) β :=
    (coulombPermute_gibbs_preserving hβ.le σ).map_eq
  have hmap : (conditionalEntropyBranchCoulombCoreLaw β φ).map
      (coulombPermute σ).toMeasurableEquiv =
        conditionalEntropyBranchCoulombCoreLaw β (coulombPermuteCore σ φ) := by
    rw [conditionalEntropyBranchCoulombCoreLaw,
      conditionalEntropyBranch_densityLaw_map _ _ (φ.continuous.measurable.pow_const 2),
      hpres]
    unfold conditionalEntropyBranchCoulombCoreLaw
    congr 1
    funext z
    change φ ((coulombPermute σ).symm z) ^ 2 = φ (coulombPermute σ z) ^ 2
    congr 2
    ext j
    simp only [coulombPermute_symm_apply, coulombPermute_apply, σ, Equiv.symm_swap]
  have hjoint : (conditionalEntropyBranchCoulombCoreLaw β φ).map
      (conditionalEntropyBranchCoulombChart i) =
      (conditionalEntropyBranchCoulombCoreLaw β (coulombPermuteCore σ φ)).map (coulombFrozenFirst N) := by
    change (conditionalEntropyBranchCoulombCoreLaw β φ).map
      ((coulombFrozenFirst N) ∘ (coulombPermute σ).toMeasurableEquiv) = _
    rw [← Measure.map_map (coulombFrozenFirst N).measurable
      (coulombPermute σ).toMeasurableEquiv.measurable, hmap]
  unfold conditionalEntropyBranchCoulombSiteCost conditionalEntropyBranchCoulombFirstCost
  rw [hjoint]

theorem conditionalEntropyBranch_coulomb_all_sites_core_upper_of_first {β : ℝ}
    (hβ : 0 < β) (K : ℝ)
    (hFirst : ∀ (N : ℕ) (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤),
      (∫ z, φ z ^ 2 ∂coulombMeasure (N + 1) β) = 1 →
      conditionalEntropyBranchCoulombFirstCost hβ φ ≠ ∞ ∧
        (conditionalEntropyBranchCoulombFirstCost hβ φ).toReal ≤
          K * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z 0‖ ^ 2
            ∂coulombMeasure (N + 1) β)) :
    ∀ (N : ℕ) (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤),
      (∫ z, φ z ^ 2 ∂coulombMeasure (N + 1) β) = 1 → ∀ i : Fin (N + 1),
      conditionalEntropyBranchCoulombSiteCost hβ (conditionalEntropyBranchCoulombCoreLaw β φ) i ≠ ∞ ∧
        (conditionalEntropyBranchCoulombSiteCost hβ
          (conditionalEntropyBranchCoulombCoreLaw β φ) i).toReal ≤
          K * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z i‖ ^ 2
            ∂coulombMeasure (N + 1) β) := by
  intro N φ hmass i
  let σ := Equiv.swap (0 : Fin (N + 1)) i
  have hm := coulombPermute_gibbs_preserving hβ.le σ
  have hmass' : (∫ z, coulombPermuteCore σ φ z ^ 2 ∂coulombMeasure (N + 1) β) = 1 := by
    exact (hm.integral_comp (coulombPermute σ).toMeasurableEquiv.measurableEmbedding
      (fun z => φ z ^ 2)).trans hmass
  have h := hFirst N (coulombPermuteCore σ φ) hmass'
  have hEnergy : (∫ z, ‖gradient (coulombPermuteCore σ φ : CoulombConfig (N + 1) → ℝ) z 0‖ ^ 2
      ∂coulombMeasure (N + 1) β) =
      ∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z i‖ ^ 2 ∂coulombMeasure (N + 1) β := by
    simp only [coulombPermuteCore_gradient_component, σ, Equiv.symm_swap, Equiv.swap_apply_left]
    exact hm.integral_comp (coulombPermute σ).toMeasurableEquiv.measurableEmbedding
      (fun z => ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z i‖ ^ 2)
  rw [hEnergy] at h
  simpa only [conditionalEntropyBranch_coulomb_core_site_cost, σ] using h

theorem conditionalEntropyBranch_coulomb_all_sites_core_upper {β : ℝ} (hβ : 0 < β) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ)
      (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤),
      (∫ z, φ z ^ 2 ∂coulombMeasure (N + 1) β) = 1 → ∀ i : Fin (N + 1),
      conditionalEntropyBranchCoulombSiteCost hβ (conditionalEntropyBranchCoulombCoreLaw β φ) i ≠ ∞ ∧
        (conditionalEntropyBranchCoulombSiteCost hβ
          (conditionalEntropyBranchCoulombCoreLaw β φ) i).toReal ≤
          K * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z i‖ ^ 2
            ∂coulombMeasure (N + 1) β) := by
  obtain ⟨K, hK, hFirst⟩ := conditionalEntropyBranch_coulomb_first_core_upper hβ
  exact ⟨K, hK, conditionalEntropyBranch_coulomb_all_sites_core_upper_of_first hβ K hFirst⟩

/-- Actual summed conditional-KL upper bound, with the full physical energy
and with no permutation symmetry restriction on phi. -/
theorem conditionalEntropyBranch_coulomb_sum_core_upper_of_sites {β : ℝ}
    (hβ : 0 < β) (K : ℝ)
    (hSites : ∀ (N : ℕ) (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤),
      (∫ z, φ z ^ 2 ∂coulombMeasure (N + 1) β) = 1 → ∀ i : Fin (N + 1),
      conditionalEntropyBranchCoulombSiteCost hβ (conditionalEntropyBranchCoulombCoreLaw β φ) i ≠ ∞ ∧
        (conditionalEntropyBranchCoulombSiteCost hβ
          (conditionalEntropyBranchCoulombCoreLaw β φ) i).toReal ≤
          K * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z i‖ ^ 2
            ∂coulombMeasure (N + 1) β)) :
    ∀ (N : ℕ) (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤),
      (∫ z, φ z ^ 2 ∂coulombMeasure (N + 1) β) = 1 →
      (∀ i : Fin (N + 1), conditionalEntropyBranchCoulombSiteCost hβ
        (conditionalEntropyBranchCoulombCoreLaw β φ) i ≠ ∞) ∧
      (∑ i : Fin (N + 1), (conditionalEntropyBranchCoulombSiteCost hβ
        (conditionalEntropyBranchCoulombCoreLaw β φ) i).toReal) ≤
        K * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z‖ ^ 2
          ∂coulombMeasure (N + 1) β) := by
  intro N φ hmass
  letI := coulombMeasure_isProbability (N := N + 1) hβ
  refine ⟨fun i => (hSites N φ hmass i).1, ?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => (hSites N φ hmass i).2)
  rw [← Finset.mul_sum] at hsum
  have hg : MemLp (fun z => gradient (φ : CoulombConfig (N + 1) → ℝ) z) 2
      (coulombMeasure (N + 1) β) :=
    (TauCeti.continuous_gradient_testFunction φ).memLp_of_hasCompactSupport
      (TauCeti.hasCompactSupport_gradient_testFunction φ)
  have hGi (i : Fin (N + 1)) :
      Integrable (fun z => ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z i‖ ^ 2)
        (coulombMeasure (N + 1) β) :=
    (hg.continuousLinearMap_comp (coulombCoordinate i)).norm.integrable_sq
  have he : (∑ i : Fin (N + 1), ∫ z,
      ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z i‖ ^ 2 ∂coulombMeasure (N + 1) β) =
      ∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z‖ ^ 2 ∂coulombMeasure (N + 1) β := by
    rw [← integral_finsetSum Finset.univ (fun i _ => hGi i)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => (EuclideanSpace.norm_sq_eq _).symm)
  rwa [he] at hsum

theorem conditionalEntropyBranch_coulomb_sum_core_upper {β : ℝ} (hβ : 0 < β) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ)
      (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤),
      (∫ z, φ z ^ 2 ∂coulombMeasure (N + 1) β) = 1 →
      (∀ i : Fin (N + 1), conditionalEntropyBranchCoulombSiteCost hβ
        (conditionalEntropyBranchCoulombCoreLaw β φ) i ≠ ∞) ∧
      (∑ i : Fin (N + 1), (conditionalEntropyBranchCoulombSiteCost hβ
        (conditionalEntropyBranchCoulombCoreLaw β φ) i).toReal) ≤
        K * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z‖ ^ 2
          ∂coulombMeasure (N + 1) β) := by
  obtain ⟨K, hK, hSites⟩ := conditionalEntropyBranch_coulomb_all_sites_core_upper hβ
  exact ⟨K, hK, conditionalEntropyBranch_coulomb_sum_core_upper_of_sites hβ K hSites⟩

end RepulsiveCoulomb
