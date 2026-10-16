module

public import LeanResearch.RepulsiveCoulomb.CoulombRelativeFactorization
public import Mathlib.Probability.Kernel.MeasurableLIntegral

@[expose] public section

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace RepulsiveCoulomb

def coulombRelativeFrozenFirst (N : ℕ) :
    CoulombConfig (N + 2) ≃ᵐ (ℂ × CoulombConfig N) × ℂ :=
  (coulombRelativeCoordinates N).trans
    (((MeasurableEquiv.refl ℂ).prodCongr
      (MeasurableEquiv.prodComm : ℂ × CoulombConfig N ≃ᵐ CoulombConfig N × ℂ)).trans
        (MeasurableEquiv.prodAssoc : (ℂ × CoulombConfig N) × ℂ ≃ᵐ ℂ × (CoulombConfig N × ℂ)).symm)

theorem coulombRelativeFrozenFirst_insert {N : ℕ} (c u : ℂ) (y : CoulombConfig N) :
    coulombRelativeFrozenFirst N (coulombRelativeInsert c u y) = ((c, y), u) := by
  change (((coulombRelativeCoordinates N (coulombRelativeInsert c u y)).1,
    (coulombRelativeCoordinates N (coulombRelativeInsert c u y)).2.2),
    (coulombRelativeCoordinates N (coulombRelativeInsert c u y)).2.1) = _
  rw [coulombRelativeCoordinates_insert]

theorem coulombRelativeFrozenFirst_symm_apply {N : ℕ} (p : ℂ × CoulombConfig N) (u : ℂ) :
    (coulombRelativeFrozenFirst N).symm (p, u) = coulombRelativeInsert p.1 u p.2 := by
  apply (coulombRelativeFrozenFirst N).injective
  rw [MeasurableEquiv.apply_symm_apply, coulombRelativeFrozenFirst_insert]

theorem coulombRelativeFrozenFirst_measurePreserving (N : ℕ) :
    MeasurePreserving (coulombRelativeFrozenFirst N)
      (volume : Measure (CoulombConfig (N + 2))) volume := by
  have hs : MeasurePreserving (Prod.swap : ℂ × CoulombConfig N → CoulombConfig N × ℂ)
      volume volume := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure ℂ)) (ν := (volume : Measure (CoulombConfig N))))
  have ha : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (ℂ × CoulombConfig N) × ℂ ≃ᵐ ℂ × (CoulombConfig N × ℂ))
      volume volume := volume_preserving_prodAssoc
  exact ha.symm.comp (((MeasurePreserving.id (volume : Measure ℂ)).prod hs).comp
    (coulombRelativeCoordinates_measurePreserving N))

def coulombRelativeRootConfig {N : ℕ} (p : ℂ × CoulombConfig N) : CoulombConfig (N + N + 1) :=
  WithLp.toLp 2 (coulombRelativeRoots p.1 p.2)

theorem coulombRelativeRootConfig_continuous (N : ℕ) :
    Continuous (coulombRelativeRootConfig (N := N)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  refine Fin.cases ?_ (fun l => ?_) k
  · exact continuous_const
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) l
    · simp only [coulombRelativeRoots_left]
      change Continuous (fun p : ℂ × CoulombConfig N => Real.sqrt 2 • p.2 j - p.1)
      exact (((coulombCoordinate j).continuous.comp continuous_snd).const_smul (Real.sqrt 2)).sub continuous_fst
    · simp only [coulombRelativeRoots_right]
      change Continuous (fun p : ℂ × CoulombConfig N => -(Real.sqrt 2 • p.2 j - p.1))
      exact ((((coulombCoordinate j).continuous.comp continuous_snd).const_smul (Real.sqrt 2)).sub continuous_fst).neg

def coulombRelativeExponents (N : ℕ) (β : ℝ) : Fin (N + N + 1) → ℝ :=
  fun _ => β / ((N + 2 : ℕ) : ℝ)

theorem coulombRelativeExponents_nonneg (N : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    ∀ j, 0 ≤ coulombRelativeExponents N β j := fun _ => div_nonneg hβ (Nat.cast_nonneg _)

def coulombRelativeKernel (N : ℕ) (β : ℝ) (hβ : 0 < β) : Kernel (ℂ × CoulombConfig N) ℂ where
  toFun := (fun q : CoulombConfig (N + N + 1) =>
    pointMeasure β (coulombRelativeExponents N β) (fun j => q j)) ∘ coulombRelativeRootConfig (N := N)
  measurable' := by
    have h : Measurable (fun q : CoulombConfig (N + N + 1) =>
        pointMeasure β (coulombRelativeExponents N β) (fun j => q j)) :=
      pointMeasure_measurable_config β (coulombRelativeExponents_nonneg N hβ.le)
    exact h.comp (coulombRelativeRootConfig_continuous N).measurable

theorem coulombRelativeKernel_apply (N : ℕ) (β : ℝ) (hβ : 0 < β) (p : ℂ × CoulombConfig N) :
    coulombRelativeKernel N β hβ p =
      pointMeasure β (coulombRelativeExponents N β) (coulombRelativeRoots p.1 p.2) := by
  change pointMeasure β (coulombRelativeExponents N β) (fun j => coulombRelativeRootConfig p j) = _
  apply congrArg (pointMeasure β (coulombRelativeExponents N β))
  rfl

instance coulombRelativeKernel_isMarkov (N : ℕ) (β : ℝ) (hβ : 0 < β) :
    IsMarkovKernel (coulombRelativeKernel N β hβ) where
  isProbabilityMeasure p := by
    rw [coulombRelativeKernel_apply]
    exact pointMeasure_isProbability hβ
      (coulombRelativeExponents_nonneg N hβ.le) (coulombRelativeRoots p.1 p.2)

end RepulsiveCoulomb

