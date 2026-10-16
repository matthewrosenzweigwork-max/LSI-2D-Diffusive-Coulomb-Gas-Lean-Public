import LeanResearch.RepulsiveCoulomb.PointMetricLineCompactification
import LeanResearch.RepulsiveCoulomb.PlanarPointedLineCompactification
import LeanResearch.RepulsiveCoulomb.PlanarInversionConjugateHomeomorph

/-! Full, parameter-preserving topological straightening of the actual metric
line. This is a construction from the approved compactification and relative
Schoenflies, with the finite inversion pole restored by a proved limit. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- The image of each literal line parameter is that real coordinate. Thus the
two ends, and the orientation of the boundary parameter, are explicitly fixed. -/
theorem exists_pointMetricLine_parameter_straightening_at_pole {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ℓ : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t)
    {p : ℂ} (hp : p ∉ range ℓ) :
    ∃ H : ℂ ≃ₜ ℂ, H p = Complex.I ∧ ∀ t : ℝ, H (ℓ t) = (t : ℂ) := by
  have hℓ := pointMetricLine_isClosedEmbedding ha y ℓ hd
  have hk : IsClosedEmbedding (fun t : ℝ ↦ (t : ℂ)) :=
    Complex.isometry_ofReal.isClosedEmbedding
  have hq : Complex.I ∉ range (fun t : ℝ ↦ (t : ℂ)) := by
    rintro ⟨t, ht⟩
    have hi := congrArg Complex.im ht
    simpa using hi
  obtain ⟨F, hF0, hF⟩ := exists_pointedPlanarLine_extension hℓ hk hp hq
    (pointMetricLine_inverted_jordan ha y ℓ hd hp)
  refine ⟨planarInversionConjugateHomeomorph F hF0 p Complex.I, ?_, ?_⟩
  · simp [planarInversionConjugateHomeomorph_apply, planarInversion, hF0]
  · intro t
    rw [planarInversionConjugateHomeomorph_apply, hF]
    simp [planarInversion]

/-- Unpointed existence chooses an actual complementary point. The preceding
version lets a specified point select the positive halfplane explicitly. -/
theorem exists_pointMetricLine_parameter_straightening {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ℓ : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t) :
    ∃ H : ℂ ≃ₜ ℂ, ∀ t : ℝ, H (ℓ t) = (t : ℂ) := by
  obtain ⟨p, hp⟩ := pointMetricLine_compl_nonempty ha y ℓ hd
  obtain ⟨H, _, hH⟩ := exists_pointMetricLine_parameter_straightening_at_pole ha y ℓ hd hp
  exact ⟨H, hH⟩

/-- Straightening respects the whole boundary carrier, in both directions. -/
theorem line_straightening_mem_iff {ℓ : ℝ → ℂ} (H : ℂ ≃ₜ ℂ)
    (hH : ∀ t : ℝ, H (ℓ t) = (t : ℂ)) (z : ℂ) :
    z ∈ range ℓ ↔ (H z).im = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    rw [hH]
    simp
  · intro hz
    refine ⟨(H z).re, H.injective ?_⟩
    rw [hH]
    apply Complex.ext <;> simp [hz]

theorem line_straightening_image {ℓ : ℝ → ℂ} (H : ℂ ≃ₜ ℂ)
    (hH : ∀ t : ℝ, H (ℓ t) = (t : ℂ)) :
    H '' range ℓ = {z : ℂ | z.im = 0} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (line_straightening_mem_iff H hH w).mp hw
  · intro hz
    refine ⟨H.symm z, ?_, H.apply_symm_apply z⟩
    apply (line_straightening_mem_iff H hH _).mpr
    simpa using hz

end RepulsiveCoulomb
