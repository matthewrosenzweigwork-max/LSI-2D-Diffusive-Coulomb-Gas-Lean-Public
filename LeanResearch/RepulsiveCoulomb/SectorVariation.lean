module

public import LeanResearch.RepulsiveCoulomb.EuclideanSectorMap

@[expose] public section

/-! Angular contraction bounds for lengths of arbitrary curves, expressed through
metric variation, and exact preservation along boundary rays. -/
noncomputable section
open Set
open scoped ENNReal NNReal
namespace RepulsiveCoulomb

theorem eVariationOn_lower_of_edist_lower {A X Y : Type*} [LinearOrder A]
    [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {f : X → Y} {g : A → X}
    {s : Set A} {t : Set X} {C : ℝ≥0∞}
    (h : ∀ x ∈ t, ∀ y ∈ t, C * edist x y ≤ edist (f x) (f y)) (hg : MapsTo g s t) :
    C * eVariationOn g s ≤ eVariationOn (f ∘ g) s := by
  unfold eVariationOn
  rw [ENNReal.mul_iSup]
  apply iSup_le
  rintro ⟨n, u, hu, hs⟩
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ Finset.range n, edist (f (g (u (i + 1)))) (f (g (u i))) :=
      Finset.sum_le_sum (fun i _ ↦ h _ (hg (hs _)) _ (hg (hs _)))
    _ ≤ _ := le_iSup_of_le ⟨n, u, hu, hs⟩ le_rfl

theorem sectorAngularMap_lipschitzOn {L β : ℝ} (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (hβ : β ≤ Real.pi) : LipschitzOnWith 1 (sectorAngularMap L) (closedEuclideanSector β) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx z hz
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
    (sectorAngularMap_dist_bounds hL0 hL1 hβ hx hz).2

theorem sectorAngularMap_variation_bounds {A : Type*} [LinearOrder A]
    {L β : ℝ} (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hβ : β ≤ Real.pi)
    {γ : A → ℂ} {s : Set A} (hγ : MapsTo γ s (closedEuclideanSector β)) :
    ENNReal.ofReal L * eVariationOn γ s ≤ eVariationOn (sectorAngularMap L ∘ γ) s ∧
      eVariationOn (sectorAngularMap L ∘ γ) s ≤ eVariationOn γ s := by
  constructor
  · apply eVariationOn_lower_of_edist_lower _ hγ
    intro x hx z hz
    have h := ENNReal.ofReal_le_ofReal (sectorAngularMap_dist_bounds hL0 hL1 hβ hx hz).1
    simpa only [edist_dist, dist_eq_norm, ENNReal.ofReal_mul hL0] using h
  · simpa only [ENNReal.coe_one, one_mul] using
      (sectorAngularMap_lipschitzOn hL0 hL1 hβ).comp_eVariationOn_le hγ

theorem sectorPolar_same_ray_dist (r s θ : ℝ) : ‖sectorPolar r θ - sectorPolar s θ‖ = |r - s| := by
  unfold sectorPolar
  rw [← sub_mul, norm_mul, conePhase_norm, mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem sectorAngularMap_polar {L r θ : ℝ} (hr : 0 ≤ r) (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    sectorAngularMap L (sectorPolar r θ) = sectorPolar r (L * θ) := by
  by_cases hr0 : r = 0
  · subst r
    rw [sectorPolar_zero, sectorAngularMap_zero, sectorPolar_zero]
  · rw [sectorAngularMap, sectorPolar_norm hr, sectorPolar_arg (lt_of_le_of_ne hr (Ne.symm hr0)) hθ]

theorem sectorAngularMap_preserves_ray_dist {L r s θ : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    ‖sectorAngularMap L (sectorPolar r θ) - sectorAngularMap L (sectorPolar s θ)‖ =
      ‖sectorPolar r θ - sectorPolar s θ‖ := by
  rw [sectorAngularMap_polar hr hθ, sectorAngularMap_polar hs hθ,
    sectorPolar_same_ray_dist, sectorPolar_same_ray_dist]

end RepulsiveCoulomb
