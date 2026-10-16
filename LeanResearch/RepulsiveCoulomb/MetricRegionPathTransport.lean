import LeanResearch.RepulsiveCoulomb.MetricRegionPathDistance

/-! Transport of the genuine path infimum under actual metric coordinate maps.
All paths are transported, so these statements do not assume finitely many
chart or seam crossings. -/
noncomputable section
open Set
open scoped ENNReal
namespace RepulsiveCoulomb
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem eVariationOn_map_eq_of_pairwise_edist {A : Type*} [LinearOrder A]
    {P : Set X} (f : X → Y) (hf : ∀ x ∈ P, ∀ z ∈ P, edist (f x) (f z) = edist x z)
    (γ : A → X) (s : Set A) (hγ : MapsTo γ s P) :
    eVariationOn (f ∘ γ) s = eVariationOn γ s := by
  unfold eVariationOn
  apply iSup_congr
  rintro ⟨n, u, hu, hus⟩
  apply Finset.sum_congr rfl
  intro i hi
  exact hf _ (hγ (hus (i + 1))) _ (hγ (hus i))

theorem metricRegionPathEDist_map_le {P : Set X} {Q : Set Y} (f : X → Y)
    (hc : ContinuousOn f P) (hmap : MapsTo f P Q)
    (hmetric : ∀ x ∈ P, ∀ z ∈ P, edist (f x) (f z) = edist x z) (x z : X) :
    metricRegionPathEDist Q (f x) (f z) ≤ metricRegionPathEDist P x z := by
  apply le_iInf
  intro γ
  have hfc : ContinuousOn (f ∘ γ.toFun) (Icc (0 : ℝ) 1) :=
    hc.comp γ.continuous.continuousOn γ.mapsTo
  let η : MetricRegionLengthPath Q (f x) (f z) :=
    MetricRegionLengthPath.ofContinuousOn (f ∘ γ.toFun) hfc
      (by simp only [Function.comp_apply, γ.source])
      (by simp only [Function.comp_apply, γ.target]) (hmap.comp γ.mapsTo)
  calc
    metricRegionPathEDist Q (f x) (f z) ≤ η.length := metricRegionPathEDist_le_length η
    _ = eVariationOn (f ∘ γ.toFun) (Icc (0 : ℝ) 1) :=
      MetricRegionLengthPath.length_ofContinuousOn _ _ _ _ _
    _ = γ.length := eVariationOn_map_eq_of_pairwise_edist f hmetric _ _ γ.mapsTo

theorem metricRegionPathEDist_map_eq {P : Set X} {Q : Set Y} (f : X → Y) (g : Y → X)
    (hfc : ContinuousOn f P) (hgc : ContinuousOn g Q)
    (hfmap : MapsTo f P Q) (hgmap : MapsTo g Q P)
    (hfmetric : ∀ x ∈ P, ∀ z ∈ P, edist (f x) (f z) = edist x z)
    (hgmetric : ∀ x ∈ Q, ∀ z ∈ Q, edist (g x) (g z) = edist x z)
    (hleft : LeftInvOn g f P) {x z : X} (hx : x ∈ P) (hz : z ∈ P) :
    metricRegionPathEDist Q (f x) (f z) = metricRegionPathEDist P x z := by
  apply le_antisymm (metricRegionPathEDist_map_le f hfc hfmap hfmetric x z)
  have h := metricRegionPathEDist_map_le g hgc hgmap hgmetric (f x) (f z)
  rwa [hleft hx, hleft hz] at h

end RepulsiveCoulomb
