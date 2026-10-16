module

public import LeanResearch.RepulsiveCoulomb.PointActualSectorTopContact

@[expose] public section

/-! ISOLATED SOURCE-ONLY DRAFT. Original-input first-marked sector endpoint.
The only supplied maps are the actual halfplane homeomorphism, finitely many
actual old boundary geodesic pieces, and the original clean minimizing ray.
The sector map, all direction edges, finite beta, chart normalization, complete
embedding, bottom identification and first marked top contact are constructed.

No compiler invocation, kernel acceptance, or canonical staging is claimed.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_point_actual_first_marked_sector
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (HP : ℂ ≃ₜ ℂ) (hP : P = HP ⁻¹' planarClosedUpperHalfplane)
    (hclosed : IsClosed P) (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, ∃ C : PointRetainedConeNeighborhood a y P p, C.Full ∨ C.Admissible)
    (pieces : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (pieces i).curve)
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    (hmarks : (↑(pointSignedMarked ν α) : Set ℂ) ⊆ P)
    (hν : ∀ p ∈ frontier P, ∃ K : PointRetainedConeNeighborhood a y P p,
      ν p = Real.pi - (1 + coalescedPointExponent a y p / 2) * (K.hi - K.lo))
    (hcurv : ∀ p ∈ interior P, coalescedPointExponent a y p ≠ 0 → p ∈ pointSignedMarked ν α)
    (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (hρP : ∀ t, ρ t ∈ P) (hfront : ∀ t, ρ t ∈ frontier P)
    (hclean : Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {ρ 0}) (range ρ))
    (hsupport : ρ 0 ∈ α.support)
    (C : PointRetainedConeNeighborhood a y P (ρ 0)) (hadm : C.Admissible) :
    ∃ D : PointActualSectorData a y ha P,
      D.nu = ν ∧ D.alpha = α ∧ D.ray = ρ ∧
      (∃ hι : Fintype {x : ℂ // x ∈ (pointSignedMarked D.nu D.alpha).erase (D.ray 0)},
        D.beta = @finiteCappedDirectionMinimum _ hι D.direction (min Real.pi (α (ρ 0)))) ∧
      ∃ F : closedEuclideanSector D.beta → P,
        (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
        (∀ x z, (pointRegionIntrinsicEDist ha y P (F x).1 (F z).1).toReal = dist x z) ∧
        (∀ r : NNReal, ∀ hr : (r : ℂ) ∈ closedEuclideanSector D.beta, (F ⟨(r : ℂ), hr⟩).1 = ρ r) ∧
        (∀ z, z.1 ∈ interior (closedEuclideanSector D.beta) →
          (F z).1 ∈ interior P ∧ (F z).1 ∉ pointSignedMarked ν α) ∧
        Topology.IsClosedEmbedding (fun z ↦ (F z).1) ∧ IsProperMap (fun z ↦ (F z).1) ∧
        (∀ γ : ℝ → closedEuclideanSector D.beta, ∀ s t,
          pointConformalMetricLength ha y (fun r ↦ (F (γ r)).1) s t = eVariationOn γ (Icc s t)) ∧
        (D.beta < min Real.pi (α (ρ 0)) →
          ∃ x : ℂ, x ∈ pointSignedMarked ν α ∧ x ≠ ρ 0 ∧
            ∃ L : ℝ, 0 < L ∧ ∃ q : closedEuclideanSector D.beta,
              q.1 = sectorPolar L D.beta ∧ (F q).1 = x ∧
              ∀ t : unitInterval, 0 < t.1 → t.1 < 1 →
                ∀ qt : closedEuclideanSector D.beta, qt.1 = sectorPolar (L * t.1) D.beta →
                  (F qt).1 ∉ pointSignedMarked ν α) := by
  obtain ⟨D, hDν, hDα, hDρ, hminimum, hclosest⟩ :=
    exists_actual_first_sector_data ha y HP hP hclosed hconn hcharts pieces hpieces
      hbudget hmarks hν hcurv ρ hρ hρP hfront hclean hsupport C hadm
  obtain ⟨F, hd, hi, hbottom, hregular, hFclosed, hFproper, hseed, hlength⟩ :=
    D.exists_actual_closed_sector_with_bottom
  refine ⟨D, hDν, hDα, hDρ, ?_, F, hd, hi, ?_, ?_, hFclosed, hFproper, hlength, ?_⟩
  · simpa only [hDα, hDρ] using hminimum
  · intro r hr
    simpa only [hDρ] using hbottom r hr
  · intro z hz
    simpa only [hDν, hDα] using hregular z hz
  · intro hcap
    have hcapD : D.beta < min Real.pi (D.alpha (D.ray 0)) := by
      simpa only [hDα, hDρ] using hcap
    obtain ⟨i, hiβ, _, _, hbefore⟩ := hclosest hcapD
    obtain ⟨L, hL, q, hq, hcontact, hfree⟩ :=
      D.completed_map_first_marked_top F hd hseed hcapD i hiβ hbefore
    have himark : i.1 ∈ pointSignedMarked ν α := by
      simpa only [hDν, hDα] using (Finset.mem_erase.mp i.2).2
    have hine : i.1 ≠ ρ 0 := by
      simpa only [hDρ] using (Finset.mem_erase.mp i.2).1
    refine ⟨i.1, himark, hine, L, hL, q, hq, hcontact, ?_⟩
    intro t ht ht1 qt hqt
    simpa only [hDν, hDα] using hfree t ht ht1 qt hqt

end RepulsiveCoulomb
