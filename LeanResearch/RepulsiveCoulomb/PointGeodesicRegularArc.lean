import LeanResearch.RepulsiveCoulomb.HolomorphicRadialArc
import LeanResearch.RepulsiveCoulomb.ConePowerGeodesicNonnegative

/-! Every short nonconstant geodesic from any point has a regular real-analytic
Euclidean parametrization, including both endpoints. The exact change from metric
time is a positive power, and positive punctures require no separation. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_pointConformal_geodesic_regular_arc_radius {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ R : ℝ, 0 < R ∧
      ∀ z : ℂ, (pointSmoothConformalEDist a y z p).toReal ≤ R → z ≠ p →
        ∀ γ : Icc (0 : ℝ) 1 → ℂ,
          γ ⟨0, by norm_num⟩ = p → γ ⟨1, by norm_num⟩ = z →
          (∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
            |t.1 - s.1| * (pointSmoothConformalEDist a y p z).toReal) →
          ∃ η : ℝ → ℂ,
            AnalyticOnNhd ℝ η (Icc (0 : ℝ) 1) ∧
            InjOn η (Icc (0 : ℝ) 1) ∧
            (∀ s ∈ Icc (0 : ℝ) 1, deriv η s ≠ 0) ∧
            η 0 = p ∧ η 1 = z ∧
            (∀ t : Icc (0 : ℝ) 1,
              γ t = η (t.1 ^ (coalescedPointExponent a y p / 2 + 1)⁻¹)) ∧
            Set.range γ = η '' Icc (0 : ℝ) 1 := by
  obtain ⟨e, R, hR, hep, hinv, he, hsource, hmetric⟩ := exists_pointConformal_regular_power_cone_disk ha y p
  let α := coalescedPointExponent a y p / 2
  have hα : 0 ≤ α := div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ R := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact hR.le
  refine ⟨R, hR, ?_⟩
  intro z hz hzp γ h0 h1 hd
  have hL : (pointSmoothConformalEDist a y p z).toReal = coneRadialPotential α (e z) := by
    rw [hmetric p hpp z hz, hep, standardCone_distance_from_apex_nonneg hα,
      ENNReal.toReal_ofReal (by positivity)]
    simp only [coneRadialPotential, div_eq_mul_inv, mul_comm]
  have hball (t : Icc (0 : ℝ) 1) : (pointSmoothConformalEDist a y (γ t) p).toReal ≤ R := by
    have h := hd t ⟨0, by norm_num⟩
    rw [h0, zero_sub, abs_neg, abs_of_nonneg t.2.1] at h
    rw [h]
    have hbound : (pointSmoothConformalEDist a y p z).toReal ≤ R := by
      rwa [pointSmoothConformalEDist_comm a y p z]
    exact (mul_le_of_le_one_left ENNReal.toReal_nonneg t.2.2).trans hbound
  have hparam (t : Icc (0 : ℝ) 1) : e (γ t) = t.1 ^ (α + 1)⁻¹ • e z := by
    apply standardCone_geodesic_from_apex_nonneg hα (fun s => e (γ s)) (e z)
      (by rw [h0, hep]) (by rw [h1])
    intro s u
    rw [← hmetric (γ s) (hball s) (γ u) (hball u), hd, hL]
  have htarget : ∀ s ∈ Icc (0 : ℝ) 1, s • e z ∈ e.target := by
    intro s hs
    let t : Icc (0 : ℝ) 1 := ⟨s ^ (α + 1), Real.rpow_nonneg hs.1 _,
      Real.rpow_le_one hs.1 hs.2 (by positivity)⟩
    have ht : t.1 ^ (α + 1)⁻¹ = s := by
      dsimp [t]
      rw [← Real.rpow_mul hs.1, mul_inv_cancel₀ (show α + 1 ≠ 0 by linarith), Real.rpow_one]
    rw [← ht, ← hparam t]
    exact e.mapsTo (hsource _ (hball t))
  have hez : e z ≠ 0 := by
    intro h
    apply hzp
    apply e.injOn (hsource _ hz) (hsource _ hpp)
    exact h.trans hep.symm
  obtain ⟨hA, hdη, hinj⟩ := holomorphic_radial_arc_regular e he hinv hez htarget
  let η : ℝ → ℂ := fun s => e.symm (s • e z)
  have hη (t : Icc (0 : ℝ) 1) : γ t = η (t.1 ^ (α + 1)⁻¹) := by
    change γ t = e.symm (t.1 ^ (α + 1)⁻¹ • e z)
    rw [← hparam t, e.left_inv (hsource _ (hball t))]
  refine ⟨η, hA, hinj, hdη, ?_, ?_, hη, ?_⟩
  · change e.symm ((0 : ℝ) • e z) = p
    rw [zero_smul, ← hep, e.left_inv (hsource _ hpp)]
  · change e.symm ((1 : ℝ) • e z) = z
    rw [one_smul, e.left_inv (hsource _ hz)]
  · apply Set.Subset.antisymm
    · rintro q ⟨t, rfl⟩
      exact ⟨t.1 ^ (α + 1)⁻¹,
        ⟨Real.rpow_nonneg t.2.1 _, Real.rpow_le_one t.2.1 t.2.2 (by positivity)⟩,
        (hη t).symm⟩
    · rintro q ⟨s, hs, rfl⟩
      let t : Icc (0 : ℝ) 1 := ⟨s ^ (α + 1), Real.rpow_nonneg hs.1 _,
        Real.rpow_le_one hs.1 hs.2 (by positivity)⟩
      refine ⟨t, ?_⟩
      rw [hη t]
      congr 1
      dsimp [t]
      rw [← Real.rpow_mul hs.1, mul_inv_cancel₀ (show α + 1 ≠ 0 by linarith), Real.rpow_one]

end RepulsiveCoulomb
