import LeanResearch.RepulsiveCoulomb.PointGeodesicSmoothArc

/-! One common holomorphic chart for all short incident geodesic collars.
The global smooth representatives agree on neighborhoods of the whole closed
interval with the explicit analytic inverse-chart radial arcs. Thus actual
endpoint derivatives, orientation, and turn transport are retained for gluing. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_pointConformal_smooth_radial_germ_chart {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ R : ℝ, 0 < R ∧ e p = 0 ∧
      AnalyticOnNhd ℂ e.symm e.target ∧
      (∀ z ∈ e.source, AnalyticAt ℂ e z ∧ deriv e z ≠ 0) ∧
      (∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ R → z ∈ e.source) ∧
      (∀ u, (pointSmoothConformalEDist a y u p).toReal ≤ R →
        ∀ v, (pointSmoothConformalEDist a y v p).toReal ≤ R →
          pointSmoothConformalEDist a y u v =
            pointSmoothConformalEDist (standardConeExponents (coalescedPointExponent a y p / 2))
              standardConeLocations (e u) (e v)) ∧
      ∀ z : ℂ, (pointSmoothConformalEDist a y z p).toReal ≤ R → z ≠ p →
        ∀ γ : Icc (0 : ℝ) 1 → ℂ,
          γ ⟨0, by norm_num⟩ = p → γ ⟨1, by norm_num⟩ = z →
          (∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
            |t.1 - s.1| * (pointSmoothConformalEDist a y p z).toReal) →
          ∃ η : ℝ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞)) η ∧
            InjOn η (Icc (0 : ℝ) 1) ∧
            (∀ s ∈ Icc (0 : ℝ) 1, deriv η s ≠ 0) ∧
            η 0 = p ∧ η 1 = z ∧
            (∀ s ∈ Icc (0 : ℝ) 1, η =ᶠ[𝓝 s] (fun u : ℝ => e.symm (u • e z))) ∧
            (∀ t : Icc (0 : ℝ) 1,
              γ t = η (t.1 ^ (coalescedPointExponent a y p / 2 + 1)⁻¹)) ∧
            range γ = η '' Icc (0 : ℝ) 1 := by
  obtain ⟨e, R, hR, hep, hinv, he, hsource, hmetric⟩ :=
    exists_pointConformal_regular_power_cone_disk ha y p
  let α := coalescedPointExponent a y p / 2
  have hα : 0 ≤ α := div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ R := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact hR.le
  refine ⟨e, R, hR, hep, hinv, he, hsource, hmetric, ?_⟩
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
    exact hzp (e.injOn (hsource _ hz) (hsource _ hpp) (h.trans hep.symm))
  obtain ⟨hA, hreg, hinj⟩ := holomorphic_radial_arc_regular e he hinv hez htarget
  let η₀ : ℝ → ℂ := fun s => e.symm (s • e z)
  have hη₀ (t : Icc (0 : ℝ) 1) : γ t = η₀ (t.1 ^ (α + 1)⁻¹) := by
    change γ t = e.symm (t.1 ^ (α + 1)⁻¹ • e z)
    rw [← hparam t, e.left_inv (hsource _ (hball t))]
  have himage : range γ = η₀ '' Icc (0 : ℝ) 1 := by
    apply Subset.antisymm
    · rintro q ⟨t, rfl⟩
      exact ⟨t.1 ^ (α + 1)⁻¹,
        ⟨Real.rpow_nonneg t.2.1 _, Real.rpow_le_one t.2.1 t.2.2 (by positivity)⟩, (hη₀ t).symm⟩
    · rintro q ⟨s, hs, rfl⟩
      let t : Icc (0 : ℝ) 1 := ⟨s ^ (α + 1), Real.rpow_nonneg hs.1 _,
        Real.rpow_le_one hs.1 hs.2 (by positivity)⟩
      refine ⟨t, ?_⟩
      rw [hη₀ t]
      congr 1
      dsimp [t]
      rw [← Real.rpow_mul hs.1, mul_inv_cancel₀ (show α + 1 ≠ 0 by linarith), Real.rpow_one]
  obtain ⟨η, hη, hagree⟩ := analytic_unitInterval_global_smooth_extension η₀ hA
  have heq : EqOn η η₀ (Icc (0 : ℝ) 1) := fun s hs => (hagree s hs).self_of_nhds
  refine ⟨η, hη, ?_, ?_, ?_, ?_, hagree, ?_, ?_⟩
  · intro s hs t ht hst
    exact hinj hs ht ((heq hs).symm.trans (hst.trans (heq ht)))
  · intro s hs
    rw [(hagree s hs).deriv_eq]
    exact hreg s hs
  · rw [heq (by norm_num)]
    change e.symm ((0 : ℝ) • e z) = p
    rw [zero_smul, ← hep, e.left_inv (hsource _ hpp)]
  · rw [heq (by norm_num)]
    change e.symm ((1 : ℝ) • e z) = z
    rw [one_smul, e.left_inv (hsource _ hz)]
  · intro t
    rw [heq ⟨Real.rpow_nonneg t.2.1 _, Real.rpow_le_one t.2.1 t.2.2
      (inv_nonneg.mpr (by
        have hc := coalescedPointExponent_nonneg a y p
        positivity))⟩]
    exact hη₀ t
  · exact himage.trans heq.image_eq.symm

end RepulsiveCoulomb
