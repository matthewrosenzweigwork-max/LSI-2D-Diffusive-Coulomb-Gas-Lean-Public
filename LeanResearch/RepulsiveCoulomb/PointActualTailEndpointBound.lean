import LeanResearch.RepulsiveCoulomb.PointActualOutwardTailAngle
import LeanResearch.RepulsiveCoulomb.ContinuousLastLevelCrossing
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic

/-! Uncompiled additive successor. Construct the last circle crossing on an
actual minimizing segment and carry the uniform angular bound to its original
far endpoint. Endpoint tangent differentiability is never assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_pointConformal_actual_tail_endpoint_angle_bound
    {n : ℕ} {a : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin n → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {A k : ℝ} (hA : 0 < A) (hyA : ∀ j, 2 * ‖y j‖ ≤ A)
    (hB : 0 < pointExteriorHalfMass a)
    (hD : pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * A)
    (hk : k ∈ Icc (0 : ℝ) 1) (hanchor : ‖γ k‖ < A) (hend : A < ‖γ 1‖) :
    ∃ s ∈ Ioo k 1, ‖γ s‖ = A ∧ (∀ t ∈ Ioc s 1, A < ‖γ t‖) ∧
      ∃ φ : ℝ → ℝ, Continuous φ ∧
        (∀ t ∈ Icc s 1, Complex.exp ((φ t : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ)) ∧
        ∀ t ∈ Ioo s 1,
          Real.rpow A (1 + pointExteriorHalfMass a) / Real.rpow ‖γ t‖ (1 + pointExteriorHalfMass a) +
            pointExteriorMoment a y / (pointExteriorHalfMass a * ‖γ t‖) ≤ 1 / 2 →
          |φ 1 - φ t| ≤ angularTailPotential A (pointExteriorHalfMass a)
            (pointExteriorMoment a y) ‖γ t‖ := by
  have hk1 : k < 1 := lt_of_le_of_ne hk.2 (by
    intro heq
    rw [heq] at hanchor
    linarith)
  obtain ⟨s, hs, hstart, hout⟩ := exists_last_level_crossing hc.norm hk1 hanchor hend
  have hs0 : 0 < s := hk.1.trans_lt hs.1
  have hz (t : ℝ) (ht : t ∈ Icc s 1) : 0 < ‖γ t‖ := by
    by_cases hts : t = s
    · subst t; rwa [hstart]
    · exact hA.trans (hout t ⟨lt_of_le_of_ne ht.1 (Ne.symm hts), ht.2⟩)
  obtain ⟨φ, hφ, hφlift⟩ := exists_global_argument_lift_on_Icc hc hs.2
    (fun t ht => norm_pos_iff.mp (hz t ht))
  refine ⟨s, hs, hstart, hout, φ, hφ, hφlift, ?_⟩
  intro t ht hsmall
  let G := angularTailPotential A (pointExteriorHalfMass a) (pointExteriorMoment a y) ‖γ t‖
  let T : Set ℝ := {u | |φ u - φ t| ≤ G}
  have hTc : IsClosed T := isClosed_le (hφ.sub continuous_const).abs continuous_const
  have hsub : Ioo t 1 ⊆ T := by
    intro u hu
    have hsu : s < u := ht.1.trans hu.1
    obtain ⟨ψ, hψ, hψlift, hbound⟩ := exists_pointConformal_actual_outward_tail_angle_bound
      ha y γ hc L hL hgeo hA hyA hB hD hs0 hsu hu.2 hstart
      (fun x hx => hout x ⟨hx.1, hx.2.trans hu.2.le⟩)
    have hlocal := hbound t ⟨ht.1.le, hu.1.le⟩ hsmall
    have hφsub : ∀ x ∈ Icc t u,
        Complex.exp ((φ x : ℂ) * Complex.I) = γ x / (‖γ x‖ : ℂ) := by
      intro x hx
      exact hφlift x ⟨ht.1.le.trans hx.1, hx.2.trans hu.2.le⟩
    have hψsub : ∀ x ∈ Icc t u,
        Complex.exp ((ψ x : ℂ) * Complex.I) = γ x / (‖γ x‖ : ℂ) := by
      intro x hx
      exact hψlift x ⟨ht.1.le.trans hx.1, hx.2⟩
    change |φ u - φ t| ≤ G
    rw [interval_argument_increment_eq hu.1.le hφ hψ hφsub hψsub]
    exact hlocal
  have h1 : (1 : ℝ) ∈ closure (Ioo t 1) := by
    rw [closure_Ioo ht.2.ne]
    exact ⟨ht.2.le, le_rfl⟩
  exact (closure_minimal hsub hTc) h1

end RepulsiveCoulomb
