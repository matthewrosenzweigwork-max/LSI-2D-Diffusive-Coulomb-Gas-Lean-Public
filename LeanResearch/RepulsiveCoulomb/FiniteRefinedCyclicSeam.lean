import LeanResearch.RepulsiveCoulomb.FiniteRefinedNodeCorrespondence
import LeanResearch.RepulsiveCoulomb.PointIncidentSeamOrigin

/-! SOURCE-ONLY, UNCOMPILED. Exact closed-period polar identification and its
transport under a pair of ordered refined node systems. The cyclic seam is
included explicitly; it is not silently treated as equality of real angles. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- The half-open period (0,2*pi] has no repeated positive-radius polar ray. -/
theorem sectorPolar_injOn_positive_period {r : ℝ} (hr : 0 < r) :
    InjOn (sectorPolar r) (Ioc (0 : ℝ) (2 * Real.pi)) := by
  intro θ hθ φ hφ he
  have hrot := congrArg (fun z : ℂ ↦ conePhase (-Real.pi) * z) he
  rw [conePhase_mul_sectorPolar, conePhase_mul_sectorPolar] at hrot
  have hθarg : -Real.pi + θ ∈ Ioc (-Real.pi) Real.pi :=
    ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hφarg : -Real.pi + φ ∈ Ioc (-Real.pi) Real.pi :=
    ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  have ha := congrArg Complex.arg hrot
  rw [sectorPolar_arg hr hθarg, sectorPolar_arg hr hφarg] at ha
  linarith

/-- On the closed period the only extra identification is 0 with 2*pi. -/
theorem sectorPolar_eq_iff_closed_period {r θ φ : ℝ} (hr : 0 < r)
    (hθ : θ ∈ Icc (0 : ℝ) (2 * Real.pi))
    (hφ : φ ∈ Icc (0 : ℝ) (2 * Real.pi)) :
    sectorPolar r θ = sectorPolar r φ ↔
      θ = φ ∨ (θ = 0 ∧ φ = 2 * Real.pi) ∨ (θ = 2 * Real.pi ∧ φ = 0) := by
  have hT : (2 * Real.pi) ∈ Ioc (0 : ℝ) (2 * Real.pi) :=
    ⟨by positivity, le_rfl⟩
  have hperiod : sectorPolar r (2 * Real.pi) = sectorPolar r 0 := by
    simpa only [zero_add] using (sectorPolar_periodic r) 0
  constructor
  · intro he
    by_cases hθ0 : θ = 0
    · by_cases hφ0 : φ = 0
      · exact Or.inl (hθ0.trans hφ0.symm)
      · have hφpos : 0 < φ := lt_of_le_of_ne hφ.1 (Ne.symm hφ0)
        have hφT : φ = 2 * Real.pi := sectorPolar_injOn_positive_period hr
          ⟨hφpos, hφ.2⟩ hT (by rw [hperiod, ← hθ0]; exact he.symm)
        exact Or.inr (Or.inl ⟨hθ0, hφT⟩)
    · have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
      by_cases hφ0 : φ = 0
      · have hθT : θ = 2 * Real.pi := sectorPolar_injOn_positive_period hr
          ⟨hθpos, hθ.2⟩ hT (by rw [hperiod, ← hφ0]; exact he)
        exact Or.inr (Or.inr ⟨hθT, hφ0⟩)
      · have hφpos : 0 < φ := lt_of_le_of_ne hφ.1 (Ne.symm hφ0)
        exact Or.inl (sectorPolar_injOn_positive_period hr
          ⟨hθpos, hθ.2⟩ ⟨hφpos, hφ.2⟩ he)
  · rintro (he | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [he]
    · exact hperiod.symm
    · exact hperiod

namespace FiniteRefinedNodeSystem
variable {N : ℕ} {count : Fin N → ℕ}

/-- Positive-radius ray equality is transported, including both copies of
the cyclic origin. Its converse follows by exchanging the two systems. -/
theorem polar_eq_transfer (P Q : FiniteRefinedNodeSystem count)
    (hP0 : P.coarse 0 = 0) (hPT : P.coarse (Fin.last N) = 2 * Real.pi)
    (hQ0 : Q.coarse 0 = 0) (hQT : Q.coarse (Fin.last N) = 2 * Real.pi)
    {r : ℝ} (hr : 0 < r) {j l : Fin N}
    {i : Fin (count j + 1)} {t : Fin (count l + 1)}
    (he : sectorPolar r (P.node j i) = sectorPolar r (P.node l t)) :
    sectorPolar r (Q.node j i) = sectorPolar r (Q.node l t) := by
  have hPmem (a : Fin N) (b : Fin (count a + 1)) :
      P.node a b ∈ Icc (0 : ℝ) (2 * Real.pi) := by
    simpa only [hP0, hPT] using P.node_mem_global a b
  have hQmem (a : Fin N) (b : Fin (count a + 1)) :
      Q.node a b ∈ Icc (0 : ℝ) (2 * Real.pi) := by
    simpa only [hQ0, hQT] using Q.node_mem_global a b
  apply (sectorPolar_eq_iff_closed_period hr (hQmem j i) (hQmem l t)).mpr
  rcases (sectorPolar_eq_iff_closed_period hr (hPmem j i) (hPmem l t)).mp he with
    heq | ⟨hfirst, hlast⟩ | ⟨hlast, hfirst⟩
  · exact Or.inl (P.node_eq_transfer Q heq)
  · right; left
    constructor
    · simpa only [hQ0] using P.node_eq_first_transfer Q (by simpa only [hP0] using hfirst)
    · simpa only [hQT] using P.node_eq_last_transfer Q (by simpa only [hPT] using hlast)
  · right; right
    constructor
    · simpa only [hQT] using P.node_eq_last_transfer Q (by simpa only [hPT] using hlast)
    · simpa only [hQ0] using P.node_eq_first_transfer Q (by simpa only [hP0] using hfirst)

/-- The correspondence preserves full nonnegative boundary points, not only
unit rays. Equality of radii is forced by norms, and the center is separate. -/
theorem polar_eq_iff (P Q : FiniteRefinedNodeSystem count)
    (hP0 : P.coarse 0 = 0) (hPT : P.coarse (Fin.last N) = 2 * Real.pi)
    (hQ0 : Q.coarse 0 = 0) (hQT : Q.coarse (Fin.last N) = 2 * Real.pi)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (j l : Fin N) (i : Fin (count j + 1)) (t : Fin (count l + 1)) :
    sectorPolar r (P.node j i) = sectorPolar s (P.node l t) ↔
      sectorPolar r (Q.node j i) = sectorPolar s (Q.node l t) := by
  have transfer (A B : FiniteRefinedNodeSystem count)
      (hA0 : A.coarse 0 = 0) (hAT : A.coarse (Fin.last N) = 2 * Real.pi)
      (hB0 : B.coarse 0 = 0) (hBT : B.coarse (Fin.last N) = 2 * Real.pi)
      (he : sectorPolar r (A.node j i) = sectorPolar s (A.node l t)) :
      sectorPolar r (B.node j i) = sectorPolar s (B.node l t) := by
    have hrs : r = s := by
      have hn := congrArg norm he
      simpa only [sectorPolar_norm hr, sectorPolar_norm hs] using hn
    subst s
    rcases eq_or_lt_of_le hr with hr0 | hrpos
    · rw [← hr0, sectorPolar_zero, sectorPolar_zero]
    · exact A.polar_eq_transfer B hA0 hAT hB0 hBT hrpos he
  exact ⟨transfer P Q hP0 hPT hQ0 hQT, transfer Q P hQ0 hQT hP0 hPT⟩

end FiniteRefinedNodeSystem
end RepulsiveCoulomb
