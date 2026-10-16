import LeanResearch.RepulsiveCoulomb.EuclideanSectorContraction

/-! Actual angular contractions as bijections of closed Euclidean sectors, with
sharp two-sided metric estimates and preserved radial length. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def closedEuclideanSector (β : ℝ) : Set ℂ := {z | 0 ≤ Complex.arg z ∧ Complex.arg z ≤ β}
def sectorAngularMap (L : ℝ) (z : ℂ) : ℂ := sectorPolar ‖z‖ (L * Complex.arg z)

theorem sectorPolar_norm {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖sectorPolar r θ‖ = r := by
  rw [sectorPolar, norm_mul, conePhase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

theorem sectorPolar_arg {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    Complex.arg (sectorPolar r θ) = θ := by
  rw [sectorPolar, Complex.arg_real_mul _ hr, conePhase_arg hθ]

theorem sectorPolar_zero (θ : ℝ) : sectorPolar 0 θ = 0 := by simp [sectorPolar]

theorem sectorPolar_norm_arg (z : ℂ) : sectorPolar ‖z‖ (Complex.arg z) = z :=
  Complex.norm_mul_exp_arg_mul_I z

theorem sectorAngularMap_norm (L : ℝ) (z : ℂ) : ‖sectorAngularMap L z‖ = ‖z‖ :=
  sectorPolar_norm (norm_nonneg _) _

theorem sectorAngularMap_zero (L : ℝ) : sectorAngularMap L 0 = 0 := by
  simp [sectorAngularMap, sectorPolar_zero]

theorem sectorAngularMap_arg {L β : ℝ} (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hβ : β ≤ Real.pi)
    {z : ℂ} (hz : z ∈ closedEuclideanSector β) :
    Complex.arg (sectorAngularMap L z) = L * Complex.arg z := by
  by_cases hz0 : z = 0
  · subst z
    simp [sectorAngularMap_zero]
  · apply sectorPolar_arg (norm_pos_iff.mpr hz0)
    exact ⟨lt_of_lt_of_le (neg_neg_of_pos Real.pi_pos) (mul_nonneg hL0 hz.1),
      (mul_le_of_le_one_left hz.1 hL1).trans (hz.2.trans hβ)⟩

theorem sectorAngularMap_mapsTo {L β : ℝ} (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hβ : β ≤ Real.pi) :
    MapsTo (sectorAngularMap L) (closedEuclideanSector β) (closedEuclideanSector (L * β)) := by
  intro z hz
  change 0 ≤ Complex.arg (sectorAngularMap L z) ∧ Complex.arg (sectorAngularMap L z) ≤ L * β
  rw [sectorAngularMap_arg hL0 hL1 hβ hz]
  exact ⟨mul_nonneg hL0 hz.1, mul_le_mul_of_nonneg_left hz.2 hL0⟩

theorem sectorAngularMap_dist_bounds {L β : ℝ} (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hβ : β ≤ Real.pi)
    {x z : ℂ} (hx : x ∈ closedEuclideanSector β) (hz : z ∈ closedEuclideanSector β) :
    L * ‖x - z‖ ≤ ‖sectorAngularMap L x - sectorAngularMap L z‖ ∧
      ‖sectorAngularMap L x - sectorAngularMap L z‖ ≤ ‖x - z‖ := by
  have ha : |Complex.arg x - Complex.arg z| ≤ Real.pi := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2, hz.1, hz.2]
  have h := sectorPolar_angular_contraction hL0 hL1 (norm_nonneg x) (norm_nonneg z) ha
  rw [sectorPolar_norm_arg, sectorPolar_norm_arg] at h
  exact h

theorem sectorAngularMap_bijOn {L β : ℝ} (hL0 : 0 < L) (hL1 : L ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ Real.pi) :
    Set.BijOn (sectorAngularMap L) (closedEuclideanSector β) (closedEuclideanSector (L * β)) := by
  refine ⟨sectorAngularMap_mapsTo hL0.le hL1 hβ1, ?_, ?_⟩
  · intro x hx z hz he
    have h := (sectorAngularMap_dist_bounds hL0.le hL1 hβ1 hx hz).1
    rw [he, sub_self, norm_zero] at h
    have hn : ‖x - z‖ = 0 := by nlinarith [norm_nonneg (x - z)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  · intro w hw
    by_cases hw0 : w = 0
    · subst w
      exact ⟨0, by simp [closedEuclideanSector, hβ0], sectorAngularMap_zero L⟩
    · let θ := Complex.arg w / L
      have ht0 : 0 ≤ θ := div_nonneg hw.1 hL0.le
      have htβ : θ ≤ β := (div_le_iff₀ hL0).mpr (by simpa [mul_comm] using hw.2)
      have ht : θ ∈ Ioc (-Real.pi) Real.pi :=
        ⟨(neg_neg_of_pos Real.pi_pos).trans_le ht0, htβ.trans hβ1⟩
      refine ⟨sectorPolar ‖w‖ θ, ?_, ?_⟩
      · change 0 ≤ Complex.arg (sectorPolar ‖w‖ θ) ∧ Complex.arg (sectorPolar ‖w‖ θ) ≤ β
        rw [sectorPolar_arg (norm_pos_iff.mpr hw0) ht]
        exact ⟨ht0, htβ⟩
      · rw [sectorAngularMap, sectorPolar_norm (norm_nonneg _), sectorPolar_arg (norm_pos_iff.mpr hw0) ht]
        have he : L * θ = Complex.arg w := by dsimp [θ]; field_simp
        rw [he, sectorPolar_norm_arg]

end RepulsiveCoulomb
