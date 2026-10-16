module

public import LeanResearch.RepulsiveCoulomb.FiniteLinkEndpointSubdivision
public import LeanResearch.RepulsiveCoulomb.FlatLinkSectorDisk

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Cut actual occupied polar intervals at a chosen
period boundary. Recentring is proved by periodicity of the actual polar map.
A wrapping arc is the union of its two literal cut-open pieces; it is never
replaced by the shorter circular representative. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem sectorPolar_periodic (r : ℝ) :
    Function.Periodic (sectorPolar r) (2 * Real.pi) := by
  intro θ
  apply Complex.ext
  · simp only [sectorPolar_re, Real.cos_add_two_pi]
  · simp only [sectorPolar_im, Real.sin_add_two_pi]

theorem flatLinkOccupiedDisk_sub_periods (ρ lo hi : ℝ) (n : ℤ) :
    flatLinkOccupiedDisk ρ (lo - n • (2 * Real.pi)) (hi - n • (2 * Real.pi)) =
      flatLinkOccupiedDisk ρ lo hi := by
  ext w
  constructor
  · rintro ⟨r, hr, θ, hθ, he⟩
    refine ⟨r, hr, θ + n • (2 * Real.pi), ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, ?_⟩
    exact he.trans (((sectorPolar_periodic r).zsmul n) θ).symm
  · rintro ⟨r, hr, θ, hθ, he⟩
    refine ⟨r, hr, θ - n • (2 * Real.pi), ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, ?_⟩
    exact he.trans ((sectorPolar_periodic r).sub_zsmul_eq n).symm

/-- Move the lower endpoint into one period while keeping the full width. -/
theorem flatLinkOccupiedDisk_rebase (ρ lo width : ℝ)
    (hperiod : 0 < 2 * Real.pi) :
    flatLinkOccupiedDisk ρ lo (lo + width) =
      flatLinkOccupiedDisk ρ (toIcoMod hperiod 0 lo)
        (toIcoMod hperiod 0 lo + width) := by
  rw [toIcoMod]
  convert (flatLinkOccupiedDisk_sub_periods ρ lo (lo + width)
    (toIcoDiv hperiod 0 lo)).symm using 1 <;> congr 1 <;> ring

/-- Exact two-piece split at the cut. Both pieces retain the original radial
coordinate, including the center and the two copies of the cut ray. -/
theorem flatLinkOccupiedDisk_split_at_period {ρ lo width : ℝ}
    (hlo : lo ∈ Ico (0 : ℝ) (2 * Real.pi))
    (hwrap : 2 * Real.pi < lo + width) :
    flatLinkOccupiedDisk ρ lo (lo + width) =
      flatLinkOccupiedDisk ρ lo (2 * Real.pi) ∪
        flatLinkOccupiedDisk ρ 0 (lo + width - 2 * Real.pi) := by
  ext w
  constructor
  · rintro ⟨r, hr, θ, hθ, he⟩
    by_cases hθcut : θ ≤ 2 * Real.pi
    · exact Or.inl ⟨r, hr, θ, ⟨hθ.1, hθcut⟩, he⟩
    · right
      refine ⟨r, hr, θ - 2 * Real.pi,
        ⟨by linarith, by linarith [hθ.2]⟩, ?_⟩
      exact he.trans ((sectorPolar_periodic r).sub_eq θ).symm
  · rintro (⟨r, hr, θ, hθ, he⟩ | ⟨r, hr, θ, hθ, he⟩)
    · exact ⟨r, hr, θ, ⟨hθ.1, hθ.2.trans hwrap.le⟩, he⟩
    · refine ⟨r, hr, θ + 2 * Real.pi,
        ⟨by linarith [hlo.2, hθ.1], by linarith [hθ.2]⟩, ?_⟩
      exact he.trans ((sectorPolar_periodic r) θ).symm

/-- Every actual interval of width at most one period has a one-piece or
two-piece cut-open description, with all new endpoints in [0,2*pi]. -/
theorem flatLinkOccupiedDisk_cut_open {ρ lo width : ℝ}
    (hwidth : 0 ≤ width) (hwidthT : width ≤ 2 * Real.pi) :
    ∃ b : ℝ, b ∈ Ico (0 : ℝ) (2 * Real.pi) ∧
      flatLinkOccupiedDisk ρ lo (lo + width) = flatLinkOccupiedDisk ρ b (b + width) ∧
      ((b + width ≤ 2 * Real.pi) ∨
        (0 < b + width - 2 * Real.pi ∧ b + width - 2 * Real.pi < 2 * Real.pi ∧
          flatLinkOccupiedDisk ρ b (b + width) =
            flatLinkOccupiedDisk ρ b (2 * Real.pi) ∪
              flatLinkOccupiedDisk ρ 0 (b + width - 2 * Real.pi))) := by
  have hperiod : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  let b := toIcoMod hperiod 0 lo
  have hb : b ∈ Ico (0 : ℝ) (2 * Real.pi) := toIcoMod_mem_Ico' hperiod lo
  refine ⟨b, hb, flatLinkOccupiedDisk_rebase ρ lo width hperiod, ?_⟩
  rcases le_or_gt (b + width) (2 * Real.pi) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨sub_pos.mpr h, by linarith [hb.2], flatLinkOccupiedDisk_split_at_period hb h⟩

end RepulsiveCoulomb
