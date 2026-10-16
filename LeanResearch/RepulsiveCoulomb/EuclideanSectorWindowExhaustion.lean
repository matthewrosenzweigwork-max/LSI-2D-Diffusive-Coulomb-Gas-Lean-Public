module

public import LeanResearch.RepulsiveCoulomb.EuclideanInteriorAngularWindow
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! ISOLATED SOURCE-ONLY DRAFT. Explicit nested interior angular windows and
literal completion to the entire closed sector, including both boundary rays.
The approximants preserve radius, which later preserves the actual chart seed.
-/
noncomputable section
open Set Metric Filter Topology
namespace RepulsiveCoulomb

def sectorWindowLower (β : ℝ) (n : ℕ) : ℝ := β / ((n : ℝ) + 3)
def sectorWindowUpper (β : ℝ) (n : ℕ) : ℝ := β - sectorWindowLower β n
def sectorWindow (β : ℝ) (n : ℕ) : Set ℂ :=
  flatInteriorAngularWindow (sectorWindowLower β n) (sectorWindowUpper β n)

theorem sectorWindow_bounds {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    0 < sectorWindowLower β n ∧ sectorWindowLower β n < sectorWindowUpper β n ∧
      sectorWindowUpper β n < β := by
  have hd : 0 < (n : ℝ) + 3 := by positivity
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hl : 0 < sectorWindowLower β n := div_pos hβ hd
  have h2 : 2 * sectorWindowLower β n < β := by
    dsimp [sectorWindowLower]
    have he : 2 * β / ((n : ℝ) + 3) < β := (div_lt_iff₀ hd).mpr (by nlinarith)
    simpa only [mul_div_assoc] using he
  dsimp [sectorWindowUpper]
  exact ⟨hl, by linarith, by linarith⟩

theorem flatInteriorAngularWindow_mem_of_arg {l u : ℝ}
    (hl : 0 < l) (hlu : l < u) (huπ : u ≤ Real.pi)
    {z : ℂ} (hz : Complex.arg z ∈ Icc l u) : z ∈ flatInteriorAngularWindow l u := by
  refine ⟨⟨hl.le.trans hz.1, hz.2⟩, ?_⟩
  change 0 ≤ Real.cos l * z.im - Real.sin l * z.re
  rw [complex_support_side]
  exact mul_nonneg (norm_nonneg _) (Real.sin_nonneg_of_mem_Icc
    ⟨sub_nonneg.mpr hz.1, by linarith [hz.2]⟩)

theorem sectorWindow_mono {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    {i j : ℕ} (hij : i ≤ j) : sectorWindow β i ⊆ sectorWindow β j := by
  have hi := sectorWindow_bounds hβ i
  have hj := sectorWindow_bounds hβ j
  have hl : sectorWindowLower β j ≤ sectorWindowLower β i := by
    apply div_le_div_of_nonneg_left hβ.le (by positivity)
    have h : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have hu : sectorWindowUpper β i ≤ sectorWindowUpper β j := by
    dsimp [sectorWindowUpper]
    linarith
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    exact zero_mem_flatInteriorAngularWindow (hj.1.trans hj.2.1).le
  · have harg := flatInteriorAngularWindow_arg hi.1 hi.2.1 (hi.2.2.le.trans hβπ) hz hz0
    exact flatInteriorAngularWindow_mem_of_arg hj.1 hj.2.1 (hj.2.2.le.trans hβπ)
      ⟨hl.trans harg.1, harg.2.trans hu⟩

theorem sectorWindow_subset {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    sectorWindow β n ⊆ closedEuclideanSector β := by
  intro z hz
  exact ⟨hz.1.1, hz.1.2.trans (sectorWindow_bounds hβ n).2.2.le⟩

theorem mem_iUnion_sectorWindow_of_strict_arg {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    {z : ℂ} (hz : Complex.arg z ∈ Ioo (0 : ℝ) β) : z ∈ ⋃ n, sectorWindow β n := by
  let δ := min (Complex.arg z) (β - Complex.arg z)
  have hδ : 0 < δ := lt_min hz.1 (sub_pos.mpr hz.2)
  obtain ⟨n, hn⟩ := exists_nat_gt (β / δ)
  have hprod : β < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
  have hl : sectorWindowLower β n < δ := by
    apply (div_lt_iff₀ (show 0 < (n : ℝ) + 3 by positivity)).mpr
    nlinarith
  have hbounds := sectorWindow_bounds hβ n
  refine mem_iUnion.mpr ⟨n, flatInteriorAngularWindow_mem_of_arg hbounds.1 hbounds.2.1
    (hbounds.2.2.le.trans hβπ) ?_⟩
  constructor
  · exact hl.le.trans (min_le_left _ _)
  · have hh := hl.trans_le (min_le_right (Complex.arg z) (β - Complex.arg z))
    dsimp [sectorWindowUpper]
    linarith

def sectorWindowApproxAngle (β θ : ℝ) (n : ℕ) : ℝ :=
  sectorWindowLower β n + (1 - 2 / ((n : ℝ) + 3)) * θ

def sectorWindowApprox (β : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  sectorPolar ‖z‖ (sectorWindowApproxAngle β (Complex.arg z) n)

theorem sectorWindowApproxAngle_mem {β θ : ℝ} (hβ : 0 < β) (hθ : θ ∈ Icc (0 : ℝ) β)
    (n : ℕ) : sectorWindowApproxAngle β θ n ∈
      Icc (sectorWindowLower β n) (sectorWindowUpper β n) := by
  have hd : 0 < (n : ℝ) + 3 := by positivity
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hc : 0 ≤ 1 - 2 / ((n : ℝ) + 3) := by
    have h : 2 / ((n : ℝ) + 3) ≤ 1 := (div_le_one hd).mpr (by linarith)
    linarith
  refine ⟨le_add_of_nonneg_right (mul_nonneg hc hθ.1), ?_⟩
  have h := mul_le_mul_of_nonneg_left hθ.2 hc
  have he : sectorWindowLower β n + (1 - 2 / ((n : ℝ) + 3)) * β = sectorWindowUpper β n := by
    dsimp [sectorWindowLower, sectorWindowUpper]
    field_simp [hd.ne']
    ring
  exact (add_le_add (le_refl (sectorWindowLower β n)) h).trans_eq he

theorem sectorWindowApprox_mem {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    {z : ℂ} (hz : z ∈ closedEuclideanSector β) (n : ℕ) :
    sectorWindowApprox β z n ∈ sectorWindow β n := by
  have hn := sectorWindow_bounds hβ n
  by_cases hz0 : z = 0
  · simp only [sectorWindowApprox, hz0, norm_zero, sectorPolar_zero]
    exact zero_mem_flatInteriorAngularWindow (hn.1.trans hn.2.1).le
  · have ht := sectorWindowApproxAngle_mem hβ hz n
    have ht0 : 0 < sectorWindowApproxAngle β (Complex.arg z) n := hn.1.trans_le ht.1
    have htπ : sectorWindowApproxAngle β (Complex.arg z) n ≤ Real.pi :=
      ht.2.trans (hn.2.2.le.trans hβπ)
    apply flatInteriorAngularWindow_mem_of_arg hn.1 hn.2.1 (hn.2.2.le.trans hβπ)
    change Complex.arg (sectorPolar ‖z‖ _) ∈ _
    rw [sectorPolar_arg (norm_pos_iff.mpr hz0) ⟨by linarith [Real.pi_pos], htπ⟩]
    exact ht

theorem sectorWindowApprox_norm (β : ℝ) (z : ℂ) (n : ℕ) :
    ‖sectorWindowApprox β z n‖ = ‖z‖ := sectorPolar_norm (norm_nonneg _) _

theorem sectorWindowApprox_tendsto (β : ℝ) (z : ℂ) :
    Tendsto (sectorWindowApprox β z) atTop (𝓝 z) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 3)⁻¹) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      ((tendsto_add_atTop_iff_nat 3).2 (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hangle : Tendsto (sectorWindowApproxAngle β (Complex.arg z)) atTop (𝓝 (Complex.arg z)) := by
    change Tendsto (fun n : ℕ ↦ β / ((n : ℝ) + 3) +
      (1 - 2 / ((n : ℝ) + 3)) * Complex.arg z) atTop (𝓝 (Complex.arg z))
    have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := (hinv.const_mul β).add ((hconst.sub (hinv.const_mul 2)).mul_const (Complex.arg z))
    simpa only [sectorWindowApproxAngle, sectorWindowLower, div_eq_mul_inv,
      mul_zero, sub_zero, one_mul, zero_add] using h
  have hc : Continuous (fun θ : ℝ ↦ sectorPolar ‖z‖ θ) := by
    unfold sectorPolar conePhase
    fun_prop
  have h := (hc.tendsto (Complex.arg z)).comp hangle
  change Tendsto (fun n : ℕ ↦ sectorPolar ‖z‖
    (sectorWindowApproxAngle β (Complex.arg z) n)) atTop (𝓝 z)
  simpa only [Function.comp_def, sectorWindowApprox, sectorPolar_norm_arg] using h

theorem closure_iUnion_sectorWindow {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) :
    closure (⋃ n, sectorWindow β n) = closedEuclideanSector β := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro z hz
      obtain ⟨n, hn⟩ := mem_iUnion.mp hz
      exact sectorWindow_subset hβ n hn
    · exact closedEuclideanSector_isClosed hβ hβπ
  · intro z hz
    exact mem_closure_of_tendsto (sectorWindowApprox_tendsto β z)
      (Eventually.of_forall fun n ↦ mem_iUnion.mpr ⟨n, sectorWindowApprox_mem hβ hβπ hz n⟩)

end RepulsiveCoulomb
