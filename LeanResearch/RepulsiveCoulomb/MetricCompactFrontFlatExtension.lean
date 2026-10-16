module

public import LeanResearch.RepulsiveCoulomb.MetricSupportedFlatPatchedUnion
public import LeanResearch.RepulsiveCoulomb.MetricInteriorSupportedPatchExtension
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

/-! ISOLATED SOURCE-ONLY DRAFT, 2026-10-03.

Extend an actual old convex flat patch along only a compact selected front.
For a sector disk the front is its outer circular arc. This avoids incorrectly
requiring a full Euclidean disk at the singular apex. All patches and their
mutual agreement are constructed from actual whole-ball charts.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- A compact front of a full-dimensional convex old source is thickened by
actual full disk charts. No compatible family, extension map, or prescribed
positive extension radius is an input. The old source need not be compact. -/
theorem exists_compact_front_flat_extension {Y : Type*} [MetricSpace Y]
    {K A : Set ℂ} (hK : Convex ℝ K) (hne : (interior K).Nonempty)
    (hA : IsCompact A) (hAK : A ⊆ K)
    (f : K → Y) (hf : Isometry f)
    (hcharts : ∀ x : A, Nonempty (MetricFlatDiskChart Y (f ⟨x.1, hAK x.2⟩))) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ W : Set ℂ, IsOpen W ∧
      interior K ⊆ W ∧ cthickening ε A ⊆ W ∧
      ∃ G : W → Y,
        (∀ x : K, ∀ hx : x.1 ∈ W, G ⟨x.1, hx⟩ = f x) ∧
        ∀ p, ∃ V : Set W, IsOpen V ∧ p ∈ V ∧
          ∀ x ∈ V, ∀ z ∈ V, dist (G x) (G z) = dist x z := by
  let q : A → K := fun x ↦ ⟨x.1, hAK x.2⟩
  have hpatch (x : A) : ∃ B : ℝ, 0 < B ∧
      ∃ e : supportedFlatPatch univ (q x).1 B ≃ᵢ ball (f (q x)) B,
        ∀ z : K, ∀ hz : z.1 ∈ supportedFlatPatch univ (q x).1 B,
          (e ⟨z.1, hz⟩).1 = f z := by
    obtain ⟨C⟩ := hcharts x
    exact exists_interior_supported_patch_extension hK hne f hf (q x) (by simp) C
  choose R hR e hold using hpatch
  obtain ⟨G, hGagree, hGlocal⟩ := exists_supported_flat_patched_union
    hK hne convex_univ (fun _ _ ↦ mem_univ _) f hf q R hR e hold
  let W := supportedFlatPatchedSet univ q R
  have hW : IsOpen W := by
    change IsOpen (interior K ∪ ⋃ x, supportedFlatPatch univ (q x).1 (R x))
    simp only [supportedFlatPatch, inter_univ]
    exact isOpen_interior.union (isOpen_iUnion fun _ ↦ isOpen_ball)
  have hAW : A ⊆ W := by
    intro x hx
    exact Or.inr (mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hR ⟨x, hx⟩), mem_univ _⟩)
  obtain ⟨ε, hε, hεW⟩ := hA.exists_cthickening_subset_open hW hAW
  exact ⟨ε, hε, W, hW, fun _ hx ↦ Or.inl hx, hεW, G, hGagree, hGlocal⟩

/-- Generic Euclidean radial truncation. The cone S is a literal source set,
not a target map, continuation certificate, or metric conclusion. -/
def flatRadialTruncation (S : Set ℂ) (R : ℝ) : Set ℂ :=
  S ∩ closedBall (0 : ℂ) R

/-- The selected outer arc includes both angular endpoint points. -/
def flatRadialFront (S : Set ℂ) (R : ℝ) : Set ℂ :=
  S ∩ sphere (0 : ℂ) R

theorem flatRadialFront_subset (S : Set ℂ) (R : ℝ) :
    flatRadialFront S R ⊆ flatRadialTruncation S R := by
  intro z hz
  exact ⟨hz.1, sphere_subset_closedBall hz.2⟩

theorem flatRadialTruncation_convex {S : Set ℂ} (hS : Convex ℝ S) (R : ℝ) :
    Convex ℝ (flatRadialTruncation S R) := hS.inter (convex_closedBall _ _)

theorem flatRadialTruncation_mono (S : Set ℂ) {R T : ℝ} (hRT : R ≤ T) :
    flatRadialTruncation S R ⊆ flatRadialTruncation S T := by
  intro z hz
  exact ⟨hz.1, hz.2.trans hRT⟩

theorem flatRadialFront_compact {S : Set ℂ} (hS : IsClosed S) (R : ℝ) :
    IsCompact (flatRadialFront S R) :=
  (isCompact_sphere (0 : ℂ) R).inter_left hS

/-- Every newly added interior point lies within the same radial increment
of the old circular front. The old radial sides and apex require no patches:
only the interior of the enlarged convex source is used before completion. -/
theorem flatRadialTruncation_interior_enlargement
    {S : Set ℂ} (hscale : ∀ z ∈ S, ∀ t : ℝ, 0 ≤ t → t • z ∈ S)
    {R ε h : ℝ} (hR : 0 < R) (hh : 0 ≤ h) (hhε : h ≤ ε) :
    interior (flatRadialTruncation S (R + h)) ⊆
      interior (flatRadialTruncation S R) ∪ cthickening ε (flatRadialFront S R) := by
  intro z hz
  have hzS : z ∈ interior S := interior_mono inter_subset_left hz
  have hzbound : ‖z‖ ≤ R + h := by
    simpa only [mem_closedBall, dist_zero_right] using (interior_subset hz).2
  by_cases hzR : ‖z‖ < R
  · left
    have hsub : interior S ∩ ball (0 : ℂ) R ⊆ flatRadialTruncation S R := by
      intro w hw
      exact ⟨interior_subset hw.1, ball_subset_closedBall hw.2⟩
    apply interior_mono hsub
    rw [(isOpen_interior.inter isOpen_ball).interior_eq]
    exact ⟨hzS, by simpa only [mem_ball, dist_zero_right] using hzR⟩
  · right
    have hRz : R ≤ ‖z‖ := le_of_not_gt hzR
    have hzpos : 0 < ‖z‖ := hR.trans_le hRz
    let c := R / ‖z‖
    have hc : 0 ≤ c := div_nonneg hR.le (norm_nonneg _)
    have hc1 : c ≤ 1 := (div_le_one hzpos).mpr hRz
    let q : ℂ := c • z
    have hqnorm : ‖q‖ = R := by
      rw [show q = c • z from rfl, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      exact div_mul_cancel₀ _ hzpos.ne'
    have hq : q ∈ flatRadialFront S R := by
      refine ⟨hscale z (interior_subset hzS) c hc, ?_⟩
      simpa only [mem_sphere, dist_zero_right] using hqnorm
    have hd : dist z q = ‖z‖ - R := by
      rw [dist_eq_norm, show z - q = (1 - c) • z by simp [q, sub_smul],
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hc1)]
      dsimp [c]
      field_simp [hzpos.ne']
    apply mem_cthickening_of_dist_le z q ε (flatRadialFront S R) hq
    rw [hd]
    linarith

end RepulsiveCoulomb
