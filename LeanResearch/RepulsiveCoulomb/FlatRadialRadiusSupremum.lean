import LeanResearch.RepulsiveCoulomb.MetricCompactFrontFlatExtension
import LeanResearch.RepulsiveCoulomb.DirectedFlatIsometryUnion

/-! ISOLATED SOURCE-ONLY DRAFT. Actual Cauchy completion of already verified
compatible bounded-radius stages. This is only the limiting-map helper; stage
existence and compatibility are NOT asserted by this module. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem closure_iUnion_flatRadialTruncations
    {S : Set ℂ} (hS : IsClosed S)
    (hscale : ∀ z ∈ S, ∀ t : ℝ, 0 ≤ t → t • z ∈ S)
    {W : Set ℝ} (hWne : W.Nonempty) (hWpos : ∀ s ∈ W, 0 < s) (hWbound : BddAbove W) :
    closure (⋃ s : W, flatRadialTruncation S s.1) =
      flatRadialTruncation S (sSup W) := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro z hz
      obtain ⟨s, hs⟩ := mem_iUnion.mp hz
      exact flatRadialTruncation_mono S (le_csSup hWbound s.2) hs
    · exact hS.inter isClosed_closedBall
  · intro z hz
    have hzbound : ‖z‖ ≤ sSup W := by
      simpa only [mem_closedBall, dist_zero_right] using hz.2
    by_cases hz0 : z = 0
    · obtain ⟨s, hs⟩ := hWne
      apply subset_closure
      refine mem_iUnion.mpr ⟨⟨s, hs⟩, hz.1, ?_⟩
      simpa only [hz0, mem_closedBall, dist_self] using (hWpos s hs).le
    · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      obtain ⟨s, hs, hzs⟩ := exists_lt_of_lt_csSup hWne
        ((sub_lt_self ‖z‖ hε).trans_le hzbound)
      let r := min ‖z‖ s
      have hr0 : 0 ≤ r := le_min (norm_nonneg _) (hWpos s hs).le
      have hrs : r ≤ s := min_le_right _ _
      have hrz : r ≤ ‖z‖ := min_le_left _ _
      have hzr : ‖z‖ - ε < r := lt_min (sub_lt_self ‖z‖ hε) hzs
      let c := r / ‖z‖
      let q : ℂ := c • z
      have hc : 0 ≤ c := div_nonneg hr0 (norm_nonneg _)
      have hc1 : c ≤ 1 := (div_le_one hzpos).mpr hrz
      have hqnorm : ‖q‖ = r := by
        rw [show q = c • z from rfl, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
        exact div_mul_cancel₀ _ hzpos.ne'
      have hd : dist z q = ‖z‖ - r := by
        rw [dist_eq_norm, show z - q = (1 - c) • z by simp [q, sub_smul],
          norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hc1)]
        dsimp [c]
        field_simp [hzpos.ne']
      refine ⟨q, mem_iUnion.mpr ⟨⟨s, hs⟩, hscale z hz.1 c hc, ?_⟩, ?_⟩
      · simpa only [mem_closedBall, dist_zero_right, hqnorm] using hrs
      · rw [hd]
        linarith

/-- The map at the supremum radius is constructed by complete-target Cauchy
extension and agrees with each actual finite stage, on all its boundary. -/
theorem exists_flatRadialTruncation_supremum_isometry
    {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    {S : Set ℂ} (hS : IsClosed S)
    (hscale : ∀ z ∈ S, ∀ t : ℝ, 0 ≤ t → t • z ∈ S)
    {W : Set ℝ} (hWne : W.Nonempty) (hWpos : ∀ s ∈ W, 0 < s) (hWbound : BddAbove W)
    (f : ∀ s : W, flatRadialTruncation S s.1 → Y)
    (hf : ∀ s, Isometry (f s))
    (hcompat : ∀ s t : W, ∀ z (hs : z ∈ flatRadialTruncation S s.1)
      (ht : z ∈ flatRadialTruncation S t.1), f s ⟨z, hs⟩ = f t ⟨z, ht⟩) :
    ∃ F : flatRadialTruncation S (sSup W) → Y, Isometry F ∧
      ∀ s (z : flatRadialTruncation S s.1),
        F ⟨z.1, flatRadialTruncation_mono S (le_csSup hWbound s.2) z.2⟩ = f s z := by
  let U : W → Set ℂ := fun s ↦ flatRadialTruncation S s.1
  have hdir : Directed (· ⊆ ·) U := by
    intro s t
    rcases le_total s.1 t.1 with hst | hts
    · exact ⟨t, flatRadialTruncation_mono S hst, subset_rfl⟩
    · exact ⟨s, subset_rfl, flatRadialTruncation_mono S hts⟩
  have hclosure := closure_iUnion_flatRadialTruncations hS hscale hWne hWpos hWbound
  let incl : flatRadialTruncation S (sSup W) → closure (⋃ s, U s) :=
    fun z ↦ ⟨z.1, hclosure.symm ▸ z.2⟩
  have hinc : Isometry incl := fun _ _ ↦ rfl
  let F := directedFlatClosure U f hcompat ∘ incl
  refine ⟨F, (directedFlatClosure_isometry U f hdir hcompat hf).comp hinc, ?_⟩
  intro s z
  exact directedFlatClosure_apply U f hdir hcompat hf s z

end RepulsiveCoulomb
