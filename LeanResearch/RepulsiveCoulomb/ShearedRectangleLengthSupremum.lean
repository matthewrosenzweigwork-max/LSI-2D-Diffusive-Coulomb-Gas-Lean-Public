import LeanResearch.RepulsiveCoulomb.ShearedRectangleWidthSupremum
import LeanResearch.RepulsiveCoulomb.TranslatedRectangleExchange

/-! SOURCE-ONLY ASSEMBLY. Actual Cauchy completion at a supremum of finite
longitudinal lengths, with transverse width fixed. This low-level gluing lemma
is not an original-input strip existence theorem; the geometric caller below
constructs its stage set and proves compatibility. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem exists_shearedRectangle_length_supremum_isometry
    {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    {v : ℂ} (hv : ‖v‖ = 1) (s : ℝ)
    {W : Set ℝ} (hWne : W.Nonempty) (hWpos : ∀ R ∈ W, 0 < R) (hWbound : BddAbove W)
    (f : ∀ R : W, flatShearedRectangle v R.1 s → Y)
    (hf : ∀ R, Isometry (f R))
    (hcompat : ∀ R T : W, ∀ z (hR : z ∈ flatShearedRectangle v R.1 s)
      (hT : z ∈ flatShearedRectangle v T.1 s), f R ⟨z, hR⟩ = f T ⟨z, hT⟩) :
    ∃ F : flatShearedRectangle v (sSup W) s → Y, Isometry F ∧
      ∀ R (z : flatShearedRectangle v R.1 s),
        F ⟨z.1, flatShearedRectangle_mono (le_csSup hWbound R.2) le_rfl z.2⟩ = f R z := by
  let g : ∀ R : W, flatShearedRectangle v s R.1 → Y :=
    fun R ↦ f R ∘ shearedRectangleExchange hv s R.1
  have hg (R : W) : Isometry (g R) := (hf R).comp (shearedRectangleExchange hv s R.1).isometry
  have hgc : ∀ R T : W, ∀ z (hR : z ∈ flatShearedRectangle v s R.1)
      (hT : z ∈ flatShearedRectangle v s T.1), g R ⟨z, hR⟩ = g T ⟨z, hT⟩ := by
    intro R T z hR hT
    exact hcompat R T (shearedCoordinateExchange v hv z)
      ((shearedRectangleExchange hv s R.1) ⟨z, hR⟩).2
      ((shearedRectangleExchange hv s T.1) ⟨z, hT⟩).2
  obtain ⟨G, hG, hGold⟩ := exists_shearedRectangle_supremum_isometry hv s hWne hWpos hWbound g hg hgc
  let swap := shearedRectangleExchange hv (sSup W) s
  let F := G ∘ swap
  refine ⟨F, hG.comp swap.isometry, ?_⟩
  intro R z
  let w := (shearedRectangleExchange hv R.1 s) z
  have hw : w.1 ∈ flatShearedRectangle v s (sSup W) :=
    flatShearedRectangle_mono le_rfl (le_csSup hWbound R.2) w.2
  have he : swap ⟨z.1, flatShearedRectangle_mono (le_csSup hWbound R.2) le_rfl z.2⟩ =
      ⟨w.1, hw⟩ := Subtype.ext rfl
  change G (swap ⟨z.1, _⟩) = f R z
  rw [he, hGold R w]
  apply congrArg (f R)
  apply Subtype.ext
  exact (shearedCoordinateExchange v hv).symm_apply_apply z.1

end RepulsiveCoulomb
