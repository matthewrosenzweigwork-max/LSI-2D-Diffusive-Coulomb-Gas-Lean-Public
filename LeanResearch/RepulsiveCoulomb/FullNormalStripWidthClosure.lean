import LeanResearch.RepulsiveCoulomb.FullNormalStripSourceGeometry
import LeanResearch.RepulsiveCoulomb.ShearedRectangleWidthSupremum

/-! Source-only, uncompiled. Literal completion of all widths below a finite
positive h, using actual Cauchy completion rather than a maximum certificate. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem flatFullNormalStrip_mono {s t : ℝ} (hst : s ≤ t) :
    flatFullNormalStrip s ⊆ flatFullNormalStrip t :=
  fun _ hz ↦ ⟨hz.1, hz.2.trans hst⟩

theorem closure_iUnion_fullNormalStrips {h : ℝ} (hh : 0 < h) :
    closure (⋃ s : Ioo (0 : ℝ) h, flatFullNormalStrip s.1) = flatFullNormalStrip h := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro z hz
      obtain ⟨s, hs⟩ := mem_iUnion.mp hz
      exact flatFullNormalStrip_mono s.2.2.le hs
    · exact flatFullNormalStrip_isClosed h
  · intro z hz
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let b := max 0 (z.im - ε)
    have hb0 : 0 ≤ b := le_max_left _ _
    have hbh : b < h := max_lt hh (by linarith [hz.2])
    let s := (b + h) / 2
    have hs0 : 0 < s := by dsimp [s]; linarith
    have hsh : s < h := by dsimp [s]; linarith
    have hbs : b < s := by dsimp [s]; linarith
    let w := min z.im s
    have hw0 : 0 ≤ w := le_min hz.1 hs0.le
    have hws : w ≤ s := min_le_right _ _
    have hwz : w ≤ z.im := min_le_left _ _
    have hwclose : z.im - ε < w := lt_min (by linarith)
      ((le_max_right 0 (z.im - ε)).trans_lt hbs)
    refine ⟨flatShearedPoint Complex.I z.re w, mem_iUnion.mpr ⟨⟨s, hs0, hsh⟩, ?_⟩, ?_⟩
    · simpa [flatFullNormalStrip, flatShearedPoint] using And.intro hw0 hws
    · have he : z = flatShearedPoint Complex.I z.re z.im := by
        apply Complex.ext <;> simp [flatShearedPoint]
      calc
        dist z (flatShearedPoint Complex.I z.re w) =
            dist (flatShearedPoint Complex.I z.re z.im)
              (flatShearedPoint Complex.I z.re w) :=
          congrArg (fun q : ℂ => dist q (flatShearedPoint Complex.I z.re w)) he
        _ = |z.im - w| := flatShearedPoint_dist_transverse (by simp) z.re z.im w
        _ < ε := by
          rw [abs_of_nonneg (sub_nonneg.mpr hwz)]
          linarith

theorem exists_fullNormalStrip_width_limit {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    {h : ℝ} (hh : 0 < h)
    (f : ∀ s : Ioo (0 : ℝ) h, flatFullNormalStrip s.1 → Y)
    (hf : ∀ s, Isometry (f s))
    (hcompat : ∀ s t z (hs : z ∈ flatFullNormalStrip s.1)
      (ht : z ∈ flatFullNormalStrip t.1), f s ⟨z, hs⟩ = f t ⟨z, ht⟩) :
    ∃ F : flatFullNormalStrip h → Y, Isometry F ∧
      ∀ s (z : flatFullNormalStrip s.1),
        F ⟨z.1, flatFullNormalStrip_mono s.2.2.le z.2⟩ = f s z := by
  let U : Ioo (0 : ℝ) h → Set ℂ := fun s ↦ flatFullNormalStrip s.1
  have hdir : Directed (· ⊆ ·) U := by
    intro s t
    rcases le_total s.1 t.1 with hst | hts
    · exact ⟨t, flatFullNormalStrip_mono hst, subset_rfl⟩
    · exact ⟨s, subset_rfl, flatFullNormalStrip_mono hts⟩
  have hclosure := closure_iUnion_fullNormalStrips hh
  let incl : flatFullNormalStrip h → closure (⋃ s, U s) :=
    fun z ↦ ⟨z.1, hclosure.symm ▸ z.2⟩
  have hinc : Isometry incl := fun _ _ ↦ rfl
  let F := directedFlatClosure U f hcompat ∘ incl
  refine ⟨F, (directedFlatClosure_isometry U f hdir hcompat hf).comp hinc, ?_⟩
  intro s z
  exact directedFlatClosure_apply U f hdir hcompat hf s z

end RepulsiveCoulomb
