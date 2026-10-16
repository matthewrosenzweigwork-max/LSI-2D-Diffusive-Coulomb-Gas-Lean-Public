module

public import LeanResearch.RepulsiveCoulomb.TranslatedStripSourceGeometry
public import LeanResearch.RepulsiveCoulomb.ShearedRectangleWidthSupremum

@[expose] public section

/-! SOURCE-ONLY MAXIMAL-WIDTH HELPER. Actual Cauchy completion on an
UNBOUNDED strip at a finite width supremum. All source closure and all-pairs
limit assertions are proved; no attained limiting map is an input. This helper
alone does not construct the regular stage set or prove maximal contact.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem flatShearedStrip_mono {v : ℂ} {s t : ℝ} (hst:s≤t) :
    flatShearedStrip v s⊆flatShearedStrip v t := by
  rintro z ⟨r,hr,u,hu,rfl⟩
  exact ⟨r,hr,u,⟨hu.1,hu.2.trans hst⟩,rfl⟩

theorem closure_iUnion_shearedStrips {v : ℂ} (hv:‖v‖=1) (hvi:v.im≠0)
    {W : Set ℝ} (hWne:W.Nonempty) (hWpos:∀s∈W,0<s) (hWbound:BddAbove W) :
    closure (⋃ s:W,flatShearedStrip v s.1)=flatShearedStrip v (sSup W) := by
  apply Subset.antisymm
  · apply closure_minimal _ (flatShearedStrip_isClosed hvi)
    intro z hz
    obtain ⟨s,hs⟩:=mem_iUnion.mp hz
    exact flatShearedStrip_mono (le_csSup hWbound s.2) hs
  · rintro z ⟨r,hr,u,hu,hz⟩
    obtain ⟨n,hn⟩:=exists_nat_ge r
    have hrect:z∈flatShearedRectangle v n (sSup W):=⟨r,⟨hr,hn⟩,u,hu,hz⟩
    rw [← closure_iUnion_shearedRectangles hv n hWne hWpos hWbound] at hrect
    apply closure_mono _ hrect
    intro w hw
    obtain ⟨s,hs⟩:=mem_iUnion.mp hw
    obtain ⟨r,hr,u,hu,hwu⟩:=hs
    exact mem_iUnion.mpr ⟨s,r,hr.1,u,hu,hwu⟩

theorem exists_shearedStrip_width_supremum_isometry
    {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    {v : ℂ} (hv:‖v‖=1) (hvi:v.im≠0)
    {W : Set ℝ} (hWne:W.Nonempty) (hWpos:∀s∈W,0<s) (hWbound:BddAbove W)
    (f:∀s:W,flatShearedStrip v s.1→Y) (hf:∀s,Isometry (f s))
    (hcompat:∀s t:W,∀z (hs:z∈flatShearedStrip v s.1) (ht:z∈flatShearedStrip v t.1),
      f s ⟨z,hs⟩=f t ⟨z,ht⟩) :
    ∃F:flatShearedStrip v (sSup W)→Y,Isometry F ∧
      ∀s (z:flatShearedStrip v s.1),
        F ⟨z.1,flatShearedStrip_mono (le_csSup hWbound s.2) z.2⟩=f s z := by
  let U:=fun s:W↦flatShearedStrip v s.1
  have hdir:Directed (·⊆·) U:=by
    intro s t
    rcases le_total s.1 t.1 with hst|hts
    · exact ⟨t,flatShearedStrip_mono hst,subset_rfl⟩
    · exact ⟨s,subset_rfl,flatShearedStrip_mono hts⟩
  have hclosure:=closure_iUnion_shearedStrips hv hvi hWne hWpos hWbound
  let incl:flatShearedStrip v (sSup W)→closure (⋃s,U s):=fun z↦⟨z.1,hclosure.symm ▸ z.2⟩
  have hincl:Isometry incl:=fun _ _↦rfl
  let F:=directedFlatClosure U f hcompat∘incl
  refine ⟨F,(directedFlatClosure_isometry U f hdir hcompat hf).comp hincl,?_⟩
  intro s z
  exact directedFlatClosure_apply U f hdir hcompat hf s z

end RepulsiveCoulomb
