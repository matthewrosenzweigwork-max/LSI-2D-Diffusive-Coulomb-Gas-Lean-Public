import LeanResearch.RepulsiveCoulomb.PointTranslatedLengthConstruction
import LeanResearch.RepulsiveCoulomb.TranslatedStripSourceGeometry
import LeanResearch.RepulsiveCoulomb.PointUniformStripMarkedAvoidance

/-! SOURCE-ONLY ASSEMBLY. Construct the actual unbounded positive translated
strip from original signed geometry and a genuine locally normalized corner.
The map, uniform width, all finite stages, compatibility, finite-length
attainment, properness, exact old-boundary contact and mark avoidance are
outputs. No development/continuation family is an input.

The two one-dimensional normalization fields in PointTranslatedOriginalData
remain genuine local corner data. Their adapter from arbitrary unoriented
original old germs is not silently asserted here.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb.PointTranslatedOriginalData
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j} {P : Set ℂ}
    (D : PointTranslatedOriginalData a y ha P)

theorem exists_actual_uniform_translated_strip :
    ∃ s : ℝ, ∃ hs : 0 < s, ∃ hsedge : s < D.edgeLength,
      ∃ F : flatShearedStrip (conePhase D.angle) s → P,
        (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
        (∀ r : NNReal, F (translatedStripBottom hs.le r)=D.ray r) ∧
        (∀ u : Icc (0 : ℝ) s,
          F (translatedStripEdge u)=D.edge ⟨u.1,u.2.1,u.2.2.trans hsedge.le⟩) ∧
        (∀ z, (F z).1 ∉ (↑(pointSignedMarked D.nu D.alpha) : Set ℂ) \ {(D.ray 0).1}) ∧
        (∀ r : NNReal, 0<r → ∀ u : Icc (0 : ℝ) s, 0<u.1 →
          (F ⟨flatShearedPoint (conePhase D.angle) r.1 u.1,r.1,r.2,u.1,u.2,rfl⟩).1 ∈ interior P) ∧
        IsClosedEmbedding (fun z ↦ (F z).1) ∧ IsProperMap (fun z ↦ (F z).1) ∧
        range (fun z ↦ (F z).1) ∩ frontier P =
          range (fun r ↦ (D.ray r).1) ∪
          range (fun u : Icc (0 : ℝ) s ↦ (D.edge ⟨u.1,u.2.1,u.2.2.trans hsedge.le⟩).1) := by
  classical
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  obtain ⟨delta,hdelta,hdedge,hclear,s,hs,hsedge,hsdelta,⟨T₀⟩⟩ := D.exists_initial_clear_stage
  let R : ℕ → ℝ := fun n ↦ s+(n:ℝ)+1
  have hsR (n : ℕ) : s≤R n := by
    dsimp [R]
    linarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
  let T : ∀ n : ℕ, D.Stage s hs hsedge (R n) := fun n ↦
    Classical.choice (D.exists_stage_at_length T₀ (hsR n) hsdelta.le hclear)
  let K : ℕ → Set ℂ := fun n ↦ flatShearedRectangle (conePhase D.angle) (R n) s
  let f := fun n ↦ (T n).map
  have hf (n : ℕ) : Isometry (f n) := (T n).metric
  have hcompat : ∀ i j : ℕ, ∀ z (hi : z∈K i) (hj : z∈K j), f i ⟨z,hi⟩=f j ⟨z,hj⟩ := by
    intro i j z hi hj
    rcases le_total (R i) (R j) with hij | hji
    · exact D.stages_agree (T i) (T j) hij hsdelta.le hclear ⟨z,hi⟩
    · exact (D.stages_agree (T j) (T i) hji hsdelta.le hclear ⟨z,hj⟩).symm
  have hdir : Directed (·⊆·) K := by
    intro i j
    refine ⟨max i j,?_,?_⟩ <;> apply flatShearedRectangle_mono _ le_rfl
    · dsimp [R]
      have hij : (i : ℝ) ≤ ((max i j : ℕ) : ℝ) := by exact_mod_cast le_max_left i j
      linarith
    · dsimp [R]
      have hij : (j : ℝ) ≤ ((max i j : ℕ) : ℝ) := by exact_mod_cast le_max_right i j
      linarith
  have hcover : flatShearedStrip (conePhase D.angle) s ⊆ ⋃ n,K n := by
    rintro z ⟨r,hr,u,hu,rfl⟩
    obtain ⟨n,hn⟩ := exists_nat_ge r
    exact mem_iUnion.mpr ⟨n,r,⟨hr,by dsimp [R]; linarith⟩,u,hu,rfl⟩
  have hKstrip (n : ℕ) : K n ⊆ flatShearedStrip (conePhase D.angle) s := by
    rintro z ⟨r,hr,u,hu,rfl⟩
    exact ⟨r,hr.1,u,hu,rfl⟩
  let incl : flatShearedStrip (conePhase D.angle) s → ⋃ n,K n := Set.inclusion hcover
  have hincl : Isometry incl := fun _ _ ↦ rfl
  let F := directedFlatUnion K f hcompat ∘ incl
  have hF : Isometry F := (directedFlatUnion_isometry K f hdir hcompat hf).comp hincl
  have hstage (n : ℕ) (z : K n) : F ⟨z.1,hKstrip n z.2⟩=(T n).map z :=
    directedFlatUnion_of_mem K f hcompat (incl ⟨z.1,hKstrip n z.2⟩) n z.2
  have hFb (r : NNReal) : F (translatedStripBottom hs.le r)=D.ray r := by
    obtain ⟨n,hn⟩ := exists_nat_ge (r:ℝ)
    have hr : (r:ℝ)∈Icc (0:ℝ) (R n) := ⟨r.2,by dsimp [R]; linarith⟩
    exact (hstage n (shearedBottomPoint hs.le ⟨r.1,hr⟩)).trans ((T n).bottom ⟨r.1,hr⟩)
  have hFe (u : Icc (0 : ℝ) s) :
      F (translatedStripEdge u)=D.edge ⟨u.1,u.2.1,u.2.2.trans hsedge.le⟩ :=
    (hstage 0 (shearedCompactEdgePoint (T 0).length_pos.le u)).trans ((T 0).compact_edge u)
  have hinterior (r : NNReal) (hr : 0<r) (u : Icc (0 : ℝ) s) (hu : 0<u.1) :
      (F ⟨flatShearedPoint (conePhase D.angle) r.1 u.1,r.1,r.2,u.1,u.2,rfl⟩).1∈interior P := by
    obtain ⟨n,hn⟩ := exists_nat_ge (r:ℝ)
    have hrR : r.1∈Icc (0:ℝ) (R n) := ⟨r.2,by dsimp [R]; linarith⟩
    let z : K n := ⟨flatShearedPoint (conePhase D.angle) r.1 u.1,r.1,hrR,u.1,u.2,rfl⟩
    rw [hstage n z]
    exact (Stage.positive_flatChart D (T n) hsdelta.le hclear ⟨r.1,hrR⟩ hr u hu).1
  have hunmarked : ∀ z, (F z).1∉(↑(pointSignedMarked D.nu D.alpha):Set ℂ)\{(D.ray 0).1} := by
    apply pointShearedStrip_avoids_marked (conePhase_norm D.angle) hs.le (fun r ↦ (D.ray r).1)
      (fun z hz r ↦ hsdelta.trans (hclear z hz r)) F (fun x z ↦ hF.dist_eq x z)
    intro r hr
    have he : (⟨(r:ℂ),hr⟩ : flatShearedStrip (conePhase D.angle) s)=translatedStripBottom hs.le r := by
      apply Subtype.ext
      simp [translatedStripBottom]
    rw [he,hFb]
  have hvi : (conePhase D.angle).im≠0 := by
    rw [conePhase_im]
    exact (Real.sin_pos_of_pos_of_lt_pi D.angle_pos D.angle_lt_pi).ne'
  obtain ⟨hclosed,hproper⟩ := pointTranslatedStrip_closed_proper ha y hvi F (fun x z ↦ hF.dist_eq x z)
  have hcontact : range (fun z ↦ (F z).1)∩frontier P = range (fun r ↦ (D.ray r).1) ∪
      range (fun u : Icc (0:ℝ) s ↦ (D.edge ⟨u.1,u.2.1,u.2.2.trans hsedge.le⟩).1) := by
    ext p
    constructor
    · rintro ⟨⟨z,rfl⟩,hzfront⟩
      obtain ⟨r,hr,u,hu,hz⟩ := z.2
      by_cases hr0 : r=0
      · right
        refine ⟨⟨u,hu⟩,?_⟩
        have hpoint : z=translatedStripEdge (v:=conePhase D.angle) ⟨u,hu⟩ := by
          apply Subtype.ext
          change z.1 = flatShearedPoint (conePhase D.angle) 0 u
          simpa only [hr0] using hz
        exact (congrArg (fun q : P ↦ q.1) ((congrArg F hpoint).trans (hFe ⟨u,hu⟩))).symm
      · by_cases hu0 : u=0
        · left
          refine ⟨⟨r,hr⟩,?_⟩
          have hpoint : z=translatedStripBottom (v:=conePhase D.angle) hs.le ⟨r,hr⟩ := by
            apply Subtype.ext
            change z.1 = flatShearedPoint (conePhase D.angle) r 0
            simpa only [hu0] using hz
          exact (congrArg (fun q : P ↦ q.1) ((congrArg F hpoint).trans (hFb ⟨r,hr⟩))).symm
        · have hrpos : 0<r := lt_of_le_of_ne hr (Ne.symm hr0)
          have hupos : 0<u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
          have hpoint : z=⟨flatShearedPoint (conePhase D.angle) r u,r,hr,u,hu,rfl⟩ := Subtype.ext hz
          exfalso
          apply hzfront.2
          rw [hpoint]
          exact hinterior ⟨r,hr⟩ hrpos ⟨u,hu⟩ hupos
    · rintro (⟨r,rfl⟩ | ⟨u,rfl⟩)
      · exact ⟨⟨translatedStripBottom hs.le r,congrArg Subtype.val (hFb r)⟩,D.ray_frontier r⟩
      · exact ⟨⟨translatedStripEdge u,congrArg Subtype.val (hFe u)⟩,D.edge_frontier _⟩
  exact ⟨s,hs,hsedge,F,fun x z ↦ hF.dist_eq x z,hFb,hFe,hunmarked,hinterior,hclosed,hproper,hcontact⟩

end RepulsiveCoulomb.PointTranslatedOriginalData
