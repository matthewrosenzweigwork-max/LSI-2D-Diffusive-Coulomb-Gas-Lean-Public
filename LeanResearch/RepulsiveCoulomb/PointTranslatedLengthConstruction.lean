module

public import LeanResearch.RepulsiveCoulomb.PointTranslatedOriginalData
public import LeanResearch.RepulsiveCoulomb.ShearedRectangleLengthSupremum

@[expose] public section

/-! SOURCE-ONLY ASSEMBLY. Construct the nonempty stage set from the actual
corner chart, derive compatibility and every advancing-front chart from the
original signed geometry, complete at the length supremum, and contradict a
finite stopping length by the constructed longitudinal extension. No family,
continuation, stage-regularity or attainment premise occurs in the endpoint.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb.PointTranslatedOriginalData
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j} {P : Set ℂ}
    (D : PointTranslatedOriginalData a y ha P)

theorem exists_initial_clear_stage :
    ∃ delta : ℝ, 0 < delta ∧ delta < D.edgeLength ∧
      (∀ z ∈ (↑(pointSignedMarked D.nu D.alpha) : Set ℂ) \ {(D.ray 0).1}, ∀ r : NNReal,
        delta < (pointSmoothConformalEDist a y z (D.ray r).1).toReal) ∧
      ∃ s : ℝ, ∃ hs : 0 < s, ∃ hsedge : s < D.edgeLength,
        s < delta ∧ Nonempty (D.Stage s hs hsedge s) := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  obtain ⟨delta,hdelta,hdedge,hdgerm,hclear⟩ :=
    pointMetricRay_exists_uniform_marked_clearance ha y (fun t ↦ (D.ray t).1)
      (fun r t ↦ D.ray_metric.dist_eq r t) (pointSignedMarked D.nu D.alpha).finite_toSet
      D.ray_clean D.edgeLength_pos D.germRadius_pos
  obtain ⟨s,hs,hsdelta,F,hdF,hseed⟩ :=
    point_exists_translated_corner_seed ha y D.corner D.angle_lt_pi hdelta
  have hsedge : s < D.edgeLength := hsdelta.trans hdedge
  have hsgerm : s < D.germRadius := hsdelta.trans hdgerm
  have hf : @Isometry _ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace F :=
    @Isometry.of_dist_eq _ P _ (pointRegionMetricSpace ha y P).toPseudoMetricSpace F hdF
  have hb (r : Icc (0 : ℝ) s) : F (shearedBottomPoint hs.le r) = D.ray ⟨r.1,r.2.1⟩ := by
    apply Subtype.ext
    rw [hseed]
    change D.corner.flatInverse (flatShearedPoint (conePhase D.angle) r.1 0) = _
    rw [flatShearedPoint_zero]
    exact D.lower_trace ⟨r.1,r.2.1⟩ (r.2.2.trans hsgerm.le)
  have he (u : Icc (0 : ℝ) s) : F (shearedCompactEdgePoint hs.le u) =
      D.edge ⟨u.1,u.2.1,u.2.2.trans hsedge.le⟩ := by
    apply Subtype.ext
    rw [hseed]
    exact D.upper_trace ⟨u.1,u.2.1,u.2.2.trans hsedge.le⟩ (u.2.2.trans hsgerm.le)
  exact ⟨delta,hdelta,hdedge,hclear,s,hs,hsedge,hsdelta,⟨⟨hs,F,hf,hb,he⟩⟩⟩

theorem Stage.exists_longer {s delta R limit : ℝ} {hs : 0 < s} {hsedge : s < D.edgeLength}
    (T : D.Stage s hs hsedge R) (hRlimit : R < limit) (hsdelta : s ≤ delta)
    (hclear : ∀ z ∈ (↑(pointSignedMarked D.nu D.alpha) : Set ℂ) \ {(D.ray 0).1}, ∀ r : NNReal,
      delta < (pointSmoothConformalEDist a y z (D.ray r).1).toReal) :
    ∃ h : ℝ, 0 < h ∧ R+h < limit ∧ Nonempty (D.Stage s hs hsedge (R+h)) := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  obtain ⟨C⟩ := pointCleanRay_exists_actual_retained_halfDisk ha y D.boundary_atom
    D.ray D.ray_metric D.ray_frontier D.ray_clean (⟨R,T.length_pos.le⟩ : NNReal) T.length_pos
  have hfront (u : Icc (0 : ℝ) s) (hu : 0<u.1) :
      Nonempty (MetricFlatDiskChart P (T.map (shearedRightPoint T.length_pos.le u))) :=
    (Stage.positive_flatChart D T hsdelta hclear
      ⟨R,T.length_pos.le,le_rfl⟩ T.length_pos u hu).2.2
  obtain ⟨h,hh,hhlimit,F,hdF,hFold,hFb⟩ := point_exists_translated_longitudinal_extension ha y
    D.closed D.angle_pos D.angle_lt_pi T.length_pos hs hRlimit D.ray D.ray_metric
    T.map T.metric T.bottom C hfront
  have hlen : 0<R+h := add_pos T.length_pos hh
  have he (u : Icc (0 : ℝ) s) : F (shearedCompactEdgePoint hlen.le u) =
      D.edge ⟨u.1,u.2.1,u.2.2.trans hsedge.le⟩ :=
    (hFold (shearedCompactEdgePoint T.length_pos.le u)
      (shearedCompactEdgePoint hlen.le u).2).trans (T.compact_edge u)
  exact ⟨h,hh,hhlimit,⟨⟨hlen,F,Isometry.of_dist_eq hdF,hFb,he⟩⟩⟩

/-- Every requested finite length is attained at the SAME fixed transverse
width. The only initial map is one actually constructed from the corner. -/
theorem exists_stage_at_length {s delta R₀ limit : ℝ} {hs : 0 < s} {hsedge : s < D.edgeLength}
    (T₀ : D.Stage s hs hsedge R₀) (hR₀limit : R₀ ≤ limit) (hsdelta : s ≤ delta)
    (hclear : ∀ z ∈ (↑(pointSignedMarked D.nu D.alpha) : Set ℂ) \ {(D.ray 0).1}, ∀ r : NNReal,
      delta < (pointSmoothConformalEDist a y z (D.ray r).1).toReal) :
    Nonempty (D.Stage s hs hsedge limit) := by
  classical
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  letI : UniformSpace P := M.toUniformSpace
  letI : TopologicalSpace P := M.toUniformSpace.toTopologicalSpace
  letI : CompleteSpace P := pointRegionMetricSpace_complete ha y D.closed
  let W : Set ℝ := {R | R₀≤R ∧ R≤limit ∧ Nonempty (D.Stage s hs hsedge R)}
  have hR₀W : R₀∈W := ⟨le_rfl,hR₀limit,⟨T₀⟩⟩
  have hWne : W.Nonempty := ⟨R₀,hR₀W⟩
  have hWbound : BddAbove W := ⟨limit,fun R hR ↦ hR.2.1⟩
  let T : ∀ R : W, D.Stage s hs hsedge R.1 := fun R ↦ Classical.choice R.2.2.2
  let f := fun R : W ↦ (T R).map
  have hf (R : W) : Isometry (f R) := (T R).metric
  have hcompat : ∀ R Q : W, ∀ z (hR : z∈flatShearedRectangle (conePhase D.angle) R.1 s)
      (hQ : z∈flatShearedRectangle (conePhase D.angle) Q.1 s), f R ⟨z,hR⟩=f Q ⟨z,hQ⟩ := by
    intro R Q z hR hQ
    rcases le_total R.1 Q.1 with hRQ | hQR
    · exact D.stages_agree (T R) (T Q) hRQ hsdelta hclear ⟨z,hR⟩
    · exact (D.stages_agree (T Q) (T R) hQR hsdelta hclear ⟨z,hQ⟩).symm
  obtain ⟨F,hF,hFold⟩ := exists_shearedRectangle_length_supremum_isometry
    (conePhase_norm D.angle) s hWne (fun R hR ↦ T₀.length_pos.trans_le hR.1)
    hWbound f hf hcompat
  let S := sSup W
  have hR₀S : R₀≤S := le_csSup hWbound hR₀W
  have hSpos : 0<S := T₀.length_pos.trans_le hR₀S
  have hSlim : S≤limit := csSup_le hWne (fun R hR ↦ hR.2.1)
  have hFb : ∀ r : Icc (0 : ℝ) S, F (shearedBottomPoint hs.le r)=D.ray ⟨r.1,r.2.1⟩ := by
    let top : Icc (0 : ℝ) S := ⟨S,hSpos.le,le_rfl⟩
    let B : Icc (0 : ℝ) S → flatShearedRectangle (conePhase D.angle) S s := shearedBottomPoint hs.le
    have hB : Isometry B := by
      apply Isometry.of_dist_eq
      intro t u
      exact flatShearedPoint_dist_parallel (conePhase D.angle) t.1 u.1 0
    let rmap : Icc (0 : ℝ) S → NNReal := fun r ↦ ⟨r.1,r.2.1⟩
    have hrmap : Isometry rmap := fun _ _ ↦ rfl
    have heq : EqOn (F∘B) (D.ray∘rmap) (Iio top) := by
      intro r hr
      have hrS : r.1<S := hr
      obtain ⟨Q,hQ,hrQ⟩ := exists_lt_of_lt_csSup hWne hrS
      let q : flatShearedRectangle (conePhase D.angle) Q s :=
        shearedBottomPoint hs.le (⟨r.1,r.2.1,hrQ.le⟩ : Icc (0 : ℝ) Q)
      exact (hFold ⟨Q,hQ⟩ q).trans ((T ⟨Q,hQ⟩).bottom ⟨r.1,r.2.1,hrQ.le⟩)
    have hclosure : closure (Iio top)=Iic top := closure_Iio'
      ⟨(⟨0,le_rfl,hSpos.le⟩ : Icc (0 : ℝ) S),hSpos⟩
    intro r
    exact heq.closure (hF.comp hB).continuous (D.ray_metric.comp hrmap).continuous
      (by rw [hclosure]; exact r.2.2)
  have hFe : ∀ u : Icc (0 : ℝ) s, F (shearedCompactEdgePoint hSpos.le u)=
      D.edge ⟨u.1,u.2.1,u.2.2.trans hsedge.le⟩ := by
    intro u
    exact (hFold ⟨R₀,hR₀W⟩ (shearedCompactEdgePoint (T ⟨R₀,hR₀W⟩).length_pos.le u)).trans
      ((T ⟨R₀,hR₀W⟩).compact_edge u)
  let TF : D.Stage s hs hsedge S := ⟨hSpos,F,hF,hFb,hFe⟩
  have hSeq : S=limit := by
    apply le_antisymm hSlim
    by_contra hn
    have hSlt : S<limit := lt_of_not_ge hn
    obtain ⟨h,hh,hhlim,⟨G⟩⟩ := Stage.exists_longer D TF hSlt hsdelta hclear
    have hnew : S+h∈W := ⟨by linarith,hhlim.le,⟨G⟩⟩
    have hle : S+h≤S := le_csSup hWbound hnew
    linarith
  exact ⟨hSeq ▸ TF⟩

end RepulsiveCoulomb.PointTranslatedOriginalData
