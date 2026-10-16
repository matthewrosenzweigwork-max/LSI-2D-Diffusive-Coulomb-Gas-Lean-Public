module

public import LeanResearch.RepulsiveCoulomb.PointRetainedFlatBoundaryInterval
public import Mathlib.Topology.Connected.Clopen

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. A minimizing ray with zero signed coefficient at
all positive-time boundary contacts has either no positive boundary contact or
lies on the old boundary for every positive time. Local propagation uses the
actual symmetric interval in a genuine retained-flat halfdisk. It is not a
first-contact gap, continuation certificate or a supplied boundary germ. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem pointMetricRay_regular_boundary_contact_all_or_none
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P : Set ℂ} (ρ : NNReal→P)
    (hρ : @Isometry NNReal P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace ρ)
    (hflat : ∀ t : NNReal,0<t→(ρ t).1∈frontier P→
      ∃ C : PointRetainedConeNeighborhood a y P (ρ t).1,C.flatPhysicalWidth=Real.pi) :
    (∀ t : NNReal,0<t→(ρ t).1∉frontier P) ∨
      ∀ t : NNReal,0<t→(ρ t).1∈frontier P := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let X := Ioi (0:ℝ)
  letI : ConnectedSpace X := isConnected_iff_connectedSpace.mp
    (isConnected_Ioi : IsConnected (Ioi (0 : ℝ)))
  let j : X→NNReal := fun t ↦ ⟨t.1,t.2.le⟩
  let B : Set X := {t | (ρ (j t)).1∈frontier P}
  have hj : Continuous j := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hρc : Continuous (fun t ↦ (ρ t).1) :=
    (pointMetricRay_isClosedEmbedding ha y (fun t ↦ (ρ t).1) (fun s t ↦ hρ.dist_eq s t)).continuous
  have hBc : IsClosed B := isClosed_frontier.preimage (hρc.comp hj)
  have hBo : IsOpen B := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨C,hC⟩ := hflat (j t) t.2 ht
    let L := min t.1 C.radius/2
    have hL : 0<L := half_pos (lt_min t.2 C.radius_pos)
    have hLt : L<t.1 := (half_lt_self (lt_min t.2 C.radius_pos)).trans_le (min_le_left _ _)
    have hLC : L<C.radius := (half_lt_self (lt_min t.2 C.radius_pos)).trans_le (min_le_right _ _)
    let k : Icc (-L) L→NNReal := fun s ↦ ⟨t.1+s.1,by linarith [s.2.1]⟩
    have hk : Isometry k := by
      apply Isometry.of_dist_eq
      intro s u
      change |(t.1+s.1)-(t.1+u.1)|=|s.1-u.1|
      congr 1
      ring
    have hk0 : k (complexSymmetricIntervalZero hL)=j t := by
      apply Subtype.ext
      simp only [k,j,complexSymmetricIntervalZero,add_zero]
    have hinterval := pointRetainedFlat_symmetric_interval_frontier ha y ht C hC hL hLC
      (ρ∘k) (hρ.comp hk) (congrArg ρ hk0)
    apply Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self hL))
    intro u hu
    have hdist : |u.1-t.1|<L := hu
    let s : Icc (-L) L := ⟨u.1-t.1,(abs_le.mp hdist.le)⟩
    have he : k s=j u := by
      apply Subtype.ext
      dsimp [k,j,s]
      ring
    have hh := hinterval s
    change (ρ (k s)).1∈frontier P at hh
    rwa [he] at hh
  by_cases hB : B.Nonempty
  · right
    have he : B=univ := (show IsClopen B from ⟨hBc,hBo⟩).eq_univ hB
    intro t ht
    have hmem : (⟨t.1,ht⟩ : X)∈B := by rw [he]; trivial
    exact hmem
  · left
    intro t ht hm
    exact hB ⟨⟨t.1,ht⟩,hm⟩

end RepulsiveCoulomb
