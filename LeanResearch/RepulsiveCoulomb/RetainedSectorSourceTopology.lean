module

public import LeanResearch.RepulsiveCoulomb.RetainedSectorPassingHalfDisk
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

/-! SOURCE-ONLY, NOT COMPILED. Literal source closure, properness of a supplied
sector isometry, and connectedness after removing its free ray. These are
source/geometric outputs needed by the actual two-ray Jordan cut theorem. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem retainedSector_source_isClosed {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) :
    IsClosed (closedEuclideanSector β) := by
  rcases lt_or_eq_of_le hβπ with hlt | heq
  · have hset : closedEuclideanSector β = {z : ℂ | 0 ≤ z.im} ∩
        {z : ℂ | Real.cos β*z.im-Real.sin β*z.re ≤ 0} := by
      ext z
      constructor
      · intro hz
        exact ⟨Complex.arg_nonneg_iff.mp hz.1,retainedSector_upper_halfplane hβπ hz⟩
      · exact fun hz ↦ mem_closedEuclideanSector_of_halfplanes hβ hlt hz.1 hz.2
    rw [hset]
    exact (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le ((continuous_const.mul Complex.continuous_im).sub
        (continuous_const.mul Complex.continuous_re)) continuous_const)
  · rw [heq]
    have hset : closedEuclideanSector Real.pi = {z : ℂ | 0 ≤ z.im} := by
      ext z
      simp only [closedEuclideanSector,mem_setOf_eq,Complex.arg_nonneg_iff,Complex.arg_le_pi,and_true]
    rw [hset]
    exact isClosed_le continuous_const Complex.continuous_im

/-- Closed/proper image is a consequence of the genuine old-metric isometry. -/
theorem pointRetainedSector_closed_proper
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z) :
    Topology.IsClosedEmbedding σ ∧ IsProperMap σ := by
  letI : CompleteSpace (closedEuclideanSector β) :=
    (retainedSector_source_isClosed hβ hβπ).isComplete.completeSpace_coe
  have hi : @Isometry (closedEuclideanSector β) ℂ inferInstance
      (pointSmoothConformalMetricSpace ha y).toPseudoEMetricSpace σ :=
    @Isometry.of_dist_eq _ ℂ _ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace _ hσ
  have hc : @Topology.IsClosedEmbedding (closedEuclideanSector β) ℂ inferInstance
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace σ :=
    @Isometry.isClosedEmbedding (closedEuclideanSector β) ℂ
      (inferInstance : EMetricSpace (closedEuclideanSector β))
      (inferInstance : CompleteSpace (closedEuclideanSector β))
      (pointSmoothConformalMetricSpace ha y).toEMetricSpace σ hi
  rw [pointSmoothConformalMetricSpace_topology ha y] at hc
  exact ⟨hc, hc.isProperMap⟩

/-- The sector with its entire free ray removed is connected. Its source
coordinates are (positive radius) times [0,beta), so the bottom stays while the
apex disappears from this relatively open removed piece. -/
theorem retainedSector_without_free_ray_connected {Y : Type*} [TopologicalSpace Y]
    {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (σ : closedEuclideanSector β → Y) (hσ : Continuous σ) (hinj : Function.Injective σ) :
    IsConnected (range σ \ range (fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u))) := by
  let K : Set (ℝ×ℝ) := Ioi (0:ℝ) ×ˢ Ico (0:ℝ) β
  have hKconvex : Convex ℝ K := (convex_Ioi 0).prod (convex_Ico 0 β)
  have hK : IsConnected K := ⟨⟨(1,0),by simp [K,hβ]⟩,hKconvex.isPreconnected⟩
  letI : ConnectedSpace K := isConnected_iff_connectedSpace.mp hK
  let i : K → closedEuclideanSector β := fun q ↦
    ⟨sectorPolar q.1.1 q.1.2,by
      change 0 ≤ Complex.arg _ ∧ Complex.arg _ ≤ β
      rw [sectorPolar_arg q.2.1 ⟨by linarith [q.2.2.1,Real.pi_pos],q.2.2.2.le.trans hβπ⟩]
      exact ⟨q.2.2.1,q.2.2.2.le⟩⟩
  have hi : Continuous i := by
    apply Continuous.subtype_mk
    dsimp [sectorPolar,conePhase]
    fun_prop
  have him : range (σ ∘ i) =
      range σ \ range (fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u)) := by
    ext z
    constructor
    · rintro ⟨q,rfl⟩
      refine ⟨mem_range_self (i q),?_⟩
      rintro ⟨u,hu⟩
      have he := congrArg (fun x : closedEuclideanSector β ↦ x.1) (hinj hu)
      change sectorPolar u β = sectorPolar q.1.1 q.1.2 at he
      have hn := congrArg norm he
      rw [sectorPolar_norm (NNReal.coe_nonneg u),sectorPolar_norm q.2.1.le] at hn
      have hu0 : 0 < (u:ℝ) := hn.symm ▸ q.2.1
      have ha := congrArg Complex.arg he
      rw [sectorPolar_arg hu0 ⟨by linarith [Real.pi_pos],hβπ⟩,
        sectorPolar_arg q.2.1 ⟨by linarith [q.2.2.1,Real.pi_pos],q.2.2.2.le.trans hβπ⟩] at ha
      exact (ne_of_lt q.2.2.2) ha.symm
    · rintro ⟨⟨x,rfl⟩,hxT⟩
      have hx0 : x.1 ≠ 0 := by
        intro hx0
        apply hxT
        refine ⟨0,congrArg σ (Subtype.ext ?_)⟩
        change sectorPolar 0 β = x.1
        rw [sectorPolar_zero,hx0]
      have harg : Complex.arg x.1 < β := lt_of_le_of_ne x.2.2 (by
        intro he
        apply hxT
        refine ⟨⟨‖x.1‖,norm_nonneg _⟩,congrArg σ (Subtype.ext ?_)⟩
        change sectorPolar ‖x.1‖ β = x.1
        exact (congrArg (sectorPolar ‖x.1‖) he).symm.trans (sectorPolar_norm_arg x.1))
      refine ⟨⟨(‖x.1‖,Complex.arg x.1),norm_pos_iff.mpr hx0,x.2.1,harg⟩,?_⟩
      exact congrArg σ (Subtype.ext (sectorPolar_norm_arg x.1))
  rw [← him]
  exact isConnected_range (hσ.comp hi)

end RepulsiveCoulomb
