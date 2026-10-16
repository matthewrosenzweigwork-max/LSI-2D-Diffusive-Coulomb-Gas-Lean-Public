module

public import LeanResearch.RepulsiveCoulomb.PointActualSectorStageCompatibility
public import LeanResearch.RepulsiveCoulomb.FlatRadialRadiusSupremum

@[expose] public section

/-! ISOLATED SOURCE-ONLY DRAFT. Actual bounded-radius construction in every
strict interior angular window. Initial maps, stage regularity, compatibility,
Cauchy completion and positive compact-front extension are all constructed.
No sector map, compatible family, maximality, or continuation certificate is
an input. Kernel verification remains pending with the sole checker.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb
namespace PointActualSectorData
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j} {P : Set ℂ}
    (D : PointActualSectorData a y ha P)

include D in
theorem region_closed : IsClosed P := by
  rw [D.halfplane_eq]
  exact (isClosed_le continuous_const Complex.continuous_im).preimage D.halfplane.continuous

/-- At every requested finite radius, construct an actual ambient isometric
closed angular-window sector. Agreement with the whole initial metric chart
is retained. In particular the map has no assumed stage-flatness field. -/
theorem exists_closed_window_at_radius
    {l u R : ℝ} (hl : 0 < l) (hlu : l < u) (huβ : u < D.beta)
    (hR : D.chart.radius ≤ R) :
    ∃ f : flatRadialTruncation (flatInteriorAngularWindow l u) R → P,
      (∀ x z, (pointSmoothConformalEDist a y (f x).1 (f z).1).toReal = dist x z) ∧
      ∀ z, ‖z.1‖ ≤ D.chart.radius → (f z).1 = D.chart.flatInverse z.1 := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : EMetricSpace P := M.toEMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  letI : UniformSpace P := M.toUniformSpace
  letI : TopologicalSpace P := M.toUniformSpace.toTopologicalSpace
  letI : CompleteSpace P := pointRegionMetricSpace_complete ha y D.region_closed
  let S := flatInteriorAngularWindow l u
  let K := fun r : ℝ ↦ flatRadialTruncation S r
  have huπ : u ≤ Real.pi := huβ.le.trans D.beta_pi
  have hS : Convex ℝ S := flatInteriorAngularWindow_convex hl hlu huπ
  have hSclosed : IsClosed S := flatInteriorAngularWindow_isClosed hl hlu huπ
  have hscale : ∀ z ∈ S, ∀ t : ℝ, 0 ≤ t → t • z ∈ S :=
    fun z hz t ht ↦ flatInteriorAngularWindow_nonneg_smul hl hlu huπ hz ht
  have hKconv (r : ℝ) : Convex ℝ (K r) := flatRadialTruncation_convex hS r
  have hKne {r : ℝ} (hr : 0 < r) : (interior (K r)).Nonempty :=
    flatInteriorAngularWindow_truncation_interior_nonempty hl hlu huπ hr
  have hK0 {r : ℝ} (hr : 0 ≤ r) : (0 : ℂ) ∈ K r := by
    refine ⟨zero_mem_flatInteriorAngularWindow (hl.trans hlu).le, ?_⟩
    simpa only [mem_closedBall, dist_self] using hr
  have hKsector (r : ℝ) : K r ⊆ closedEuclideanSector D.beta := by
    intro z hz
    exact ⟨hz.1.1.1, hz.1.1.2.trans huβ.le⟩
  have hKarg (r : ℝ) (q : K r) (hq : q.1 ≠ 0) : Complex.arg q.1 ∈ Ioo (0 : ℝ) D.beta := by
    have h := flatInteriorAngularWindow_arg hl hlu huπ q.2.1 hq
    exact ⟨hl.trans_le h.1, h.2.trans_lt huβ⟩
  let Seed := fun (r : ℝ) (f : K r → P) ↦
    ∀ z, ‖z.1‖ ≤ D.chart.radius → (f z).1 = D.chart.flatInverse z.1
  let W : Set ℝ := {r | D.chart.radius ≤ r ∧ r ≤ R ∧
    ∃ f : K r → P, Isometry f ∧ Seed r f}
  obtain ⟨f0, hf0, hseed0⟩ := D.chart.exists_interior_window_seed ha y
    (huβ.le.trans D.beta_width) huπ
  have hzeroW : D.chart.radius ∈ W :=
    ⟨le_rfl, hR, f0, Isometry.of_dist_eq hf0, fun z _ ↦ hseed0 z⟩
  have hWne : W.Nonempty := ⟨D.chart.radius, hzeroW⟩
  have hWbound : BddAbove W := ⟨R, fun r hr ↦ hr.2.1⟩
  have hWpos : ∀ r ∈ W, 0 < r := fun r hr ↦ D.chart.radius_pos.trans_le hr.1
  have hmaps : ∀ r : W, ∃ f : K r.1 → P, Isometry f ∧ Seed r.1 f := fun r ↦ r.2.2.2
  choose f hf hseed using hmaps
  have hcompat : ∀ r s : W, ∀ z (hr : z ∈ K r.1) (hs : z ∈ K s.1),
      f r ⟨z, hr⟩ = f s ⟨z, hs⟩ := by
    intro r s z hr hs
    rcases le_total r.1 s.1 with hrs | hsr
    · exact D.stages_agree (hKconv r.1) (hKne (hWpos r.1 r.2))
        (hK0 (hWpos r.1 r.2).le) (flatRadialTruncation_mono S hrs)
        (hKsector r.1) (hKarg r.1) (f r) (f s) (hf r) (hf s)
        (hseed r) (hseed s) ⟨z, hr⟩
    · exact (D.stages_agree (hKconv s.1) (hKne (hWpos s.1 s.2))
        (hK0 (hWpos s.1 s.2).le) (flatRadialTruncation_mono S hsr)
        (hKsector s.1) (hKarg s.1) (f s) (f r) (hf s) (hf r)
        (hseed s) (hseed r) ⟨z, hs⟩).symm
  obtain ⟨F, hF, hFold⟩ := exists_flatRadialTruncation_supremum_isometry
    hSclosed hscale hWne hWpos hWbound f hf hcompat
  let T := sSup W
  have hR0T : D.chart.radius ≤ T := le_csSup hWbound hzeroW
  have hT : 0 < T := D.chart.radius_pos.trans_le hR0T
  have hTR : T ≤ R := csSup_le hWne (fun r hr ↦ hr.2.1)
  have hFseed : Seed T F := by
    intro z hz
    have hz0 : z.1 ∈ K D.chart.radius :=
      ⟨z.2.1, by simpa only [mem_closedBall, dist_zero_right] using hz⟩
    have he := hFold (⟨D.chart.radius, hzeroW⟩ : W) ⟨z.1, hz0⟩
    exact (congrArg Subtype.val he).trans (hseed ⟨D.chart.radius, hzeroW⟩ ⟨z.1, hz0⟩ hz)
  have hTeq : T = R := by
    apply le_antisymm hTR
    by_contra hn
    have hTlt : T < R := lt_of_not_ge hn
    have hfront : ∀ z : flatRadialFront S T,
        Nonempty (MetricFlatDiskChart P (F ⟨z.1, flatRadialFront_subset S T z.2⟩)) := by
      intro z
      have hn : ‖z.1‖ = T := by simpa only [mem_sphere, dist_zero_right] using z.2.2
      have hz0 : z.1 ≠ 0 := by intro he; rw [he, norm_zero] at hn; exact hT.ne' hn.symm
      exact D.stage_flatDisk (hKconv T) (hK0 hT.le) (hKsector T) (hKarg T)
        F (fun x z ↦ hF.dist_eq x z) hFseed ⟨z.1, flatRadialFront_subset S T z.2⟩ hz0
    obtain ⟨h, hh, hhR, G, hG, hGold⟩ := point_exists_closed_radial_front_extension ha y
      D.region_closed hS hSclosed hscale hT (sub_pos.mpr hTlt) (hKne hT) F hF hfront
    have hGseed : Seed (T + h) G := by
      intro z hz
      have hzT : z.1 ∈ K T :=
        ⟨z.2.1, by simpa only [mem_closedBall, dist_zero_right] using hz.trans hR0T⟩
      exact (congrArg Subtype.val (hGold ⟨z.1, hzT⟩ z.2)).trans (hFseed ⟨z.1, hzT⟩ hz)
    have hnew : T + h ∈ W :=
      ⟨by linarith, by linarith, G, Isometry.of_dist_eq hG, hGseed⟩
    have hle := le_csSup hWbound hnew
    change T + h ≤ T at hle
    linarith
  let incl : K R → K T := fun z ↦ ⟨z.1, hTeq.symm ▸ z.2⟩
  have hinc : Isometry incl := fun _ _ ↦ rfl
  refine ⟨F ∘ incl, fun x z ↦ (hF.comp hinc).dist_eq x z, ?_⟩
  intro z hz
  exact hFseed (incl z) hz

end PointActualSectorData
end RepulsiveCoulomb
