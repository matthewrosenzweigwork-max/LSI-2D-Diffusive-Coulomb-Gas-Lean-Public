import LeanResearch.RepulsiveCoulomb.PointActualSectorRadiusConstruction

/-! ISOLATED SOURCE-ONLY DRAFT. Construct a genuinely unbounded flat map on
every closed strict interior angular window, by compatible finite-radius maps.
No infinite ray family or sector-map input is supplied. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb
namespace PointActualSectorData
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j} {P : Set ℂ}
    (D : PointActualSectorData a y ha P)

theorem exists_unbounded_closed_window
    {l u : ℝ} (hl : 0 < l) (hlu : l < u) (huβ : u < D.beta) :
    ∃ F : flatInteriorAngularWindow l u → P,
      (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
      (∀ z, ‖z.1‖ ≤ D.chart.radius → (F z).1 = D.chart.flatInverse z.1) ∧
      ∀ z, z.1 ≠ 0 → (F z).1 ∈ interior P ∧ (F z).1 ∉ pointSignedMarked D.nu D.alpha := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let S := flatInteriorAngularWindow l u
  let R : ℕ → ℝ := fun n ↦ D.chart.radius + (n + 1)
  let K : ℕ → Set ℂ := fun n ↦ flatRadialTruncation S (R n)
  have hR (n : ℕ) : D.chart.radius ≤ R n := by
    dsimp [R]
    exact le_add_of_nonneg_right (by positivity)
  have hRpos (n : ℕ) : 0 < R n := D.chart.radius_pos.trans_le (hR n)
  have huπ : u ≤ Real.pi := huβ.le.trans D.beta_pi
  have hSconv : Convex ℝ S := flatInteriorAngularWindow_convex hl hlu huπ
  have hSsector : S ⊆ closedEuclideanSector D.beta := by
    intro z hz
    exact ⟨hz.1.1, hz.1.2.trans huβ.le⟩
  have hSarg (q : S) (hq : q.1 ≠ 0) : Complex.arg q.1 ∈ Ioo (0 : ℝ) D.beta := by
    have h := flatInteriorAngularWindow_arg hl hlu huπ q.2 hq
    exact ⟨hl.trans_le h.1, h.2.trans_lt huβ⟩
  have hex (n : ℕ) : ∃ f : K n → P, Isometry f ∧
      ∀ z, ‖z.1‖ ≤ D.chart.radius → (f z).1 = D.chart.flatInverse z.1 := by
    obtain ⟨f, hf, hs⟩ := D.exists_closed_window_at_radius hl hlu huβ (hR n)
    exact ⟨f, Isometry.of_dist_eq hf, hs⟩
  choose f hf hseed using hex
  have hmono {i j : ℕ} (hij : i ≤ j) : K i ⊆ K j := by
    apply flatRadialTruncation_mono S
    have h : (i : ℝ) ≤ j := by exact_mod_cast hij
    dsimp [R]
    linarith
  have hK0 (n : ℕ) : (0 : ℂ) ∈ K n := by
    refine ⟨zero_mem_flatInteriorAngularWindow (hl.trans hlu).le, ?_⟩
    simpa only [mem_closedBall, dist_self] using (hRpos n).le
  have hKarg (n : ℕ) (q : K n) (hq : q.1 ≠ 0) :
      Complex.arg q.1 ∈ Ioo (0 : ℝ) D.beta := hSarg ⟨q.1, q.2.1⟩ hq
  have hcompat : ∀ i j : ℕ, ∀ z (hi : z ∈ K i) (hj : z ∈ K j),
      f i ⟨z, hi⟩ = f j ⟨z, hj⟩ := by
    intro i j z hi hj
    rcases le_total i j with hij | hji
    · exact D.stages_agree (flatRadialTruncation_convex hSconv _)
        (flatInteriorAngularWindow_truncation_interior_nonempty hl hlu huπ (hRpos i))
        (hK0 i) (hmono hij) (fun _ hx ↦ hSsector hx.1) (hKarg i)
        (f i) (f j) (hf i) (hf j) (hseed i) (hseed j) ⟨z, hi⟩
    · exact (D.stages_agree (flatRadialTruncation_convex hSconv _)
        (flatInteriorAngularWindow_truncation_interior_nonempty hl hlu huπ (hRpos j))
        (hK0 j) (hmono hji) (fun _ hx ↦ hSsector hx.1) (hKarg j)
        (f j) (f i) (hf j) (hf i) (hseed j) (hseed i) ⟨z, hj⟩).symm
  have hdir : Directed (· ⊆ ·) K :=
    fun i j ↦ ⟨max i j, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩
  have hsource : S = ⋃ n, K n := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
      refine mem_iUnion.mpr ⟨n, hz, ?_⟩
      change dist z 0 ≤ R n
      rw [dist_zero_right]
      dsimp [R]
      linarith [D.chart.radius_pos]
    · intro z hz
      obtain ⟨n, hn⟩ := mem_iUnion.mp hz
      exact hn.1
  let incl : S → ⋃ n, K n := fun z ↦ ⟨z.1, hsource ▸ z.2⟩
  have hinc : Isometry incl := fun _ _ ↦ rfl
  let F := directedFlatUnion K f hcompat ∘ incl
  have hF : Isometry F := (directedFlatUnion_isometry K f hdir hcompat hf).comp hinc
  have hFseed : ∀ z : S, ‖z.1‖ ≤ D.chart.radius → (F z).1 = D.chart.flatInverse z.1 := by
    intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp (incl z).property
    exact (congrArg Subtype.val (directedFlatUnion_of_mem K f hcompat (incl z) n hn)).trans
      (hseed n ⟨z.1, hn⟩ hz)
  refine ⟨F, fun x z ↦ hF.dist_eq x z, hFseed, ?_⟩
  intro z hz
  exact D.stage_interior_unmarked hSconv
    (zero_mem_flatInteriorAngularWindow (hl.trans hlu).le) hSsector hSarg
    F (fun x z ↦ hF.dist_eq x z) hFseed z hz

end PointActualSectorData
end RepulsiveCoulomb
