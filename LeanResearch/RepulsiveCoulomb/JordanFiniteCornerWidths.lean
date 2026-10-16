module

public import LeanResearch.RepulsiveCoulomb.JordanDisjointCornerNeighborhoods
public import LeanResearch.RepulsiveCoulomb.JordanRemoteArcSeparation
public import LeanResearch.RepulsiveCoulomb.JordanBezierCorner
public import LeanResearch.RepulsiveCoulomb.JordanTurnAngleLift

@[expose] public section

/-!
# Constructed finite corner neighborhoods and one positive radial cut

The input is an actual finite cyclic family of arcs, literal half-open joint
injectivity, actual endpoint equations, and literal radial germs in actual
open chart domains. No separation radius, positive-width certificate, or
rounding embedding is assumed. All remote sets and all positive widths are
constructed. The successor need only be fixed-point-free: the construction
covers the empty family and two-arc loops without a hidden cardinality bound.

Records-only draft. No compiler or declaration audit has been run by the author.
-/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- Half-open joint injectivity also classifies every closed-arc hit of an
actual corner. The endpoint `1` is reduced to the next arc's endpoint `0`. -/
theorem finite_arc_corner_hit_cases
    {ι : Type*} (σ : Equiv.Perm ι) {f : ι → ℝ → ℂ}
    (hend : ∀ j, f j 1 = f (σ j) 0)
    (hinj : ∀ i j s t, s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t)
    {i j : ι} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (heq : f j t = f i 0) :
    (j = i ∧ t = 0) ∨ (σ j = i ∧ t = 1) := by
  by_cases ht1 : t = 1
  · right
    subst t
    have h := hinj (σ j) i 0 0 (by norm_num) (by norm_num)
      ((hend j).symm.trans heq)
    exact ⟨h.1, rfl⟩
  · left
    exact hinj j i t 0 ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩ (by norm_num) heq

/-- The actual compact remote set for corner `i`: its outgoing tail, its
incoming prefix, and every nonincident full closed arc. For two corners the
last union is empty, but the first two terms remain distinct arcs. -/
def finiteCornerRemoteSet {ι : Type*} (σ : Equiv.Perm ι)
    (f : ι → ℝ → ℂ) (a : ℝ) (i : ι) : Set ℂ :=
  (f i '' Icc a 1 ∪ f (σ.symm i) '' Icc (0 : ℝ) (1 - a)) ∪
    ⋃ j : {j : ι // j ≠ i ∧ σ j ≠ i}, f j.1 '' Icc (0 : ℝ) 1

theorem isCompact_finiteCornerRemoteSet
    {ι : Type*} [Finite ι] (σ : Equiv.Perm ι) {f : ι → ℝ → ℂ}
    (hf : ∀ i, Continuous (f i)) (a : ℝ) (i : ι) :
    IsCompact (finiteCornerRemoteSet σ f a i) := by
  exact ((isCompact_Icc.image (hf i)).union
    (isCompact_Icc.image (hf (σ.symm i)))).union
      (isCompact_iUnion fun j : {j : ι // j ≠ i ∧ σ j ≠ i} =>
        isCompact_Icc.image (hf j.1))

theorem corner_not_mem_finiteCornerRemoteSet
    {ι : Type*} (σ : Equiv.Perm ι) (hσ : ∀ i, σ i ≠ i)
    {f : ι → ℝ → ℂ} (hend : ∀ j, f j 1 = f (σ j) 0)
    (hinj : ∀ i j s t, s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t)
    {a : ℝ} (ha : 0 < a) (i : ι) :
    f i 0 ∉ finiteCornerRemoteSet σ f a i := by
  rintro ((⟨t, ht, heq⟩ | ⟨t, ht, heq⟩) | hother)
  · have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ha.le.trans ht.1, ht.2⟩
    rcases finite_arc_corner_hit_cases σ hend hinj htI heq with h | h
    · linarith [ht.1, h.2]
    · exact hσ i h.1
  · have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
    rcases finite_arc_corner_hit_cases σ hend hinj htI heq with h | h
    · have hfix : σ i = i := by
        calc σ i = σ (σ.symm i) := congrArg σ h.1.symm
          _ = i := σ.apply_symm_apply i
      exact hσ i hfix
    · linarith [ht.2, h.2]
  · obtain ⟨j, t, ht, heq⟩ := Set.mem_iUnion.mp hother
    rcases finite_arc_corner_hit_cases σ hend hinj ht heq with h | h
    · exact j.2.1 h.1
    · exact j.2.2 h.1

/-- A hit outside the constructed remote set can only be on one of the two
incident germs, with a strict parameter margin. No ordering of all corners
and no assumption of at least three corners is used. -/
theorem finiteCornerRemoteSet_compl_hit
    {ι : Type*} (σ : Equiv.Perm ι) (f : ι → ℝ → ℂ) {a : ℝ}
    {i j : ι} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hlocal : f j t ∈ (finiteCornerRemoteSet σ f a i)ᶜ) :
    (j = i ∧ t < a) ∨ (σ j = i ∧ 1 - a < t) := by
  classical
  by_cases hji : j = i
  · left
    refine ⟨hji, ?_⟩
    by_contra hn
    subst j
    exact hlocal (Or.inl (Or.inl ⟨t, ⟨le_of_not_gt hn, ht.2⟩, rfl⟩))
  · by_cases hsji : σ j = i
    · right
      refine ⟨hsji, ?_⟩
      by_contra hn
      have hj : j = σ.symm i := by
        calc j = σ.symm (σ j) := (σ.symm_apply_apply j).symm
          _ = σ.symm i := congrArg σ.symm hsji
      apply hlocal
      exact Or.inl (Or.inr ⟨t, ⟨ht.1, le_of_not_gt hn⟩, by rw [← hj]⟩)
    · exact False.elim (hlocal (Or.inr
        (Set.mem_iUnion.mpr ⟨⟨j, hji, hsji⟩, ⟨t, ht, rfl⟩⟩)))

/-- Actual common physical and chart radii subordinate to the remote-set
complements just constructed. Every old-boundary hit in a chart disk is on
one of that corner's two prescribed incident windows. -/
theorem exists_finite_arc_disjoint_local_chart_disks
    {ι : Type*} [Finite ι] (σ : Equiv.Perm ι) (hσ : ∀ i, σ i ≠ i)
    (f : ι → ℝ → ℂ) (hf : ∀ i, Continuous (f i))
    (hend : ∀ j, f j 1 = f (σ j) 0)
    (hinj : ∀ i j s t, s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t)
    {a : ℝ} (ha : 0 < a) (w : ℂ)
    (hw : w ∉ ⋃ i, f i '' Icc (0 : ℝ) 1)
    (V : ι → Set ℂ) (hV : ∀ i, IsOpen (V i)) (h0V : ∀ i, (0 : ℂ) ∈ V i)
    (H : ι → ℂ → ℂ) (hH : ∀ i, ContinuousOn (H i) (V i))
    (hH0 : ∀ i, H i 0 = f i 0) :
    ∃ r R ρ : ℝ, 0 < r ∧ 0 < R ∧ 0 < ρ ∧ ρ < R ∧
      (∀ i, closedBall (f i 0) r ⊆ (finiteCornerRemoteSet σ f a i)ᶜ) ∧
      (∀ i, w ∉ closedBall (f i 0) r) ∧
      Pairwise (fun i j => Disjoint (closedBall (f i 0) r) (closedBall (f j 0) r)) ∧
      (∀ i, closedBall (0 : ℂ) R ⊆ V i) ∧
      (∀ i, H i '' closedBall (0 : ℂ) R ⊆ ball (f i 0) r) ∧
      (∀ i, w ∉ H i '' closedBall (0 : ℂ) R) ∧
      Pairwise (fun i j => Disjoint
        (H i '' closedBall (0 : ℂ) R) (H j '' closedBall (0 : ℂ) R)) ∧
      ∀ i j t, t ∈ Icc (0 : ℝ) 1 → f j t ∈ H i '' closedBall (0 : ℂ) R →
        (j = i ∧ t < a) ∨ (σ j = i ∧ 1 - a < t) := by
  classical
  have hp : Function.Injective (fun i => f i 0) := by
    intro i j heq
    exact (hinj i j 0 0 (by norm_num) (by norm_num) heq).1
  have hwc : ∀ i, w ≠ f i 0 := by
    intro i heq
    exact hw (Set.mem_iUnion.mpr ⟨i, ⟨0, by norm_num, heq.symm⟩⟩)
  let U : ι → Set ℂ := fun i => (finiteCornerRemoteSet σ f a i)ᶜ
  have hU : ∀ i, IsOpen (U i) := fun i =>
    (isCompact_finiteCornerRemoteSet σ hf a i).isClosed.isOpen_compl
  have hpU : ∀ i, f i 0 ∈ U i := corner_not_mem_finiteCornerRemoteSet σ hσ hend hinj ha
  obtain ⟨r, R, ρ, hr, hR, hρ, hρR, hrU, hrw, hrdisj, hRV, _, himage,
      havoid, hdisj⟩ := exists_uniform_disjoint_chart_disks
    (fun i => f i 0) hp w hwc U hU hpU V hV h0V H hH hH0
  refine ⟨r, R, ρ, hr, hR, hρ, hρR, hrU, hrw, hrdisj, hRV,
    himage, havoid, hdisj, ?_⟩
  intro i j t ht hmem
  exact finiteCornerRemoteSet_compl_hit σ f ht
    (hrU i (Metric.ball_subset_closedBall (himage i hmem)))

/-- The finitely many literal germs hold on one closed two-sided parameter
window of radius `2a`, and every radial coordinate on that same window is
inside its actual chart domain. The strict cap also covers an empty family. -/
theorem exists_finite_radial_germ_window
    {ι : Type*} [Finite ι] (σ : Equiv.Perm ι)
    (f : ι → ℝ → ℂ) (V : ι → Set ℂ)
    (hV : ∀ i, IsOpen (V i)) (h0V : ∀ i, (0 : ℂ) ∈ V i)
    (H : ι → ℂ → ℂ) (u v : ι → ℂ)
    (hout : ∀ i, f i =ᶠ[𝓝 (0 : ℝ)] (fun t => H i (t • v i)))
    (hin : ∀ i, (fun t => f i (1 + t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => H (σ i) (t • u (σ i)))) :
    ∃ a : ℝ, 0 < a ∧ a < 1 / 4 ∧
      ∀ i t, |t| ≤ 2 * a →
        t • u i ∈ V i ∧ t • v i ∈ V i ∧
        f (σ.symm i) (1 + t) = H i (t • u i) ∧
        f i t = H i (t • v i) := by
  classical
  let P : ι → ℝ → Prop := fun i a => ∀ t : ℝ, |t| ≤ 2 * a →
    t • u i ∈ V i ∧ t • v i ∈ V i ∧
    f (σ.symm i) (1 + t) = H i (t • u i) ∧ f i t = H i (t • v i)
  obtain ⟨b, hb, hall⟩ := Schoenflies.exists_pos_forall_of_finite
    (Set.toFinite (Set.univ : Set ι)) (P := P)
    (by
      intro i δ ε _ hδε hε t ht
      exact hε t (by linarith))
    (by
      intro i _
      have hucont : ContinuousAt (fun t : ℝ => t • u i) 0 := by fun_prop
      have hvcont : ContinuousAt (fun t : ℝ => t • v i) 0 := by fun_prop
      have huV : ∀ᶠ t : ℝ in 𝓝 0, t • u i ∈ V i :=
        hucont (by simpa only [zero_smul] using (hV i).mem_nhds (h0V i))
      have hvV : ∀ᶠ t : ℝ in 𝓝 0, t • v i ∈ V i :=
        hvcont (by simpa only [zero_smul] using (hV i).mem_nhds (h0V i))
      have hnear : ∀ᶠ t : ℝ in 𝓝 0,
          t • u i ∈ V i ∧ t • v i ∈ V i ∧
          f (σ.symm i) (1 + t) = H i (t • u i) ∧ f i t = H i (t • v i) := by
        filter_upwards [huV, hvV, hin (σ.symm i), hout i] with t htu htv hti hto
        exact ⟨htu, htv, by simpa only [Equiv.apply_symm_apply] using hti, hto⟩
      obtain ⟨r, hr, hrnear⟩ := Metric.eventually_nhds_iff.mp hnear
      refine ⟨r / 4, by linarith, ?_⟩
      intro t ht
      apply hrnear
      rw [Real.dist_eq, sub_zero]
      linarith)
  refine ⟨min b (1 / 8), lt_min hb (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro i t ht
  exact hall i (Set.mem_univ i) t (by linarith [min_le_left b (1 / 8 : ℝ)])

/-- One actual positive cut is shorter than the germ window and has both
scaled chart velocities inside the prescribed strict-margin disk. -/
theorem exists_finite_positive_radial_cut
    {ι : Type*} [Finite ι] (u v : ι → ℂ) {a ρ : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < a ∧ δ < 1 / 4 ∧
      ∀ i, ‖δ • u i‖ ≤ ρ ∧ ‖δ • v i‖ ≤ ρ := by
  classical
  let P : ι → ℝ → Prop := fun i δ => ‖δ • u i‖ ≤ ρ ∧ ‖δ • v i‖ ≤ ρ
  have hmono : ∀ i, ∀ ⦃δ ε : ℝ⦄, 0 < δ → δ ≤ ε → P i ε → P i δ := by
    intro i δ ε hδ hδε hε
    have hεpos : 0 < ε := hδ.trans_le hδε
    have hbound (z : ℂ) : ‖δ • z‖ ≤ ‖ε • z‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hδ, abs_of_pos hεpos]
      exact mul_le_mul_of_nonneg_right hδε (norm_nonneg z)
    exact ⟨(hbound (u i)).trans hε.1, (hbound (v i)).trans hε.2⟩
  obtain ⟨b, hb, hall⟩ := Schoenflies.exists_pos_forall_of_finite
    (Set.toFinite (Set.univ : Set ι)) (P := P) hmono
    (by
      intro i _
      let M : ℝ := ‖u i‖ + ‖v i‖ + 1
      have hM : 0 < M := by dsimp [M]; positivity
      have hq : 0 < ρ / M := div_pos hρ hM
      have huM : ‖u i‖ ≤ M := by dsimp [M]; linarith [norm_nonneg (v i)]
      have hvM : ‖v i‖ ≤ M := by dsimp [M]; linarith [norm_nonneg (u i)]
      have hbound (z : ℂ) (hz : ‖z‖ ≤ M) : ‖(ρ / M) • z‖ ≤ ρ := by
        calc
          ‖(ρ / M) • z‖ = (ρ / M) * ‖z‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq]
          _ ≤ (ρ / M) * M := mul_le_mul_of_nonneg_left hz hq.le
          _ = ρ := div_mul_cancel₀ _ hM.ne'
      exact ⟨ρ / M, hq, hbound (u i) huM, hbound (v i) hvM⟩)
  let δ : ℝ := min (b / 2) (min (a / 2) (1 / 8))
  have hδ : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have hδb : δ ≤ b := (min_le_left _ _).trans (by linarith)
  have hδa : δ < a := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hδq : δ < 1 / 4 := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num)
  exact ⟨δ, hδ, hδa, hδq, fun i => hmono i hδ hδb (hall i (Set.mem_univ i))⟩

/-- The closed two-sided window gives literal neighborhood equalities at both
attachment parameters, as well as actual chart membership of the cut points. -/
theorem finite_radial_window_attachment_germs
    {ι : Type*} (σ : Equiv.Perm ι) (f : ι → ℝ → ℂ)
    (V : ι → Set ℂ) (H : ι → ℂ → ℂ) (u v : ι → ℂ) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a)
    (hwindow : ∀ i t, |t| ≤ 2 * a →
      t • u i ∈ V i ∧ t • v i ∈ V i ∧
      f (σ.symm i) (1 + t) = H i (t • u i) ∧ f i t = H i (t • v i)) :
    ∀ i,
      ((fun t => f (σ.symm i) (1 + t)) =ᶠ[𝓝 (-δ)] (fun t => H i (t • u i))) ∧
      (f i =ᶠ[𝓝 δ] (fun t => H i (t • v i))) ∧
      (-δ) • u i ∈ V i ∧ δ • v i ∈ V i ∧
      f (σ.symm i) (1 - δ) = H i ((-δ) • u i) ∧ f i δ = H i (δ • v i) := by
  intro i
  have hleft : (-δ) ∈ Ioo (-2 * a) (2 * a) := by constructor <;> linarith
  have hright : δ ∈ Ioo (-2 * a) (2 * a) := by constructor <;> linarith
  have habs : |δ| ≤ 2 * a := by rw [abs_of_pos hδ]; linarith
  have habsneg : |-δ| ≤ 2 * a := by simpa only [abs_neg] using habs
  have hminus := hwindow i (-δ) habsneg
  have hplus := hwindow i δ habs
  refine ⟨?_, ?_, hminus.1, hplus.2.1, ?_, hplus.2.2.2⟩
  · filter_upwards [Ioo_mem_nhds hleft.1 hleft.2] with t ht
    exact (hwindow i t (abs_le.mpr ⟨by linarith [ht.1], ht.2.le⟩)).2.2.1
  · filter_upwards [Ioo_mem_nhds hright.1 hright.2] with t ht
    exact (hwindow i t (abs_le.mpr ⟨by linarith [ht.1], ht.2.le⟩)).2.2.2
  · simpa only [sub_eq_add_neg] using hminus.2.2.1

/-- End-to-end parameter constructor from literal finite-arc and chart data.
In particular, the remote complements and every positive radius are outputs,
not input certificates. The retained closed two-sided window supplies exact
attachment germs by `finite_radial_window_attachment_germs`. -/
theorem exists_finite_radial_corner_rounding_parameters
    {ι : Type*} [Finite ι] (σ : Equiv.Perm ι) (hσ : ∀ i, σ i ≠ i)
    (f : ι → ℝ → ℂ) (hf : ∀ i, Continuous (f i))
    (hend : ∀ j, f j 1 = f (σ j) 0)
    (hinj : ∀ i j s t, s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t)
    (w : ℂ) (hw : w ∉ ⋃ i, f i '' Icc (0 : ℝ) 1)
    (V : ι → Set ℂ) (hV : ∀ i, IsOpen (V i)) (h0V : ∀ i, (0 : ℂ) ∈ V i)
    (H : ι → ℂ → ℂ) (hH : ∀ i, ContinuousOn (H i) (V i))
    (hH0 : ∀ i, H i 0 = f i 0) (u v : ι → ℂ)
    (hout : ∀ i, f i =ᶠ[𝓝 (0 : ℝ)] (fun t => H i (t • v i)))
    (hin : ∀ i, (fun t => f i (1 + t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => H (σ i) (t • u (σ i)))) :
    ∃ a r R ρ δ : ℝ,
      0 < a ∧ a < 1 / 4 ∧ 0 < r ∧ 0 < R ∧ 0 < ρ ∧ ρ < R ∧
      0 < δ ∧ δ < a ∧ δ < 1 / 4 ∧
      (∀ i t, |t| ≤ 2 * a →
        t • u i ∈ V i ∧ t • v i ∈ V i ∧
        f (σ.symm i) (1 + t) = H i (t • u i) ∧ f i t = H i (t • v i)) ∧
      (∀ i, closedBall (f i 0) r ⊆ (finiteCornerRemoteSet σ f a i)ᶜ) ∧
      (∀ i, w ∉ closedBall (f i 0) r) ∧
      Pairwise (fun i j => Disjoint (closedBall (f i 0) r) (closedBall (f j 0) r)) ∧
      (∀ i, closedBall (0 : ℂ) R ⊆ V i) ∧
      (∀ i, H i '' closedBall (0 : ℂ) R ⊆ ball (f i 0) r) ∧
      (∀ i, w ∉ H i '' closedBall (0 : ℂ) R) ∧
      Pairwise (fun i j => Disjoint
        (H i '' closedBall (0 : ℂ) R) (H j '' closedBall (0 : ℂ) R)) ∧
      (∀ i j t, t ∈ Icc (0 : ℝ) 1 → f j t ∈ H i '' closedBall (0 : ℂ) R →
        (j = i ∧ t < a) ∨ (σ j = i ∧ 1 - a < t)) ∧
      (∀ i, ‖δ • u i‖ ≤ ρ ∧ ‖δ • v i‖ ≤ ρ) := by
  obtain ⟨a, ha, haq, hwindow⟩ :=
    exists_finite_radial_germ_window σ f V hV h0V H u v hout hin
  obtain ⟨r, R, ρ, hr, hR, hρ, hρR, hrU, hrw, hrdisj, hRV, himage,
      havoid, hdisj, hlocal⟩ :=
    exists_finite_arc_disjoint_local_chart_disks σ hσ f hf hend hinj ha
      w hw V hV h0V H hH hH0
  obtain ⟨δ, hδ, hδa, hδq, hnorm⟩ := exists_finite_positive_radial_cut u v ha hρ
  exact ⟨a, r, R, ρ, δ, ha, haq, hr, hR, hρ, hρR, hδ, hδa, hδq,
    hwindow, hrU, hrw, hrdisj, hRV, himage, havoid, hdisj, hlocal, hnorm⟩

/-- The actual simultaneous quadratic replacements in their actual charts. -/
def finiteChartBezier {ι : Type*} (H : ι → ℂ → ℂ) (u v : ι → ℂ)
    (δ : ℝ) (i : ι) (t : ℝ) : ℂ :=
  H i (euclideanBezierCorner (δ • u i) (δ • v i) t)

/-- The replacement has the actual old-arc attachment points, including the
incoming sign dictated by the oriented radial velocity. -/
theorem finiteChartBezier_attachment_points
    {ι : Type*} (σ : Equiv.Perm ι) (f : ι → ℝ → ℂ)
    (V : ι → Set ℂ) (H : ι → ℂ → ℂ) (u v : ι → ℂ) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a)
    (hwindow : ∀ i t, |t| ≤ 2 * a →
      t • u i ∈ V i ∧ t • v i ∈ V i ∧
      f (σ.symm i) (1 + t) = H i (t • u i) ∧ f i t = H i (t • v i)) :
    ∀ i, finiteChartBezier H u v δ i 0 = f (σ.symm i) (1 - δ) ∧
      finiteChartBezier H u v δ i 1 = f i δ := by
  intro i
  have hcuts := finite_radial_window_attachment_germs σ f V H u v hδ hδa hwindow i
  constructor
  · calc
      finiteChartBezier H u v δ i 0 = H i ((-δ) • u i) := by
        simp only [finiteChartBezier, euclideanBezierCorner_zero, neg_smul]
      _ = f (σ.symm i) (1 - δ) := hcuts.2.2.2.2.1.symm
  · simpa only [finiteChartBezier, euclideanBezierCorner_one] using hcuts.2.2.2.2.2.symm

/-- Concrete consumer of the constructed parameters. Whole replacement
images are pairwise disjoint and avoid `w`; every open replacement image
misses every retained closed middle, including both adjacent middle pieces.
The two local exclusions are the accepted quadratic tail inequalities. -/
theorem finiteChartBezier_disjoint_retained_middles
    {ι : Type*} (σ : Equiv.Perm ι) (f : ι → ℝ → ℂ)
    (V : ι → Set ℂ) (H : ι → ℂ → ℂ) (u v : ι → ℂ) (w : ℂ)
    {a R ρ δ : ℝ} (hδ : 0 < δ) (hδa : δ < a) (haq : a < 1 / 4)
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hwindow : ∀ i t, |t| ≤ 2 * a →
      t • u i ∈ V i ∧ t • v i ∈ V i ∧
      f (σ.symm i) (1 + t) = H i (t • u i) ∧ f i t = H i (t • v i))
    (hRV : ∀ i, closedBall (0 : ℂ) R ⊆ V i)
    (havoid : ∀ i, w ∉ H i '' closedBall (0 : ℂ) R)
    (hdisj : Pairwise (fun i j => Disjoint
      (H i '' closedBall (0 : ℂ) R) (H j '' closedBall (0 : ℂ) R)))
    (hlocal : ∀ i j s, s ∈ Icc (0 : ℝ) 1 → f j s ∈ H i '' closedBall (0 : ℂ) R →
      (j = i ∧ s < a) ∨ (σ j = i ∧ 1 - a < s))
    (hnorm : ∀ i, ‖δ • u i‖ ≤ ρ ∧ ‖δ • v i‖ ≤ ρ)
    (hHinj : ∀ i, InjOn (H i) (V i))
    (hu : ∀ i, u i ≠ 0) (hc : ∀ i, v i / u i ∈ Complex.slitPlane) :
    (∀ i, MapsTo (euclideanBezierCorner (δ • u i) (δ • v i)) (Icc (0 : ℝ) 1) (V i)) ∧
      (∀ i, InjOn (finiteChartBezier H u v δ i) (Icc (0 : ℝ) 1)) ∧
      Pairwise (fun i j => Disjoint
        (finiteChartBezier H u v δ i '' Icc (0 : ℝ) 1)
        (finiteChartBezier H u v δ j '' Icc (0 : ℝ) 1)) ∧
      (∀ i, w ∉ finiteChartBezier H u v δ i '' Icc (0 : ℝ) 1) ∧
      ∀ i j, Disjoint
        (finiteChartBezier H u v δ i '' Ioo (0 : ℝ) 1)
        (f j '' Icc δ (1 - δ)) := by
  have hδu (i : ι) : δ • u i ≠ 0 := smul_ne_zero hδ.ne' (hu i)
  have hcδ (i : ι) : (δ • v i) / (δ • u i) ∈ Complex.slitPlane := by
    have hδc : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
    have he : (δ • v i) / (δ • u i) = v i / u i := by
      simp only [Complex.real_smul]
      field_simp [hδc, hu i]
    rw [he]
    exact hc i
  have hBR (i : ι) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      euclideanBezierCorner (δ • u i) (δ • v i) t ∈ closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (euclideanBezierCorner_norm_le hρ.le (hnorm i).1 (hnorm i).2 ht).trans hρR.le
  have hBV (i : ι) :
      MapsTo (euclideanBezierCorner (δ • u i) (δ • v i)) (Icc (0 : ℝ) 1) (V i) :=
    fun _ ht => hRV i (hBR i ht)
  have hsub (i : ι) : finiteChartBezier H u v δ i '' Icc (0 : ℝ) 1 ⊆
      H i '' closedBall (0 : ℂ) R := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨_, hBR i ht, rfl⟩
  refine ⟨hBV, ?_, ?_, ?_, ?_⟩
  · intro i s hs t ht heq
    exact euclideanBezierCorner_injOn (hδu i) (hcδ i) hs ht
      (hHinj i (hBV i hs) (hBV i ht) heq)
  · intro i j hij
    exact (hdisj hij).mono (hsub i) (hsub j)
  · intro i hwmem
    exact havoid i (hsub i hwmem)
  · intro i j
    apply Set.disjoint_left.mpr
    rintro z ⟨t, ht, rfl⟩ ⟨s, hs, hsz⟩
    have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hδ.le.trans hs.1, by linarith [hs.2]⟩
    have hmem : f j s ∈ H i '' closedBall (0 : ℂ) R := by
      rw [hsz]
      exact hsub i ⟨t, htI, rfl⟩
    rcases hlocal i j s hsI hmem with ⟨hji, hsa⟩ | ⟨hsji, has⟩
    · subst j
      have hsabs : |s| ≤ 2 * a := by rw [abs_of_nonneg hsI.1]; linarith
      have hwin := hwindow i s hsabs
      have he : euclideanBezierCorner (δ • u i) (δ • v i) t = s • v i :=
        hHinj i (hBV i htI) hwin.2.1 (hsz.symm.trans hwin.2.2.2)
      have hcf : 1 ≤ s / δ := (one_le_div hδ).mpr hs.1
      have hscale : (s / δ) • (δ • v i) = s • v i := by
        rw [smul_smul, div_mul_cancel₀ _ hδ.ne']
      exact euclideanBezierCorner_ne_outgoing_tail (hδu i) (hcδ i)
        ⟨ht.1.le, ht.2⟩ hcf (he.trans hscale.symm)
    · have hsabs : |s - 1| ≤ 2 * a := by
        rw [abs_of_nonpos (by linarith [hsI.2])]
        linarith
      have hwin := hwindow i (s - 1) hsabs
      have hj : σ.symm i = j := by
        calc σ.symm i = σ.symm (σ j) := congrArg σ.symm hsji.symm
          _ = j := σ.symm_apply_apply j
      have hsr : f j s = H i ((s - 1) • u i) := by
        simpa only [hj, show (1 : ℝ) + (s - 1) = s by ring] using hwin.2.2.1
      have he : euclideanBezierCorner (δ • u i) (δ • v i) t = (s - 1) • u i :=
        hHinj i (hBV i htI) hwin.1 (hsz.symm.trans hsr)
      have hcf : 1 ≤ (1 - s) / δ := (one_le_div hδ).mpr (by linarith [hs.2])
      have hscale : (-((1 - s) / δ)) • (δ • u i) = (s - 1) • u i := by
        rw [smul_smul]
        congr 1
        field_simp [hδ.ne'] <;> ring
      exact euclideanBezierCorner_ne_incoming_tail (hδu i) (hcδ i)
        ⟨ht.1, ht.2.le⟩ hcf (he.trans hscale.symm)

end RepulsiveCoulomb
