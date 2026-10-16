import LeanResearch.RepulsiveCoulomb.Imported.Schoenflies.UniformBound
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# Actual disjoint corner neighborhoods and chart disks

All radii below are constructed from a finite injective family of actual
points, a specified point different from those points, actual open
neighborhoods, and ordinary continuity. No disjoint-neighborhood or
radius-selection hypothesis is assumed. The finite index type may be empty.

Records-only proof draft: no compiler or declaration audit has been run.
-/

noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- A finite injective family in a metric space has one positive closed-ball
radius subordinate to prescribed open neighborhoods, separating all the
centers, and avoiding a specified point different from every center. The
statement also covers an empty or singleton index type. -/
theorem exists_uniform_disjoint_closedBalls_avoiding
    {ι X : Type*} [Finite ι] [MetricSpace X]
    (p : ι → X) (hp : Function.Injective p) (w : X)
    (hw : ∀ i, w ≠ p i) (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hpU : ∀ i, p i ∈ U i) :
    ∃ r : ℝ, 0 < r ∧
      (∀ i, closedBall (p i) r ⊆ U i) ∧
      (∀ i, w ∉ closedBall (p i) r) ∧
      Pairwise (fun i j => Disjoint (closedBall (p i) r) (closedBall (p j) r)) := by
  classical
  have hlocal : ∃ a > 0, ∀ i : ι,
      closedBall (p i) a ⊆ U i ∧ a < dist w (p i) := by
    obtain ⟨a, ha, hall⟩ := Schoenflies.exists_pos_forall_of_finite
      (Set.toFinite (Set.univ : Set ι))
      (P := fun i a => closedBall (p i) a ⊆ U i ∧ a < dist w (p i))
      (by
        intro i δ ε _ hδε hε
        exact ⟨(closedBall_subset_closedBall hδε).trans hε.1, hδε.trans_lt hε.2⟩)
      (by
        intro i _
        obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp (hU i) (p i) (hpU i)
        have hd : 0 < dist w (p i) := dist_pos.mpr (hw i)
        refine ⟨min (ε / 2) (dist w (p i) / 2),
          lt_min (by linarith) (by linarith), ?_, ?_⟩
        · apply Subset.trans (closedBall_subset_ball (show
            min (ε / 2) (dist w (p i) / 2) < ε from
            (min_le_left _ _).trans_lt (by linarith))) hεU
        · exact (min_le_right _ _).trans_lt (by linarith))
    exact ⟨a, ha, fun i => hall i (Set.mem_univ i)⟩
  obtain ⟨a, ha, haU⟩ := hlocal
  have hseparation : ∃ b > 0, ∀ i j : ι,
      i ≠ j → 2 * b < dist (p i) (p j) := by
    obtain ⟨b, hb, hall⟩ := Schoenflies.exists_pos_forall_of_finite
      (Set.toFinite (Set.univ : Set (ι × ι)))
      (P := fun ij b => ij.1 ≠ ij.2 → 2 * b < dist (p ij.1) (p ij.2))
      (by
        intro ij δ ε _ hδε hε hij
        have h := hε hij
        linarith)
      (by
        rintro ⟨i, j⟩ _
        by_cases hij : i = j
        · exact ⟨1, zero_lt_one, fun h => (h hij).elim⟩
        · have hd : 0 < dist (p i) (p j) := dist_pos.mpr (fun h => hij (hp h))
          exact ⟨dist (p i) (p j) / 3, by linarith, by intro _; linarith⟩)
    exact ⟨b, hb, fun i j => hall (i, j) (Set.mem_univ (i, j))⟩
  obtain ⟨b, hb, hbsep⟩ := hseparation
  refine ⟨min a b, lt_min ha hb, ?_, ?_, ?_⟩
  · intro i
    exact (closedBall_subset_closedBall (min_le_left a b)).trans (haU i).1
  · intro i hmem
    have hdist : dist w (p i) ≤ min a b := Metric.mem_closedBall.mp hmem
    exact (haU i).2.not_ge (hdist.trans (min_le_left a b))
  · intro i j hij
    apply Metric.closedBall_disjoint_closedBall
    have hsep := hbsep i j hij
    have hle := min_le_right a b
    linarith

/-- Ordinary continuity at the chart center, together with an actual open
chart domain, produces a positive closed chart disk lying in that domain
whose entire image lies strictly inside a prescribed physical ball. -/
theorem exists_closedBall_chart_refinement
    {H : ℂ → ℂ} {p : ℂ} {V : Set ℂ} {r : ℝ}
    (hH : ContinuousAt H 0) (hH0 : H 0 = p)
    (hV : IsOpen V) (h0V : (0 : ℂ) ∈ V) (hr : 0 < r) :
    ∃ R : ℝ, 0 < R ∧ closedBall (0 : ℂ) R ⊆ V ∧
      H '' closedBall (0 : ℂ) R ⊆ ball p r := by
  obtain ⟨δ, hδ, hHδ⟩ := Metric.continuousAt_iff.mp hH r hr
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV 0 h0V
  refine ⟨min (δ / 2) (ε / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩
  · exact (closedBall_subset_ball
      ((min_le_right (δ / 2) (ε / 2)).trans_lt (by linarith))).trans hεV
  · rintro _ ⟨z, hz, rfl⟩
    have hzδ : dist z 0 < δ :=
      (Metric.mem_closedBall.mp hz).trans_lt
        ((min_le_left (δ / 2) (ε / 2)).trans_lt (by linarith))
    simpa only [Metric.mem_ball, hH0] using hHδ hzδ

/-- Finitely many continuous charts admit common positive source and target
radii. The *closed* source disks lie in the actual chart domains and map
strictly inside pairwise-disjoint physical closed balls, each subordinate to
its prescribed physical neighborhood and missing the actual point `w`.

The additional positive radius `ρ < R` is a genuine strict margin: radial
segments, quadratic corner arcs, and their straight homotopy with norm at
most `ρ` lie strictly inside the selected chart disk of radius `R`. -/
theorem exists_uniform_disjoint_chart_disks
    {ι : Type*} [Finite ι]
    (p : ι → ℂ) (hp : Function.Injective p) (w : ℂ)
    (hw : ∀ i, w ≠ p i)
    (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i)) (hpU : ∀ i, p i ∈ U i)
    (V : ι → Set ℂ) (hV : ∀ i, IsOpen (V i)) (h0V : ∀ i, (0 : ℂ) ∈ V i)
    (H : ι → ℂ → ℂ) (hH : ∀ i, ContinuousOn (H i) (V i))
    (hH0 : ∀ i, H i 0 = p i) :
    ∃ r R ρ : ℝ, 0 < r ∧ 0 < R ∧ 0 < ρ ∧ ρ < R ∧
      (∀ i, closedBall (p i) r ⊆ U i) ∧
      (∀ i, w ∉ closedBall (p i) r) ∧
      Pairwise (fun i j => Disjoint (closedBall (p i) r) (closedBall (p j) r)) ∧
      (∀ i, closedBall (0 : ℂ) R ⊆ V i) ∧
      (∀ i, ContinuousOn (H i) (ball (0 : ℂ) R)) ∧
      (∀ i, H i '' closedBall (0 : ℂ) R ⊆ ball (p i) r) ∧
      (∀ i, w ∉ H i '' closedBall (0 : ℂ) R) ∧
      Pairwise (fun i j => Disjoint
        (H i '' closedBall (0 : ℂ) R) (H j '' closedBall (0 : ℂ) R)) := by
  classical
  obtain ⟨r, hr, hrU, hrw, hrdisj⟩ :=
    exists_uniform_disjoint_closedBalls_avoiding p hp w hw U hU hpU
  obtain ⟨R, hR, hall⟩ := Schoenflies.exists_pos_forall_of_finite
    (Set.toFinite (Set.univ : Set ι))
    (P := fun i R => closedBall (0 : ℂ) R ⊆ V i ∧
      H i '' closedBall (0 : ℂ) R ⊆ ball (p i) r)
    (by
      intro i δ ε _ hδε hε
      refine ⟨(closedBall_subset_closedBall hδε).trans hε.1, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact hε.2 ⟨z, closedBall_subset_closedBall hδε hz, rfl⟩)
    (by
      intro i _
      exact exists_closedBall_chart_refinement
        ((hH i).continuousAt ((hV i).mem_nhds (h0V i)))
        (hH0 i) (hV i) (h0V i) hr)
  have hRV (i : ι) : closedBall (0 : ℂ) R ⊆ V i :=
    (hall i (Set.mem_univ i)).1
  have himage (i : ι) : H i '' closedBall (0 : ℂ) R ⊆ ball (p i) r :=
    (hall i (Set.mem_univ i)).2
  have hclosed (i : ι) : H i '' closedBall (0 : ℂ) R ⊆ closedBall (p i) r :=
    (himage i).trans Metric.ball_subset_closedBall
  refine ⟨r, R, R / 2, hr, hR, by linarith, by linarith,
    hrU, hrw, hrdisj, hRV, ?_, himage, ?_, ?_⟩
  · intro i
    exact (hH i).mono (Metric.ball_subset_closedBall.trans (hRV i))
  · intro i hwmem
    exact hrw i (hclosed i hwmem)
  · intro i j hij
    exact (hrdisj hij).mono (hclosed i) (hclosed j)

end RepulsiveCoulomb
