module

public import LeanResearch.RepulsiveCoulomb.ProperMetricAnchoredLineLimit
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

@[expose] public section

/-! Uncompiled additive successor. Explicitly recenter and clip actual finite
segments. The whole-real-line Lipschitz maps and expanding isometric windows
are constructed from the segment equalities; they are not new assumptions. -/
noncomputable section
open Set Metric Filter Topology
namespace RepulsiveCoulomb

def metricCenteredClippedSegment {X : Type*}
    (γ : Icc (0 : ℝ) 1 → X) (τ : Icc (0 : ℝ) 1) (L t : ℝ) : X :=
  γ (projIcc 0 1 (by norm_num) (τ + t / L))

theorem metricCenteredClippedSegment_zero {X : Type*}
    (γ : Icc (0 : ℝ) 1 → X) (τ : Icc (0 : ℝ) 1) (L : ℝ) :
    metricCenteredClippedSegment γ τ L 0 = γ τ := by
  simp [metricCenteredClippedSegment]

theorem metricCenteredClippedSegment_lipschitz
    {X : Type*} [MetricSpace X] (γ : Icc (0 : ℝ) 1 → X)
    (τ : Icc (0 : ℝ) 1) {L : ℝ} (hL : 0 < L)
    (hd : ∀ s t : Icc (0 : ℝ) 1, dist (γ s) (γ t) = L * dist (s : ℝ) t) :
    LipschitzWith 1 (metricCenteredClippedSegment γ τ L) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  let a := (τ : ℝ) + s / L
  let b := (τ : ℝ) + t / L
  have hp : dist (projIcc 0 1 (by norm_num) a) (projIcc 0 1 (by norm_num) b) ≤ dist a b := by
    simpa only [NNReal.coe_one, one_mul] using
      (LipschitzWith.projIcc (show (0 : ℝ) ≤ 1 by norm_num)).dist_le_mul a b
  have halg : L * dist a b = dist s t := by
    rw [Real.dist_eq, Real.dist_eq]
    have hsub : a - b = (s - t) / L := by dsimp [a, b]; ring
    rw [hsub, abs_div, abs_of_pos hL]
    field_simp [ne_of_gt hL] <;> ring
  calc
    dist (metricCenteredClippedSegment γ τ L s) (metricCenteredClippedSegment γ τ L t) =
        L * dist (projIcc 0 1 (by norm_num) a) (projIcc 0 1 (by norm_num) b) := hd _ _
    _ ≤ L * dist a b := mul_le_mul_of_nonneg_left hp hL.le
    _ = 1 * dist s t := by rw [halg, one_mul]

theorem metricCenteredClippedSegment_window
    {X : Type*} [MetricSpace X] (γ : Icc (0 : ℝ) 1 → X)
    (τ : Icc (0 : ℝ) 1) {L R : ℝ} (hL : 0 < L)
    (hd : ∀ s t : Icc (0 : ℝ) 1, dist (γ s) (γ t) = L * dist (s : ℝ) t)
    (hleft : R ≤ (τ : ℝ) * L) (hright : R ≤ (1 - (τ : ℝ)) * L)
    {s t : ℝ} (hs : s ∈ Icc (-R) R) (ht : t ∈ Icc (-R) R) :
    dist (metricCenteredClippedSegment γ τ L s) (metricCenteredClippedSegment γ τ L t) = dist s t := by
  have hparam (r : ℝ) (hr : r ∈ Icc (-R) R) : (τ : ℝ) + r / L ∈ Icc (0 : ℝ) 1 := by
    have hl : -(τ : ℝ) ≤ r / L := (le_div_iff₀ hL).mpr (by nlinarith [hr.1])
    have hu : r / L ≤ 1 - (τ : ℝ) := (div_le_iff₀ hL).mpr (by nlinarith [hr.2])
    constructor <;> linarith
  rw [metricCenteredClippedSegment, metricCenteredClippedSegment,
    projIcc_of_mem _ (hparam s hs), projIcc_of_mem _ (hparam t ht), hd]
  simp only [Real.dist_eq]
  rw [show (τ : ℝ) + s / L - ((τ : ℝ) + t / L) = (s - t) / L by ring,
    abs_div, abs_of_pos hL]
  field_simp [ne_of_gt hL] <;> ring

theorem exists_line_from_centered_finite_segments
    {X : Type*} [MetricSpace X] [ProperSpace X]
    (γ : ℕ → Icc (0 : ℝ) 1 → X) (τ : ℕ → Icc (0 : ℝ) 1) (L : ℕ → ℝ)
    (hL : ∀ n, 0 < L n)
    (hd : ∀ n, ∀ s t : Icc (0 : ℝ) 1, dist (γ n s) (γ n t) = L n * dist (s : ℝ) t)
    (x₀ : X) (R : ℝ) (hanchor : ∀ n, dist (γ n (τ n)) x₀ ≤ R)
    (hleft : ∀ n : ℕ, (n : ℝ) ≤ (τ n : ℝ) * L n)
    (hright : ∀ n : ℕ, (n : ℝ) ≤ (1 - (τ n : ℝ)) * L n) :
    ∃ c : ℝ → X, Isometry c ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ q : ℚ, Tendsto (fun n => metricCenteredClippedSegment (γ (σ n)) (τ (σ n)) (L (σ n)) q)
        atTop (𝓝 (c q)) := by
  apply exists_isometric_line_of_compactly_anchored_windows
    (fun n => metricCenteredClippedSegment (γ n) (τ n) (L n)) x₀ R
  · intro n
    exact metricCenteredClippedSegment_lipschitz (γ n) (τ n) (hL n) (hd n)
  · intro n
    rw [metricCenteredClippedSegment_zero]
    exact hanchor n
  · intro n s hs t ht
    exact metricCenteredClippedSegment_window (γ n) (τ n) (hL n) (hd n)
      (hleft n) (hright n) hs ht

end RepulsiveCoulomb
