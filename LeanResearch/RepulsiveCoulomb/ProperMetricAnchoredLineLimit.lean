module

public import LeanResearch.RepulsiveCoulomb.MetricRationalLineLimit
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

@[expose] public section

/-! Uncompiled additive successor. Proper compact balls and actual increasing
isometric windows yield an actual complete line. The rational-time convergence
is retained for passing quantitative exterior-direction estimates later. -/
noncomputable section
open Set Filter Metric Topology
namespace RepulsiveCoulomb

theorem exists_isometric_line_of_compactly_anchored_windows
    {X : Type*} [MetricSpace X] [ProperSpace X]
    (γ : ℕ → ℝ → X) (x₀ : X) (R : ℝ)
    (hLip : ∀ n, LipschitzWith 1 (γ n))
    (hanchor : ∀ n, dist (γ n 0) x₀ ≤ R)
    (hwindow : ∀ n : ℕ, ∀ s ∈ Icc (-(n : ℝ)) n, ∀ t ∈ Icc (-(n : ℝ)) n,
      dist (γ n s) (γ n t) = dist s t) :
    ∃ c : ℝ → X, Isometry c ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ q : ℚ, Tendsto (fun n => γ (σ n) q) atTop (𝓝 (c q)) := by
  let f : ℕ → ℚ → X := fun n q => γ n q
  let K : ℚ → Set X := fun q => closedBall x₀ (R + |(q : ℝ)|)
  have hK : ∀ q, IsCompact (K q) := fun q => isCompact_closedBall _ _
  have hmem : ∀ n q, f n q ∈ K q := by
    intro n q
    change dist (γ n q) x₀ ≤ R + |(q : ℝ)|
    have hdist : dist (γ n q) (γ n 0) ≤ |(q : ℝ)| := by
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq, sub_zero] using (hLip n).dist_le_mul q 0
    have htri := dist_triangle (γ n q) (γ n 0) x₀
    linarith [hanchor n]
  have hexact : ∀ q r : ℚ, ∀ᶠ n in atTop, dist (f n q) (f n r) = dist q r := by
    intro q r
    obtain ⟨N, hN⟩ := exists_nat_gt (max |(q : ℝ)| |(r : ℝ)|)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hqn : |(q : ℝ)| ≤ n := (le_max_left _ _).trans (hN.le.trans hNn)
    have hrn : |(r : ℝ)| ≤ n := (le_max_right _ _).trans (hN.le.trans hNn)
    have hqcc : (q : ℝ) ∈ Icc (-(n : ℝ)) n := abs_le.mp hqn
    have hrcc : (r : ℝ) ∈ Icc (-(n : ℝ)) n := abs_le.mp hrn
    simpa only [f, Rat.dist_cast] using hwindow n q hqcc r hrcc
  exact exists_real_isometric_line_limit_of_compact_rational_samples f K hK hmem hexact

end RepulsiveCoulomb
