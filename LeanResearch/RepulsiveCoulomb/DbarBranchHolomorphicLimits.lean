import LeanResearch.RepulsiveCoulomb.PoleBranchDerivativeBounds
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.MetricSpace.Cauchy

/-! Uniform limits of genuinely holomorphic maps on complex normed-space
balls. Derivative convergence is proved from the Schwarz derivative bound,
not supplied as an additional analytic assumption. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem dbarUniformCauchy_exists_limit {X F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    {u : ℕ → X → F} {s : Set X} (hu : UniformCauchySeqOn u atTop s) :
    ∃ f : X → F, TendstoUniformlyOn u f atTop s := by
  classical
  have hp (x : s) : ∃ y : F, Tendsto (fun n => u n x) atTop (𝓝 y) :=
    cauchySeq_tendsto_of_complete (hu.cauchySeq x.property)
  choose g hg using hp
  let f : X → F := fun x => if hx : x ∈ s then g ⟨x, hx⟩ else 0
  refine ⟨f, hu.tendstoUniformlyOn_of_tendsto ?_⟩
  intro x hx
  simpa only [f, dif_pos hx] using hg ⟨x, hx⟩

theorem dbarHolomorphic_derivative_uniformCauchy
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℕ → E → F} {c : E} {r R : ℝ} (hrR : r < R)
    (hf : ∀ n, DifferentiableOn ℂ (f n) (ball c R))
    (hu : UniformCauchySeqOn f atTop (ball c R)) :
    UniformCauchySeqOn (fun n => fderiv ℂ (f n)) atTop (ball c r) := by
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  have hgap : 0 < R - r := sub_pos.mpr hrR
  let M : ℝ := ε * (R - r) / 4
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨n0, hn0⟩ := Metric.uniformCauchySeqOn_iff.mp hu M hM
  refine ⟨n0, ?_⟩
  intro n hn m hm x hx
  have hb : ∀ y ∈ ball c R, ‖(f n - f m) y‖ ≤ M := by
    intro y hy
    simpa only [Pi.sub_apply, dist_eq_norm] using (hn0 n hn m hm y hy).le
  have hd := poleBranch_fderiv_norm_le_inner_ball hrR hx ((hf n).sub (hf m)) hb
  have hxR := ball_subset_ball hrR.le hx
  rw [fderiv_sub ((hf n x hxR).differentiableAt (isOpen_ball.mem_nhds hxR))
    ((hf m x hxR).differentiableAt (isOpen_ball.mem_nhds hxR))] at hd
  rw [dist_eq_norm]
  calc
    _ ≤ 2 * M / (R - r) := hd
    _ = ε / 2 := by
      dsimp [M]
      field_simp [hgap.ne'] <;> ring
    _ < ε := by linarith

theorem dbarHolomorphic_uniform_limit_on_inner_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : ℕ → E → F} {g : E → F} {c : E} {r R : ℝ} (hrR : r < R)
    (hf : ∀ n, DifferentiableOn ℂ (f n) (ball c R))
    (hu : TendstoUniformlyOn f g atTop (ball c R)) :
    DifferentiableOn ℂ g (ball c r) := by
  obtain ⟨g', hg'⟩ := dbarUniformCauchy_exists_limit
    (dbarHolomorphic_derivative_uniformCauchy hrR hf hu.uniformCauchySeqOn)
  intro x hx
  have hder : HasFDerivAt g (g' x) x :=
    hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hg'
      (fun n y hy => ((hf n y (ball_subset_ball hrR.le hy)).differentiableAt
        (isOpen_ball.mem_nhds (ball_subset_ball hrR.le hy))).hasFDerivAt)
      (fun y hy => hu.tendsto_at (ball_subset_ball hrR.le hy)) hx
  exact hder.differentiableAt.differentiableWithinAt

end RepulsiveCoulomb
