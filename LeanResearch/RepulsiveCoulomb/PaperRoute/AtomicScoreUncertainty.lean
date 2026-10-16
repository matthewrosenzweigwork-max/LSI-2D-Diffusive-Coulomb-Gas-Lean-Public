module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.AtomicScoreAnnularMoment
public import LeanResearch.RepulsiveCoulomb.PointScoreCoreIntegrability

@[expose] public section

/-! Actual uncertainty on the original puncture-avoiding smooth core.
The cutoff bound is chosen before the configuration. The newly produced
U=96/gamma^2+1152*K^2+2+1152*K^2*Ccut^2 uses the new K only.

Proof bodies are adapted from the corresponding frozen score/annular/moment
modules. This new application replaces every hardwired old weak-force, bad-area,
uncertainty and moment producer with the new finite-atomic maximal route.
Generic cutoff, overlap, integrability, ground-state and Fatou identities are
reused unchanged; actual proof-body dependencies are audited separately. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem atomic_pointScore_uncertainty {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ U : ℝ, 0 < U ∧ ∀ (m : ℕ) (a : Fin m → ℝ), (∀ j, 0 ≤ a j) →
    ∀ y : Fin m → ℂ, (∑ j, a j ≤ Q) →
    ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
    (∫ x : ℂ, ‖x‖ ^ 2 * φ x ^ 2) ≤ U *
      ((∫ x : ℂ, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2) +
        (∫ x : ℂ, ‖pointScore γ a y x‖ ^ 2 * φ x ^ 2) + (∫ x : ℂ, φ x ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := exists_annularCutoff_gradient_bound
  let K := atomicScoreAnnularMassConstant γ Q
  let U := 96 / γ ^ 2 + 1152 * K ^ 2 + 2 + 1152 * K ^ 2 * C ^ 2
  have hU : 0 < U := by dsimp only [U]; positivity
  refine ⟨U, hU, ?_⟩
  intro m a ha y hQ φ
  have hp : HasCompactSupport (fun x : ℂ => φ x ^ 2) :=
    φ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hmass : Integrable (fun x : ℂ => φ x ^ 2) :=
    (φ.continuous.pow 2).integrable_of_hasCompactSupport hp
  have hmoment : Integrable (fun x : ℂ => ‖x‖ ^ 2 * φ x ^ 2) :=
    ((continuous_norm.pow 2).mul (φ.continuous.pow 2)).integrable_of_hasCompactSupport hp.mul_left
  have hgc := TauCeti.continuous_gradient_testFunction φ
  have hgs := TauCeti.hasCompactSupport_gradient_testFunction φ
  change Continuous (fun x : ℂ => gradient (φ : ℂ → ℝ) x) at hgc
  change HasCompactSupport (fun x : ℂ => gradient (φ : ℂ → ℝ) x) at hgs
  have hgs2 : HasCompactSupport (fun x : ℂ => ‖gradient (φ : ℂ → ℝ) x‖ ^ 2) :=
    hgs.comp_left (g := fun v : ℂ => ‖v‖ ^ 2) (by simp)
  have henergy : Integrable (fun x : ℂ => ‖gradient (φ : ℂ → ℝ) x‖ ^ 2) :=
    (hgc.norm.pow 2).integrable_of_hasCompactSupport hgs2
  have hscore := pointCore_score_energy_integrable γ ha y φ
  obtain ⟨N, hN⟩ := pointCore_exists_dyadic_outer_radius a y φ
  have h := atomic_pointScore_finite_moment_bound hγ hC.le hb ha y hQ (φ : ℂ → ℝ)
    (φ.contDiff.of_le (by simp)) hmass henergy hmoment hscore N hN
  have hM : 0 ≤ ∫ x : ℂ, φ x ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hE : 0 ≤ ∫ x : ℂ, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hS : 0 ≤ ∫ x : ℂ, ‖pointScore γ a y x‖ ^ 2 * φ x ^ 2 :=
    integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have h1 : 96 / γ ^ 2 ≤ U := by
    dsimp only [U]
    have : 0 ≤ 1152 * K ^ 2 := by positivity
    have : 0 ≤ 1152 * K ^ 2 * C ^ 2 := by positivity
    linarith
  have h2 : 1152 * K ^ 2 ≤ U := by
    dsimp only [U]
    have : 0 ≤ 96 / γ ^ 2 := by positivity
    have : 0 ≤ 1152 * K ^ 2 * C ^ 2 := by positivity
    linarith
  have h3 : 2 + 1152 * K ^ 2 * C ^ 2 ≤ U := by
    dsimp only [U]
    have : 0 ≤ 96 / γ ^ 2 := by positivity
    have : 0 ≤ 1152 * K ^ 2 := by positivity
    linarith
  have hs := mul_le_mul_of_nonneg_right h1 hS
  have he := mul_le_mul_of_nonneg_right h2 hE
  have hm := mul_le_mul_of_nonneg_right h3 hM
  change (∫ x : ℂ, ‖x‖ ^ 2 * φ x ^ 2) ≤ U * _
  change (∫ x : ℂ, ‖x‖ ^ 2 * φ x ^ 2) ≤
    (96 / γ ^ 2) * _ + 1152 * K ^ 2 * _ + (2 + 1152 * K ^ 2 * C ^ 2) * _ at h
  nlinarith only [h, hs, he, hm]

end RepulsiveCoulomb.PaperRoute
