module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.AtomicMaximalWeakForce
public import LeanResearch.RepulsiveCoulomb.PointScoreAnnulus

@[expose] public section

/-! Actual bad-score region area from the new W=64*pi atomic-maximal force bound.
The new area constant is 4*W*Q^2/gamma^2 = 256*pi*Q^2/gamma^2.

Proof bodies are adapted from the corresponding frozen score/annular/moment
modules. This new application replaces every hardwired old weak-force, bad-area,
uncertainty and moment producer with the new finite-atomic maximal route.
Generic cutoff, overlap, integrability, ground-state and Fatou identities are
reused unchanged; actual proof-body dependencies are audited separately. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem atomic_pointScore_small_region_measure {m : ℕ} {γ Q R : ℝ} (hγ : 0 < γ) (hR : 0 < R)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hQ : ∑ j, a j ≤ Q) :
    volume {z : ℂ | R ≤ ‖z‖ ∧ ‖pointScore γ a y z‖ < γ * R / 2} ≤
      ENNReal.ofReal (256 * Real.pi * Q ^ 2 / (γ ^ 2 * R ^ 2)) := by
  have ht : 0 < γ * R / 2 := by positivity
  have hsubset : {z : ℂ | R ≤ ‖z‖ ∧ ‖pointScore γ a y z‖ < γ * R / 2} ⊆
      {z : ℂ | γ * R / 2 < ‖pointLogForce a y z‖} := by
    intro z hz
    have h := norm_add_le (pointScore γ a y z) (pointLogForce a y z)
    have hid : pointScore γ a y z + pointLogForce a y z = γ • z := sub_add_cancel _ _
    rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos hγ] at h
    have hr := mul_le_mul_of_nonneg_left hz.1 hγ.le
    change γ * R / 2 < ‖pointLogForce a y z‖
    linarith [hz.2]
  apply (measure_mono hsubset).trans
  convert pointLogForce_weak_l2_atomic_maximal_of_total_le ha y hQ ht using 1
  congr 1
  field_simp
  ring

def atomicScoreBadAreaConstant (γ Q : ℝ) : ℝ := 256 * Real.pi * Q ^ 2 / γ ^ 2

theorem atomicScoreBadAreaConstant_nonneg (γ Q : ℝ) : 0 ≤ atomicScoreBadAreaConstant γ Q := by
  unfold atomicScoreBadAreaConstant
  positivity

theorem atomic_pointScoreBadAnnulus_volume_le {m : ℕ} {γ Q R : ℝ} (hγ : 0 < γ) (hR : 0 < R)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hQ : ∑ j, a j ≤ Q) :
    volume (pointScoreBadAnnulus γ a y R) ≤ ENNReal.ofReal (atomicScoreBadAreaConstant γ Q / R ^ 2) := by
  have hsub : pointScoreBadAnnulus γ a y R ⊆
      {z : ℂ | R ≤ ‖z‖ ∧ ‖pointScore γ a y z‖ < γ * R / 2} := fun z hz => ⟨hz.1, hz.2.2⟩
  have h := (measure_mono hsub).trans (atomic_pointScore_small_region_measure hγ hR ha y hQ)
  convert h using 1
  congr 1
  unfold atomicScoreBadAreaConstant
  ring

theorem atomic_pointScoreBadAnnulus_volume_ne_top {m : ℕ} {γ Q R : ℝ} (hγ : 0 < γ) (hR : 0 < R)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hQ : ∑ j, a j ≤ Q) :
    volume (pointScoreBadAnnulus γ a y R) ≠ ⊤ :=
  ((atomic_pointScoreBadAnnulus_volume_le hγ hR ha y hQ).trans_lt ENNReal.ofReal_lt_top).ne

theorem atomic_pointScoreBadAnnulus_real_volume_le {m : ℕ} {γ Q R : ℝ} (hγ : 0 < γ) (hR : 0 < R)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hQ : ∑ j, a j ≤ Q) :
    volume.real (pointScoreBadAnnulus γ a y R) ≤ atomicScoreBadAreaConstant γ Q / R ^ 2 :=
  ENNReal.toReal_le_of_le_ofReal (div_nonneg (atomicScoreBadAreaConstant_nonneg γ Q) (sq_nonneg R))
    (atomic_pointScoreBadAnnulus_volume_le hγ hR ha y hQ)

end RepulsiveCoulomb.PaperRoute
