import LeanResearch.RepulsiveCoulomb.CoulombPhaseIdentity
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! Actual Euclidean-ball mean values in C^N from common-phase averaging.
Global continuity is available for the smooth mollifiers to which this input
will be applied; holomorphy is only required on the stated local ball. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombPhaseRotation_ball_preserving (N : ℕ) (c : Circle) (r : ℝ) :
    MeasurePreserving (coulombPhaseRotation N c)
      (volume.restrict (ball (0 : CoulombConfig N) r)) (volume.restrict (ball (0 : CoulombConfig N) r)) := by
  have h := (coulombPhaseRotation_volume_preserving N c).restrict_preimage
    (measurableSet_ball : MeasurableSet (ball (0 : CoulombConfig N) r))
  have he : coulombPhaseRotation N c ⁻¹' ball (0 : CoulombConfig N) r = ball (0 : CoulombConfig N) r := by
    ext z
    simp only [mem_preimage, mem_ball, dist_zero_right, (coulombPhaseRotation N c).norm_map]
  simpa only [he] using h

theorem coulombPhaseAction_integral_ball {N : ℕ} (r θ : ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : CoulombConfig N → F) :
    (∫ z in ball (0 : CoulombConfig N) r, f (coulombPhaseAction N θ z)) =
      ∫ z in ball (0 : CoulombConfig N) r, f z := by
  simp only [coulombPhaseAction_eq_rotation]
  exact (coulombPhaseRotation_ball_preserving N (Circle.exp θ) r).integral_comp
    (coulombPhaseRotation N (Circle.exp θ)).toMeasurableEquiv.measurableEmbedding f

theorem coulomb_local_phase_set_average {N : ℕ} {f : CoulombConfig N → ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball (0 : CoulombConfig N) R))
    (z : CoulombConfig N) (hz : z ∈ ball (0 : CoulombConfig N) R) :
    (2 * Real.pi)⁻¹ • (∫ θ in Ioc 0 (2 * Real.pi), f (coulombPhaseAction N θ z)) = f 0 := by
  have hmap : MapsTo (fun w : ℂ => w • z) (closedBall (0 : ℂ) 1) (ball (0 : CoulombConfig N) R) := by
    intro w hw
    have hw' : ‖w‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hw
    have hz' : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
    rw [mem_ball, dist_zero_right, norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg z) hw').trans_lt hz'
  have hd : DifferentiableOn ℂ (fun w : ℂ => f (w • z)) (closedBall (0 : ℂ) 1) :=
    hf.comp (differentiableOn_id.smul_const z) hmap
  have hd' : DiffContOnCl ℂ (fun w : ℂ => f (w • z)) (ball (0 : ℂ) |(1 : ℝ)|) := by
    simpa only [abs_one] using hd.diffContOnCl_ball
      (Subset.rfl : closedBall (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) 1)
  have ha := hd'.circleAverage (R := 1) (c := 0)
  rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity)] at ha
  simpa only [abs_one, zero_smul, circleMap, Complex.ofReal_one, one_mul, zero_add,
    coulombPhaseAction, Circle.coe_exp] using ha

theorem coulomb_phase_ball_product_integrable {N : ℕ} {f : CoulombConfig N → ℂ} (r : ℝ)
    (hc : Continuous f) (hi : Integrable f (volume.restrict (ball (0 : CoulombConfig N) r))) :
    Integrable (fun p : ℝ × CoulombConfig N => f (coulombPhaseAction N p.1 p.2))
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (ball (0 : CoulombConfig N) r))) := by
  have hj := hc.comp (coulombPhaseAction_continuous N)
  apply (integrable_prod_iff hj.aestronglyMeasurable).mpr
  constructor
  · apply Eventually.of_forall
    intro θ
    simp only [coulombPhaseAction_eq_rotation]
    exact (coulombPhaseRotation_ball_preserving N (Circle.exp θ) r).integrable_comp_of_integrable hi
  · have he : (fun θ : ℝ => ∫ z in ball (0 : CoulombConfig N) r,
        ‖f (coulombPhaseAction N θ z)‖) =
      fun _ : ℝ => ∫ z in ball (0 : CoulombConfig N) r, ‖f z‖ := by
      funext θ
      exact coulombPhaseAction_integral_ball r θ (fun z => ‖f z‖)
    simp only [Function.comp_apply]
    rw [he]
    exact integrable_const _

theorem coulomb_holomorphic_ball_integral {N : ℕ} {f : CoulombConfig N → ℂ} {r R : ℝ}
    (hrR : r ≤ R) (hc : Continuous f) (hf : DifferentiableOn ℂ f (ball (0 : CoulombConfig N) R))
    (hi : Integrable f (volume.restrict (ball (0 : CoulombConfig N) r))) :
    (∫ z in ball (0 : CoulombConfig N) r, f z) =
      volume.real (ball (0 : CoulombConfig N) r) • f 0 := by
  have hs := integral_integral_swap (f := fun θ z => f (coulombPhaseAction N θ z))
    (coulomb_phase_ball_product_integrable r hc hi)
  have ha : (2 * Real.pi)⁻¹ •
      (∫ θ in Ioc 0 (2 * Real.pi), ∫ z in ball (0 : CoulombConfig N) r,
        f (coulombPhaseAction N θ z)) =
      ∫ _z in ball (0 : CoulombConfig N) r, f 0 := by
    rw [hs, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact coulomb_local_phase_set_average hf z (ball_subset_ball hrR hz)
  simp_rw [coulombPhaseAction_integral_ball] at ha
  rw [← intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_const,
    sub_zero, smul_smul, inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul] at ha
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ] using ha

end RepulsiveCoulomb
