module

public import LeanResearch.RepulsiveCoulomb.PointGeodesicStarGerms
public import LeanResearch.RepulsiveCoulomb.PointMetricLineNormalizedChart

@[expose] public section

/-! Isolated, uncompiled author draft. A small wrapper around the actually
constructed full metric cone disk. Its fields are proved by the existing
cone-chart theorem; no occupied interval or embedding data are stored. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

structure PointFlatLinkConeDisk {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (p : ℂ) where
  chart : OpenPartialHomeomorph ℂ ℂ
  radius : ℝ
  radius_pos : 0 < radius
  center : chart p = 0
  source : {z | (pointSmoothConformalEDist a y z p).toReal ≤ radius} ⊆ chart.source
  onto : BijOn chart {z | (pointSmoothConformalEDist a y z p).toReal ≤ radius}
    {w : ℂ | ‖w‖ ≤ radius}
  metric : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ radius →
    ∀ w, (pointSmoothConformalEDist a y w p).toReal ≤ radius →
    (pointSmoothConformalEDist a y z w).toReal = pointClassicalConeDist a y p (chart z) (chart w)

theorem exists_pointFlatLinkConeDisk {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    Nonempty (PointFlatLinkConeDisk a y p) := by
  obtain ⟨e, R, hR, h0, hsource, honto, hmetric⟩ :=
    exists_pointConformal_classical_cone_disk ha y p
  exact ⟨⟨e, R, hR, h0, hsource, honto, hmetric⟩⟩

namespace PointFlatLinkConeDisk
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}

@[simp] theorem center_mem (C : PointFlatLinkConeDisk a y p) : p ∈ C.chart.source := by
  apply C.source
  simp only [mem_setOf_eq, pointSmoothConformalEDist_self, ENNReal.toReal_zero]
  exact C.radius_pos.le

theorem norm_chart (C : PointFlatLinkConeDisk a y p) {z : ℂ}
    (hz : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius) :
    ‖C.chart z‖ = (pointSmoothConformalEDist a y z p).toReal := by
  have hp : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    simp only [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  rw [C.metric z hz p hp, C.center, pointClassicalConeDist_apex]

/-- The normalization is an actual rotation of the actual chart. It preserves
its whole disk and all point-metric pair identities, including exponent zero. -/
def rotate (C : PointFlatLinkConeDisk a y p) (θ : ℝ) : PointFlatLinkConeDisk a y p where
  chart := C.chart.trans
    (Homeomorph.mulLeft₀ (conePhase θ) (Complex.exp_ne_zero _)).toOpenPartialHomeomorph
  radius := C.radius
  radius_pos := C.radius_pos
  center := by change conePhase θ * C.chart p = 0; rw [C.center, mul_zero]
  source := by simpa using C.source
  onto := by
    have hrot : BijOn (fun z : ℂ ↦ conePhase θ * z)
        {w : ℂ | ‖w‖ ≤ C.radius} {w : ℂ | ‖w‖ ≤ C.radius} := by
      refine ⟨?_, fun _ _ _ _ h ↦ mul_left_cancel₀ (Complex.exp_ne_zero _) h, ?_⟩
      · intro w hw
        simpa only [mem_setOf_eq, norm_mul, conePhase_norm, one_mul] using hw
      · intro w hw
        refine ⟨(conePhase θ)⁻¹ * w, ?_, ?_⟩
        · simpa only [mem_setOf_eq, norm_mul, norm_inv, conePhase_norm, inv_one,
            one_mul] using hw
        · exact mul_inv_cancel_left₀ (Complex.exp_ne_zero _) w
    exact hrot.comp C.onto
  metric := by
    intro z hz w hw
    change (pointSmoothConformalEDist a y z w).toReal =
      pointClassicalConeDist a y p (conePhase θ * C.chart z) (conePhase θ * C.chart w)
    rw [pointClassicalConeDist_rotation a y p (conePhase_norm θ)]
    exact C.metric z hz w hw

@[simp] theorem rotate_apply (C : PointFlatLinkConeDisk a y p) (θ : ℝ) (z : ℂ) :
    (C.rotate θ).chart z = conePhase θ * C.chart z := rfl

end PointFlatLinkConeDisk
end RepulsiveCoulomb
