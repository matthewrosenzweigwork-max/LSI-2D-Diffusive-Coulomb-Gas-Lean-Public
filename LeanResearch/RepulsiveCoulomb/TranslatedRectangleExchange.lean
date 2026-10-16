import LeanResearch.RepulsiveCoulomb.ShearedRectangleGeometry

/-! ISOLATED SOURCE-ONLY DRAFT. The actual Euclidean reflection exchanging
longitudinal and transverse arclength coordinates. It lets compact-top
continuation advance the escaping-ray direction at a fixed uniform width. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- Reflection in the bisector of the two unit coordinate rays. -/
def shearedCoordinateExchange (v : ℂ) (hv : ‖v‖ = 1) : ℂ ≃ᵢ ℂ := by
  have hunit : v * star v = 1 := by
    simpa only [Complex.star_def, hv, one_pow, Complex.ofReal_one] using Complex.mul_conj' v
  let F : ℂ → ℂ := fun z ↦ v * star z
  have hFF : Function.Involutive F := by
    intro z
    change v * star (v * star z) = z
    rw [star_mul, star_star]
    calc
      v * (z * star v) = (v * star v) * z := by ring
      _ = z := by rw [hunit, one_mul]
  have hF : Isometry F := by
    apply Isometry.of_dist_eq
    intro z w
    rw [dist_eq_norm, dist_eq_norm]
    change ‖v * star z - v * star w‖ = ‖z - w‖
    rw [← mul_sub, ← star_sub, norm_mul, hv, one_mul]
    simpa only [Complex.star_def] using Complex.norm_conj (z - w)
  exact { toFun := F, invFun := F, left_inv := hFF, right_inv := hFF, isometry_toFun := hF }

@[simp] theorem shearedCoordinateExchange_point {v : ℂ} (hv : ‖v‖ = 1) (r u : ℝ) :
    shearedCoordinateExchange v hv (flatShearedPoint v r u) = flatShearedPoint v u r := by
  have hunit : v * star v = 1 := by
    simpa only [Complex.star_def, hv, one_pow, Complex.ofReal_one] using Complex.mul_conj' v
  change v * star ((r : ℂ) + (u : ℂ) * v) = (u : ℂ) + (r : ℂ) * v
  simp only [star_add, star_mul, Complex.star_def, Complex.conj_ofReal]
  calc
    v * ((r : ℂ) + star v * (u : ℂ)) = (r : ℂ) * v + (v * star v) * (u : ℂ) := by ring
    _ = (u : ℂ) + (r : ℂ) * v := by rw [hunit, one_mul]; ring

/-- A genuine Euclidean isometry between the exchanged rectangles. -/
def shearedRectangleExchange {v : ℂ} (hv : ‖v‖ = 1) (R s : ℝ) :
    flatShearedRectangle v R s ≃ᵢ flatShearedRectangle v s R := by
  have hmem {R s : ℝ} {z : ℂ} (hz : z ∈ flatShearedRectangle v R s) :
      shearedCoordinateExchange v hv z ∈ flatShearedRectangle v s R := by
    obtain ⟨r, hr, u, hu, rfl⟩ := hz
    rw [shearedCoordinateExchange_point]
    exact ⟨u, hu, r, hr, rfl⟩
  let F : flatShearedRectangle v R s → flatShearedRectangle v s R :=
    fun z ↦ ⟨shearedCoordinateExchange v hv z.1, hmem z.2⟩
  let G : flatShearedRectangle v s R → flatShearedRectangle v R s :=
    fun z ↦ ⟨shearedCoordinateExchange v hv z.1, hmem z.2⟩
  refine { toFun := F, invFun := G, left_inv := ?_, right_inv := ?_, isometry_toFun := ?_ }
  · intro z
    apply Subtype.ext
    exact (shearedCoordinateExchange v hv).symm_apply_apply z.1
  · intro z
    apply Subtype.ext
    exact (shearedCoordinateExchange v hv).apply_symm_apply z.1
  · apply Isometry.of_dist_eq
    intro z w
    exact (shearedCoordinateExchange v hv).dist_eq z.1 w.1

end RepulsiveCoulomb
