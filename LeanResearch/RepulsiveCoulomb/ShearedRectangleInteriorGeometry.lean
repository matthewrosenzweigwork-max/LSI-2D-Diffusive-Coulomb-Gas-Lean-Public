import LeanResearch.RepulsiveCoulomb.ShearedRectangleGeometry
import Mathlib.Analysis.Convex.Topology

/-!
NEW implementation from accepted flatShearedPoint/flatShearedRectangle and
recovered public callers. No historical source identity or historical compiler
pass is claimed. The coordinate homeomorphism is used only for topology;
all subset metrics remain the inherited Euclidean metric on ℂ.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- The actual shear in Euclidean complex coordinates. Nonzero imaginary
part is precisely the condition that the two real coordinate vectors span ℂ. -/
def flatShearHomeomorph {v : ℂ} (hvi : v.im ≠ 0) : (ℝ × ℝ) ≃ₜ ℂ where
  toFun q := flatShearedPoint v q.1 q.2
  invFun z := (z.re - (z.im / v.im) * v.re, z.im / v.im)
  left_inv := by
    rintro ⟨r, u⟩
    apply Prod.ext
    · simp [flatShearedPoint, hvi]
    · simp [flatShearedPoint, hvi]
  right_inv := by
    intro z
    apply Complex.ext
    · simp [flatShearedPoint]
    · simp [flatShearedPoint, hvi]
  continuous_toFun := by
    unfold flatShearedPoint
    fun_prop
  continuous_invFun := by fun_prop

/-- The interior has both coordinate inequalities strict. -/
theorem flatShearedRectangle_interior {v : ℂ} {R s : ℝ} (hvi : v.im ≠ 0) :
    interior (flatShearedRectangle v R s) =
      (fun q : ℝ × ℝ ↦ flatShearedPoint v q.1 q.2) ''
        (Ioo (0 : ℝ) R ×ˢ Ioo (0 : ℝ) s) := by
  rw [flatShearedRectangle_image]
  change interior ((flatShearHomeomorph hvi) '' (Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) s)) =
    (flatShearHomeomorph hvi) '' (Ioo (0 : ℝ) R ×ˢ Ioo (0 : ℝ) s)
  rw [← (flatShearHomeomorph hvi).image_interior, interior_prod_eq,
    interior_Icc, interior_Icc]

theorem flatShearedRectangle_interior_nonempty {v : ℂ} {R s : ℝ}
    (hvi : v.im ≠ 0) (hR : 0 < R) (hs : 0 < s) :
    (interior (flatShearedRectangle v R s)).Nonempty := by
  rw [flatShearedRectangle_interior hvi]
  refine ⟨flatShearedPoint v (R / 2) (s / 2), (R / 2, s / 2), ?_, rfl⟩
  exact ⟨⟨half_pos hR, half_lt_self hR⟩, ⟨half_pos hs, half_lt_self hs⟩⟩

/-- A nondegenerate closed sheared rectangle is the closure of its interior. -/
theorem flatShearedRectangle_closure_interior {v : ℂ} {R s : ℝ}
    (hvi : v.im ≠ 0) (hR : 0 < R) (hs : 0 < s) :
    closure (interior (flatShearedRectangle v R s)) = flatShearedRectangle v R s := by
  rw [(flatShearedRectangle_convex v R s).closure_interior_eq_closure_of_nonempty_interior
    (flatShearedRectangle_interior_nonempty hvi hR hs)]
  exact (flatShearedRectangle_compact v R s).isClosed.closure_eq

end RepulsiveCoulomb
