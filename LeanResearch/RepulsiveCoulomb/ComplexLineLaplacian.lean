import LeanResearch.RepulsiveCoulomb.PointScoreLaplacian

/-! The real planar Laplacian of an affine complex line's squared Hilbert norm. -/
noncomputable section
open InnerProductSpace Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem complex_affine_line_norm_sq_laplacian {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (z v : E) (w : ℂ) :
    Laplacian.laplacian (fun q : ℂ => ‖z + q • v‖ ^ 2) w = 4 * ‖v‖ ^ 2 := by
  let q : ℂ → ℝ := fun t => ‖z‖ ^ 2 + 2 * (t * inner ℂ z v).re
  have hq : HarmonicAt q w := by
    have hh : HarmonicAt (fun t : ℂ => (t * inner ℂ z v).re) w :=
      (analyticAt_id.mul analyticAt_const).harmonicAt_re
    convert! (harmonicAt_const (‖z‖ ^ 2)).add (hh.const_smul (c := (2 : ℝ))) using 1
  have he : (fun t : ℂ => ‖z + t • v‖ ^ 2) =
      q + (‖v‖ ^ 2) • (fun t : ℂ => ‖t‖ ^ 2) := by
    funext t
    rw [norm_add_sq (𝕜 := ℂ)]
    simp only [q, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      inner_smul_right, norm_smul, mul_pow, RCLike.re_to_complex]
    ring
  have hb : ContDiffAt ℝ 2 (fun t : ℂ => ‖t‖ ^ 2) w := (contDiff_norm_sq ℝ).contDiffAt
  have hr : ContDiffAt ℝ 2 ((‖v‖ ^ 2) • (fun t : ℂ => ‖t‖ ^ 2)) w := by
    convert! hb.const_smul (‖v‖ ^ 2) using 1
  rw [he, hq.1.laplacian_add hr, laplacian_smul _ hb, complex_laplacian_norm_sq,
    hq.2.self_of_nhds]
  simp only [Pi.zero_apply, zero_add, smul_eq_mul]
  ring

end RepulsiveCoulomb
