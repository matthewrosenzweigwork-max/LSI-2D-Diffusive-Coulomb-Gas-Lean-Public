module

public import LeanResearch.RepulsiveCoulomb.CoulombPotentialWeight
public import LeanResearch.RepulsiveCoulomb.HarmonicNormSquare

@[expose] public section

/-! Smooth strict complex-line subharmonicity of the canonical collision-complement exhaustion. -/
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

def coulombExhaustion {N : ℕ} (z : CoulombConfig N) : ℝ :=
  ‖z‖ ^ 2 + ‖(coulombVandermonde z)⁻¹‖ ^ 2

theorem coulombExhaustion_eq {N : ℕ} (z : CoulombConfig N) :
    coulombExhaustion z = ‖z‖ ^ 2 + (‖coulombVandermonde z‖ ^ 2)⁻¹ := by
  simp [coulombExhaustion, norm_inv, inv_pow]

theorem coulombExhaustion_contDiffAt {N : ℕ} {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) : ContDiffAt ℝ ⊤ (coulombExhaustion (N := N)) z := by
  have hi := (coulombVandermonde_contDiff_real N).contDiffAt.inv (show coulombVandermonde z ≠ 0 from hz)
  exact (contDiff_norm_sq ℝ).contDiffAt.add ((contDiff_norm_sq ℝ).contDiffAt.comp z hi)

theorem coulombExhaustion_line_laplacian_lower {N : ℕ} {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) (v : CoulombConfig N) :
    4 * ‖v‖ ^ 2 ≤ Laplacian.laplacian (fun t : ℂ => coulombExhaustion (z + t • v)) 0 := by
  have hv : coulombVandermonde (z + (0 : ℂ) • v) ≠ 0 := by
    simpa using (show coulombVandermonde z ≠ 0 from hz)
  have hi := ((coulombVandermonde_line_analyticAt z v 0).inv hv).harmonicAt
  have hn : ContDiffAt ℝ 2 (fun t : ℂ => ‖z + t • v‖ ^ 2) 0 := by
    have hc : ContDiff ℝ 2 (fun t : ℂ => z + t • v) := by fun_prop
    exact ((contDiff_norm_sq ℝ).comp hc).contDiffAt
  have hg : ContDiffAt ℝ 2 (fun t : ℂ => ‖(coulombVandermonde (z + t • v))⁻¹‖ ^ 2) 0 :=
    (contDiff_norm_sq ℝ).contDiffAt.comp 0 hi.1
  have he : (fun t : ℂ => coulombExhaustion (z + t • v)) =
      (fun t : ℂ => ‖z + t • v‖ ^ 2) +
        (fun t : ℂ => ‖(coulombVandermonde (z + t • v))⁻¹‖ ^ 2) := rfl
  rw [he, hn.laplacian_add hg, complex_affine_line_norm_sq_laplacian]
  have hpos := harmonic_norm_sq_laplacian_nonneg hi
  simp only [Pi.inv_apply] at hpos
  linarith

theorem coulombExhaustion_line_laplacian_pos {N : ℕ} {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) {v : CoulombConfig N} (hv : v ≠ 0) :
    0 < Laplacian.laplacian (fun t : ℂ => coulombExhaustion (z + t • v)) 0 := by
  have h := coulombExhaustion_line_laplacian_lower hz v
  have hn := sq_pos_of_pos (norm_pos_iff.mpr hv)
  linarith

end RepulsiveCoulomb
