import LeanResearch.RepulsiveCoulomb.LabeledCoulombModel
import LeanResearch.RepulsiveCoulomb.ComplexLineLaplacian

/-! The actual effective potential and its Levi quadratic form via complex lines. -/
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulombVandermonde_analyticAt {N : ℕ} (z : CoulombConfig N) :
    AnalyticAt ℂ (coulombVandermonde (N := N)) z := by
  unfold coulombVandermonde
  apply Finset.analyticAt_fun_prod
  intro p hp
  exact ((EuclideanSpace.proj (𝕜 := ℂ) p.1).analyticAt z).sub
    ((EuclideanSpace.proj (𝕜 := ℂ) p.2).analyticAt z)

theorem coulombVandermonde_line_analyticAt {N : ℕ} (z v : CoulombConfig N) (w : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => coulombVandermonde (z + t • v)) w := by
  have hs : AnalyticAt ℂ (fun t : ℂ => t • v) w := analyticAt_id.smul analyticAt_const
  have hl : AnalyticAt ℂ (fun t : ℂ => z + t • v) w := analyticAt_const.add hs
  exact (coulombVandermonde_analyticAt (z + w • v)).comp (f := fun t : ℂ => z + t • v) hl

theorem coulombVandermonde_line_log_harmonic {N : ℕ} {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) (v : CoulombConfig N) :
    HarmonicAt (fun t : ℂ => Real.log ‖coulombVandermonde (z + t • v)‖) 0 :=
  (coulombVandermonde_line_analyticAt z v 0).harmonicAt_log_norm (by change coulombVandermonde z ≠ 0 at hz; simpa using hz)

def coulombPotential {N : ℕ} (β : ℝ) (z : CoulombConfig N) : ℝ :=
  (β / 2) * ‖z‖ ^ 2 - (β / (N : ℝ)) * Real.log ‖coulombVandermonde z‖

def coulombLeviQuadratic {N : ℕ} (β : ℝ) (z v : CoulombConfig N) : ℝ :=
  Laplacian.laplacian (fun t : ℂ => coulombPotential β (z + t • v)) 0 / 4

theorem coulombPotential_line_laplacian {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) (v : CoulombConfig N) :
    Laplacian.laplacian (fun t : ℂ => coulombPotential β (z + t • v)) 0 = 2 * β * ‖v‖ ^ 2 := by
  have hg : ContDiffAt ℝ 2 (fun t : ℂ => ‖z + t • v‖ ^ 2) 0 := by
    have hc : ContDiff ℝ 2 (fun t : ℂ => z + t • v) := by fun_prop
    exact ((contDiff_norm_sq ℝ).comp hc).contDiffAt
  have hl := coulombVandermonde_line_log_harmonic hz v
  have hgs : ContDiffAt ℝ 2 ((β / 2) • (fun t : ℂ => ‖z + t • v‖ ^ 2)) 0 := by
    convert! hg.const_smul (β / 2) using 1
  have hls : ContDiffAt ℝ 2 ((β / (N : ℝ)) •
      (fun t : ℂ => Real.log ‖coulombVandermonde (z + t • v)‖)) 0 := by
    convert! hl.1.const_smul (β / (N : ℝ)) using 1
  have he : (fun t : ℂ => coulombPotential β (z + t • v)) =
      (β / 2) • (fun t : ℂ => ‖z + t • v‖ ^ 2) -
        (β / (N : ℝ)) • (fun t : ℂ => Real.log ‖coulombVandermonde (z + t • v)‖) := rfl
  rw [he, hgs.laplacian_sub hls, laplacian_smul _ hg, laplacian_smul _ hl.1,
    complex_affine_line_norm_sq_laplacian, hl.2.self_of_nhds]
  simp only [Pi.zero_apply, smul_eq_mul]
  ring

theorem coulombLeviQuadratic_eq {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) (v : CoulombConfig N) :
    coulombLeviQuadratic β z v = (β / 2) * ‖v‖ ^ 2 := by
  rw [coulombLeviQuadratic, coulombPotential_line_laplacian β hz v]
  ring

theorem coulombLeviQuadratic_pos {N : ℕ} {β : ℝ} (hβ : 0 < β) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) {v : CoulombConfig N} (hv : v ≠ 0) :
    0 < coulombLeviQuadratic β z v := by
  rw [coulombLeviQuadratic_eq β hz v]
  exact mul_pos (by positivity) (sq_pos_of_pos (norm_pos_iff.mpr hv))

end RepulsiveCoulomb
