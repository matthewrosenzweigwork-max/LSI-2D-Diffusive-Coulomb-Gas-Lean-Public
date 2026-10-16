import LeanResearch.RepulsiveCoulomb.PointConeRadialMetric

/-! Principal-sector Euclidean developing map for the model density |z|^alpha.
This proves a branch-local exact length transformation; angular gluing into the
full cone and all-pairs intrinsic distance are separate obligations. -/
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

def pointConeSectorMap (α : ℝ) (z : ℂ) : ℂ :=
  z ^ ((α + 1 : ℝ) : ℂ) / ((α + 1 : ℝ) : ℂ)

theorem pointConeSectorMap_hasDerivAt {α : ℝ} (hα : 0 ≤ α) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) : HasDerivAt (pointConeSectorMap α) (z ^ (α : ℂ)) z := by
  have hn : ((α + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show α + 1 ≠ 0 by linarith)
  have h := ((hasDerivAt_id z).cpow_const (c := ((α + 1 : ℝ) : ℂ)) hz).div_const ((α + 1 : ℝ) : ℂ)
  convert h using 1
  · rfl
  · push_cast
    push_cast at hn
    field_simp
    simp

theorem pointConeSectorMap_norm_deriv {α : ℝ} (hα : 0 ≤ α) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) : ‖deriv (pointConeSectorMap α) z‖ = ‖z‖ ^ α := by
  rw [(pointConeSectorMap_hasDerivAt hα hz).deriv, Complex.norm_cpow_real]

theorem pointConeSectorMap_analyticOnNhd {α : ℝ} (hα : 0 ≤ α) :
    AnalyticOnNhd ℂ (pointConeSectorMap α) Complex.slitPlane := by
  apply DifferentiableOn.analyticOnNhd _ Complex.isOpen_slitPlane
  intro z hz
  exact (pointConeSectorMap_hasDerivAt hα hz).differentiableAt.differentiableWithinAt

theorem pointConeSectorMap_norm {α : ℝ} (hα : 0 ≤ α) (z : ℂ) :
    ‖pointConeSectorMap α z‖ = ‖z‖ ^ (α + 1) / (α + 1) := by
  rw [pointConeSectorMap, norm_div, Complex.norm_cpow_real, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith : 0 < α + 1)]

theorem pointConeSectorMap_preserves_path_length {α : ℝ} (hα : 0 ≤ α)
    {γ : ℝ → ℂ} {s t : ℝ} (hγ : ContDiffOn ℝ 1 γ (Icc s t))
    (hmap : MapsTo γ (Icc s t) Complex.slitPlane) :
    pointConformalPathELength (standardConeExponents α) standardConeLocations γ s t =
      ∫⁻ u in Icc s t, ‖deriv (pointConeSectorMap α ∘ γ) u‖ₑ := by
  apply pointConformal_chart_path_length (standardConeExponents α) standardConeLocations
    (U := Complex.slitPlane) (F := pointConeSectorMap α) _ hγ hmap
  intro z hz
  exact ⟨pointConeSectorMap_analyticOnNhd hα z hz,
    (pointConeSectorMap_norm_deriv hα hz).trans (standardCone_density α z).symm⟩

/-- One unwrapped angular sector, including the apex. The half-open convention
matches the principal argument; no global injectivity of the power map is claimed. -/
def pointConeSectorWindow (α : ℝ) : Set ℂ :=
  {z | -Real.pi < (α + 1) * Complex.arg z ∧ (α + 1) * Complex.arg z ≤ Real.pi}

def pointConeSectorInverse (α : ℝ) (w : ℂ) : ℂ :=
  (((α + 1 : ℝ) : ℂ) * w) ^ (((α + 1 : ℝ) : ℂ)⁻¹)

theorem pointConeSectorInverse_left {α : ℝ} (hα : 0 ≤ α) {z : ℂ}
    (hz : z ∈ pointConeSectorWindow α) :
    pointConeSectorInverse α (pointConeSectorMap α z) = z := by
  let n : ℂ := ((α + 1 : ℝ) : ℂ)
  have hn : n ≠ 0 := by dsimp [n]; exact_mod_cast (show α + 1 ≠ 0 by linarith)
  have hi : (Complex.log z * n).im = (α + 1) * Complex.arg z := by
    simp [n, Complex.mul_im, Complex.log_im, mul_comm]
  have hlt : -Real.pi < (Complex.log z * n).im := by rw [hi]; exact hz.1
  have hle : (Complex.log z * n).im ≤ Real.pi := by rw [hi]; exact hz.2
  change (n * (z ^ n / n)) ^ n⁻¹ = z
  have hcancel : n * (z ^ n / n) = z ^ n := by field_simp
  rw [hcancel, ← Complex.cpow_mul n⁻¹ hlt hle, mul_inv_cancel₀ hn, Complex.cpow_one]

theorem pointConeSectorMap_injOn {α : ℝ} (hα : 0 ≤ α) :
    Set.InjOn (pointConeSectorMap α) (pointConeSectorWindow α) := by
  intro z hz w hw he
  calc
    z = pointConeSectorInverse α (pointConeSectorMap α z) := (pointConeSectorInverse_left hα hz).symm
    _ = pointConeSectorInverse α (pointConeSectorMap α w) := congrArg _ he
    _ = w := pointConeSectorInverse_left hα hw

end RepulsiveCoulomb
