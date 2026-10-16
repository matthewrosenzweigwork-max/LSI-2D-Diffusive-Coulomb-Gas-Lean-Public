import LeanResearch.RepulsiveCoulomb.PointActualSectorStageGeometry
import LeanResearch.RepulsiveCoulomb.MetricSupportedFlatPatchCompatibility
import LeanResearch.RepulsiveCoulomb.EuclideanInteriorAngularWindow

/-! ISOLATED SOURCE-ONLY DRAFT. Stage compatibility is derived from the
actual shared chart seed and actual geometric stage-flatness theorem. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem zero_not_interior_of_subset_closedEuclideanSector
    {K : Set ℂ} {β : ℝ} (hK : K ⊆ closedEuclideanSector β) : (0 : ℂ) ∉ interior K := by
  intro hzero
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  let z : ℂ := (-ε / 2 : ℝ) * Complex.I
  have hzball : z ∈ ball (0 : ℂ) ε := by
    rw [mem_ball, dist_zero_right]
    simp only [z, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_neg (by linarith : -ε / 2 < 0)]
    linarith
  have him : 0 ≤ z.im := Complex.arg_nonneg_iff.mp (hK (hball hzball)).1
  have himval : z.im = -ε / 2 := by simp [z]
  rw [himval] at him
  linarith

namespace PointActualSectorData
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j} {P : Set ℂ}
    (D : PointActualSectorData a y ha P)

theorem stages_agree
    {K L : Set ℂ} (hK : Convex ℝ K) (hne : (interior K).Nonempty)
    (h0 : (0 : ℂ) ∈ K) (hKL : K ⊆ L)
    (hKsector : K ⊆ closedEuclideanSector D.beta)
    (hKarg : ∀ q : K, q.1 ≠ 0 → Complex.arg q.1 ∈ Ioo (0 : ℝ) D.beta)
    (f : K → P) (g : L → P)
    (hf : @Isometry K P (inferInstance : PseudoEMetricSpace K)
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace f)
    (hg : @Isometry L P (inferInstance : PseudoEMetricSpace L)
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace g)
    (hfseed : ∀ z : K, ‖z.1‖ ≤ D.chart.radius → (f z).1 = D.chart.flatInverse z.1)
    (hgseed : ∀ z : L, ‖z.1‖ ≤ D.chart.radius → (g z).1 = D.chart.flatInverse z.1) :
    ∀ z : K, f z = g ⟨z.1, hKL z.2⟩ := by
  classical
  letI : MetricSpace P := pointRegionMetricSpace ha y P
  letI : PseudoMetricSpace P := (pointRegionMetricSpace ha y P).toPseudoMetricSpace
  letI : EMetricSpace P := (pointRegionMetricSpace ha y P).toEMetricSpace
  letI : PseudoEMetricSpace P := (pointRegionMetricSpace ha y P).toPseudoEMetricSpace
  let F : ℂ → P := fun z ↦ if hz : z ∈ K then f ⟨z, hz⟩ else f ⟨0, h0⟩
  let G : ℂ → P := fun z ↦ if hz : z ∈ L then g ⟨z, hz⟩ else g ⟨0, hKL h0⟩
  have hF (z : ℂ) (hz : z ∈ K) : F z = f ⟨z, hz⟩ := by simp only [F, dif_pos hz]
  have hG (z : ℂ) (hz : z ∈ L) : G z = g ⟨z, hz⟩ := by simp only [G, dif_pos hz]
  have hdF : ∀ x ∈ K, ∀ z ∈ K, dist (F x) (F z) = dist x z := by
    intro x hx z hz
    rw [hF x hx, hF z hz]
    exact hf.dist_eq _ _
  have hdG : ∀ x ∈ K, ∀ z ∈ K, dist (G x) (G z) = dist x z := by
    intro x hx z hz
    rw [hG x (hKL hx), hG z (hKL hz)]
    exact hg.dist_eq _ _
  have hcharts : ∀ x ∈ interior K, ∃ p : P, ∃ C : MetricFlatDiskChart P p,
      F x ∈ ball p C.radius := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro he
      exact zero_not_interior_of_subset_closedEuclideanSector hKsector (he ▸ hx)
    obtain ⟨C⟩ := D.stage_flatDisk hK h0 hKsector hKarg f (fun x z ↦ hf.dist_eq x z)
      hfseed ⟨x, interior_subset hx⟩ hx0
    refine ⟨f ⟨x, interior_subset hx⟩, C, ?_⟩
    rw [hF x (interior_subset hx)]
    exact mem_ball_self C.radius_pos
  have hVne := convex_interior_inter_ball_nonempty hK hne h0 D.chart.radius_pos
  have hseed : EqOn F G (interior K ∩ ball (0 : ℂ) D.chart.radius) := by
    intro z hz
    have hzK := interior_subset hz.1
    rw [hF z hzK, hG z (hKL hzK)]
    apply Subtype.ext
    have hnorm : ‖z‖ ≤ D.chart.radius := by
      exact (show ‖z‖ < D.chart.radius by simpa only [mem_ball, dist_zero_right] using hz.2).le
    exact (hfseed ⟨z, hzK⟩ hnorm).trans (hgseed ⟨z, hKL hzK⟩ hnorm).symm
  have heq := flat_isometries_eqOn_convex_of_open_germ hK hne hdF hdG hcharts
    (isOpen_interior.inter isOpen_ball) hVne inter_subset_left hseed
  intro z
  simpa only [hF z.1 z.2, hG z.1 (hKL z.2)] using heq z.2

end PointActualSectorData
end RepulsiveCoulomb
