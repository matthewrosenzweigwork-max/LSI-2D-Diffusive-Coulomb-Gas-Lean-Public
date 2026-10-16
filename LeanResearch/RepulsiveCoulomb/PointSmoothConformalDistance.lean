import LeanResearch.RepulsiveCoulomb.PointConformalDensity
import Mathlib.Geometry.Manifold.Riemannian.PathELength

/-! A smooth-path construction for the literal conformal density. We reuse Mathlib's
Riemannian path-length machinery, allowing a degenerate norm at the finitely many
punctures. Only extended pseudodistance identities are proved here. Separation,
completeness, local cone charts, and equality with the all-rectifiable-curve metric
are separate obligations; this module does not assert Bonk--Lang's theorem. -/
noncomputable section
open MeasureTheory Set Manifold
open scoped Manifold ENNReal
namespace RepulsiveCoulomb

/-- Tangent length is the physical Euclidean norm multiplied by sqrt(w). -/
@[instance_reducible] def pointConformalTangentENorm {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) :
    ∀ x : ℂ, ENorm (TangentSpace 𝓘(ℝ, ℂ) x) :=
  fun x ↦ ⟨fun v ↦ ENNReal.ofReal (pointConformalDensity a y x) * ENNReal.ofReal ‖NormedSpace.fromTangentSpace (𝕜 := ℝ) x v‖⟩

/-- Homogeneity remains valid at zero-density punctures. -/
theorem pointConformalTangentENorm_smul {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) :
    letI := pointConformalTangentENorm a y
    ∀ x : ℂ, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, ℂ) x) := by
  let := pointConformalTangentENorm a y
  intro x
  constructor
  intro r v
  change ENNReal.ofReal (pointConformalDensity a y x) * ENNReal.ofReal ‖NormedSpace.fromTangentSpace (𝕜 := ℝ) x (r • v)‖ =
    ‖r‖ₑ * (ENNReal.ofReal (pointConformalDensity a y x) * ENNReal.ofReal ‖NormedSpace.fromTangentSpace (𝕜 := ℝ) x v‖)
  rw [map_smul, norm_smul, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  ring

def pointSmoothConformalEDist {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (x z : ℂ) : ℝ≥0∞ :=
  letI := pointConformalTangentENorm a y
  riemannianEDist 𝓘(ℝ, ℂ) x z

def pointConformalPathELength {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) (s t : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Icc s t, ENNReal.ofReal (pointConformalDensity a y (γ u)) *
    ENNReal.ofReal ‖deriv γ u‖

theorem pointConformalPathELength_eq_manifold {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) (s t : ℝ) :
    pointConformalPathELength a y γ s t =
      letI := pointConformalTangentENorm a y
      pathELength 𝓘(ℝ, ℂ) γ s t := by
  let := pointConformalTangentENorm a y
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_congr
  intro u
  change ENNReal.ofReal (pointConformalDensity a y (γ u)) * ENNReal.ofReal ‖deriv γ u‖ =
    ENNReal.ofReal (pointConformalDensity a y (γ u)) * ENNReal.ofReal ‖NormedSpace.fromTangentSpace (𝕜 := ℝ) (γ u)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ u 1)‖
  rw [mfderiv_eq_fderiv]
  change _ = ENNReal.ofReal (pointConformalDensity a y (γ u)) * ENNReal.ofReal ‖fderiv ℝ γ u 1‖
  rfl

theorem pointSmoothConformalEDist_self {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (x : ℂ) : pointSmoothConformalEDist a y x x = 0 := by
  let := pointConformalTangentENorm a y
  let := pointConformalTangentENorm_smul a y
  exact riemannianEDist_self

theorem pointSmoothConformalEDist_comm {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (x z : ℂ) : pointSmoothConformalEDist a y x z = pointSmoothConformalEDist a y z x := by
  let := pointConformalTangentENorm a y
  let := pointConformalTangentENorm_smul a y
  exact riemannianEDist_comm

theorem pointSmoothConformalEDist_triangle {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (x z v : ℂ) : pointSmoothConformalEDist a y x v ≤
      pointSmoothConformalEDist a y x z + pointSmoothConformalEDist a y z v := by
  let := pointConformalTangentENorm a y
  let := pointConformalTangentENorm_smul a y
  exact riemannianEDist_triangle

theorem pointSmoothConformalEDist_le_path {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {γ : ℝ → ℂ} {s t : ℝ} (hγ : ContDiffOn ℝ 1 γ (Icc s t)) (hst : s ≤ t) :
    pointSmoothConformalEDist a y (γ s) (γ t) ≤ pointConformalPathELength a y γ s t := by
  let := pointConformalTangentENorm a y
  let := pointConformalTangentENorm_smul a y
  rw [pointConformalPathELength_eq_manifold]
  exact riemannianEDist_le_pathELength hγ.contMDiffOn rfl rfl hst

/-- The straight segment has finite weighted length, even if it crosses punctures. -/
theorem pointSmoothConformalEDist_segment_upper {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x z : ℂ) :
    pointSmoothConformalEDist a y x z ≤
      ENNReal.ofReal (Real.sqrt (rawPointBallFactor a y x ‖z - x‖)) *
      ENNReal.ofReal ‖z - x‖ := by
  let γ : ℝ → ℂ := fun t ↦ x + t • (z - x)
  have hγ : ContDiffOn ℝ 1 γ (Icc 0 1) := by fun_prop
  have hends := pointSmoothConformalEDist_le_path a y hγ (by norm_num : (0 : ℝ) ≤ 1)
  have h0 : γ 0 = x := by simp [γ]
  have h1 : γ 1 = z := by simp [γ]
  rw [h0, h1] at hends
  apply hends.trans
  have hd (t : ℝ) : deriv γ t = z - x := by
    have h : HasDerivAt γ (z - x) t := by
      simpa [γ] using ((hasDerivAt_id t).smul_const (z - x)).const_add x
    exact h.deriv
  have hc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ Metric.closedBall x ‖z - x‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    change ‖x + t • (z - x) - x‖ ≤ ‖z - x‖
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have hm : pointConformalPathELength a y γ 0 1 ≤
      ∫⁻ _t : ℝ in Icc (0 : ℝ) 1,
        ENNReal.ofReal (Real.sqrt (rawPointBallFactor a y x ‖z - x‖)) *
        ENNReal.ofReal ‖z - x‖ := by
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    rw [hd]
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact Real.sqrt_le_sqrt (rawPointWeight_le_ballFactor ha y x ‖z - x‖ (hc t ht))
  simpa using hm

theorem pointSmoothConformalEDist_lt_top {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x z : ℂ) :
    pointSmoothConformalEDist a y x z < ∞ :=
  (pointSmoothConformalEDist_segment_upper ha y x z).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

theorem exists_smooth_path_lt_pointConformalEDist {m : ℕ} (a : Fin m → ℝ)
    (y : Fin m → ℂ) {x z : ℂ} {r : ℝ≥0∞} (hr : pointSmoothConformalEDist a y x z < r) :
    ∃ γ : ℝ → ℂ, γ 0 = x ∧ γ 1 = z ∧ ContDiff ℝ 1 γ ∧
      pointConformalPathELength a y γ 0 1 < r := by
  let := pointConformalTangentENorm a y
  let := pointConformalTangentENorm_smul a y
  obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hr (by norm_num : (0 : ℝ) < 1)
  refine ⟨γ, h0, h1, ?_, ?_⟩
  · exact contMDiff_iff_contDiff.mp hγ
  · rwa [pointConformalPathELength_eq_manifold]

end RepulsiveCoulomb
