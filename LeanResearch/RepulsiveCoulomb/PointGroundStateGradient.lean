import LeanResearch.RepulsiveCoulomb.PointGroundStateCore

/-! Actual physical gradient identity for the normalized ground-state transform. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointDensity_hasFDerivAt {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ}
    (hz : z ∉ pointPunctures a y) :
    HasFDerivAt (pointDensity γ a y)
      (pointDensity γ a y z • innerSL ℝ (-pointScore γ a y z)) z := by
  let c : ℝ := (∫ x : ℂ, pointWeight γ a y x)⁻¹
  have h := ((hasFDerivAt_pointLogWeight γ ha y hz).exp).const_mul c
  have he : pointDensity γ a y =ᶠ[𝓝 z] (fun x => c * Real.exp (pointLogWeight γ a y x)) := by
    filter_upwards [(pointDomain a y).isOpen.mem_nhds hz] with x hx
    rw [exp_pointLogWeight_off_punctures γ ha y hx]
    rfl
  have h' := h.congr_of_eventuallyEq he
  simpa only [smul_smul, exp_pointLogWeight_off_punctures γ ha y hz, c, pointDensity] using h'

theorem pointSqrtDensity_hasFDerivAt {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ}
    (hz : z ∉ pointPunctures a y) :
    HasFDerivAt (fun x => Real.sqrt (pointDensity γ a y x))
      ((Real.sqrt (pointDensity γ a y z) / 2) • innerSL ℝ (-pointScore γ a y z)) z := by
  have hp := pointDensity_pos_off_punctures hγ ha y hz
  have h := (pointDensity_hasFDerivAt γ ha y hz).sqrt hp.ne'
  have hs : 0 < Real.sqrt (pointDensity γ a y z) := Real.sqrt_pos.mpr hp
  have hc : (1 / (2 * Real.sqrt (pointDensity γ a y z))) * pointDensity γ a y z =
      Real.sqrt (pointDensity γ a y z) / 2 := by
    have hsq := Real.sq_sqrt hp.le
    field_simp
    nlinarith
  simpa only [smul_smul, hc] using h

theorem pointSqrtDensity_gradient {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ}
    (hz : z ∉ pointPunctures a y) :
    gradient (fun x => Real.sqrt (pointDensity γ a y x)) z =
      (Real.sqrt (pointDensity γ a y z) / 2) • (-pointScore γ a y z) := by
  apply (InnerProductSpace.toDual ℝ ℂ).injective
  rw [toDual_gradient, (pointSqrtDensity_hasFDerivAt hγ ha y hz).fderiv, map_smul]
  rfl

theorem pointGroundStateCore_gradient_identity {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) (z : ℂ) :
    Real.sqrt (pointDensity γ a y z) • gradient (φ : ℂ → ℝ) z =
      gradient (pointGroundStateCore hγ ha y φ : ℂ → ℝ) z +
        (pointGroundStateCore hγ ha y φ z / 2) • pointScore γ a y z := by
  by_cases hz : z ∉ pointPunctures a y
  · change Real.sqrt (pointDensity γ a y z) • gradient (φ : ℂ → ℝ) z =
      gradient (fun x => φ x * Real.sqrt (pointDensity γ a y x)) z +
        (φ z * Real.sqrt (pointDensity γ a y z) / 2) • pointScore γ a y z
    rw [physical_gradient_mul (φ.contDiff.differentiable (by simp) z)
      (pointSqrtDensity_hasFDerivAt hγ ha y hz).differentiableAt,
      pointSqrtDensity_gradient hγ ha y hz]
    module
  · have hn : z ∉ tsupport (φ : ℂ → ℝ) := fun ht => hz (φ.tsupport_subset ht)
    have hn' : z ∉ tsupport (pointGroundStateCore hγ ha y φ : ℂ → ℝ) :=
      fun ht => hz ((pointGroundStateCore hγ ha y φ).tsupport_subset ht)
    rw [TauCeti.gradient_of_notMem_tsupport hn, TauCeti.gradient_of_notMem_tsupport hn',
      image_eq_zero_of_notMem_tsupport hn']
    simp

end RepulsiveCoulomb
