module

public import LeanResearch.RepulsiveCoulomb.PointFormMomentApproximation

@[expose] public section

/-! Fatou closure of the actual weighted moment bound. Finiteness is proved in
ENNReal before the real Bochner integral is used. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped Topology BigOperators ENNReal
namespace RepulsiveCoulomb

theorem pointForm_moment_bound_of_core {m : ℕ} {γ C : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hC : 0 ≤ C)
    (hcore : ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      (∫ x, ‖x‖ ^ 2 * φ x ^ 2 ∂pointMeasure γ a y) ≤ C *
        ((∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
          (∫ x, φ x ^ 2 ∂pointMeasure γ a y)))
    (u : PointFormDomain hγ ha y) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2 * (pointFormValueL hγ ha y u x) ^ 2) (pointMeasure γ a y) ∧
      (∫ x, ‖x‖ ^ 2 * (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y) ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨φ, hφ⟩ := pointFormCore_approximation hγ ha y u
  let v := pointFormValueL hγ ha y u
  have hv : Tendsto (fun n => pointFormValueL hγ ha y (pointFormCore hγ ha y (φ n))) atTop (𝓝 v) :=
    ((pointFormValueL hγ ha y).continuous.tendsto u).comp hφ
  have hinm : TendstoInMeasure (pointMeasure γ a y) (fun n => (φ n : ℂ → ℝ)) atTop v :=
    TendstoInMeasure.congr_left (fun n => pointFormCore_value hγ ha y (φ n))
      (tendstoInMeasure_of_tendsto_Lp hv)
  obtain ⟨ns, hns, hae⟩ := hinm.exists_seq_tendsto_ae
  have hF (n : ℕ) : AEMeasurable
      (fun x : ℂ => ENNReal.ofReal (‖x‖ ^ 2 * φ (ns n) x ^ 2)) (pointMeasure γ a y) :=
    ((continuous_norm.pow 2).mul ((φ (ns n)).continuous.pow 2)).measurable.ennreal_ofReal.aemeasurable
  have hlim : ∀ᵐ x ∂pointMeasure γ a y,
      Tendsto (fun n => ENNReal.ofReal (‖x‖ ^ 2 * φ (ns n) x ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (‖x‖ ^ 2 * v x ^ 2))) := by
    filter_upwards [hae] with x hx
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.mul (hx.pow 2))
  have hbound : ∀ᶠ n in atTop,
      (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2 * φ (ns n) x ^ 2) ∂pointMeasure γ a y) ≤
        ENNReal.ofReal (C * ‖pointFormCore hγ ha y (φ (ns n))‖ ^ 2) := by
    apply Eventually.of_forall
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (pointCore_moment_integrable hγ ha y (φ (ns n)))
      (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)))]
    have h := hcore (φ (ns n))
    rw [← pointFormCore_norm_sq_eq_integrals hγ ha y (φ (ns n))] at h
    exact ENNReal.ofReal_le_ofReal h
  have hb : Tendsto (fun n => ENNReal.ofReal (C * ‖pointFormCore hγ ha y (φ (ns n))‖ ^ 2))
      atTop (𝓝 (ENNReal.ofReal (C * ‖u‖ ^ 2))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul (((hφ.comp hns.tendsto_atTop).norm).pow 2))
  have hfatou := lintegral_le_of_ae_tendsto_of_eventually_bound (pointMeasure γ a y) hF hlim hbound hb
  have hmeas : AEStronglyMeasurable (fun x : ℂ => ‖x‖ ^ 2 * v x ^ 2) (pointMeasure γ a y) :=
    (continuous_norm.pow 2).aestronglyMeasurable.mul ((Lp.aestronglyMeasurable v).pow 2)
  have hnonneg : 0 ≤ᵐ[pointMeasure γ a y] (fun x : ℂ => ‖x‖ ^ 2 * v x ^ 2) :=
    Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hi : Integrable (fun x : ℂ => ‖x‖ ^ 2 * v x ^ 2) (pointMeasure γ a y) :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp
      (ne_of_lt (hfatou.trans_lt ENNReal.ofReal_lt_top))
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg] at hfatou
  exact ⟨hi, (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (sq_nonneg ‖u‖))).mp hfatou⟩

end RepulsiveCoulomb
