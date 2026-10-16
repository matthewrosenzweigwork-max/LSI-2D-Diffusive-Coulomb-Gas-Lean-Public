module

public import LeanResearch.RepulsiveCoulomb.CoulombConstantDomain

@[expose] public section

/-! Bounded globally smooth functions with bounded physical gradient belong to
 the original closed Coulomb form domain. The proof uses ambient compact
 cutoffs, whose jets already lie in the closure of the puncture-avoiding core. -/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology
namespace RepulsiveCoulomb

def coulombBoundedSmoothCutoff (N n : ℕ) (f : CoulombConfig (N + 2) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : TestFunction (⊤ : Opens (CoulombConfig (N + 2))) ℝ ⊤ :=
  ⟨fun z ↦ coulombOuterTestFunction N n z * f z,
    (coulombOuterTestFunction N n).contDiff.mul hf,
    (coulombOuterTestFunction N n).hasCompactSupport.mul_right, by simp⟩

theorem coulombBoundedSmoothCutoff_gradient (N n : ℕ)
    (f : CoulombConfig (N + 2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (z : CoulombConfig (N + 2)) :
    gradient (coulombBoundedSmoothCutoff N n f hf : CoulombConfig (N + 2) → ℝ) z =
      coulombOuterTestFunction N n z • gradient f z +
        f z • gradient (coulombOuterTestFunction N n : CoulombConfig (N + 2) → ℝ) z := by
  apply (InnerProductSpace.toDual ℝ (CoulombConfig (N + 2))).injective
  simp only [toDual_gradient, map_add, map_smul]
  exact fderiv_fun_mul ((coulombOuterTestFunction N n).contDiff.differentiable (by simp) z)
    (hf.differentiable (by simp) z)

theorem coulombOuterTestFunction_gradient_tendsto_zero (N : ℕ)
    (z : CoulombConfig (N + 2)) :
    Tendsto (fun n ↦ gradient (coulombOuterTestFunction N n : CoulombConfig (N + 2) → ℝ) z)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hc⟩ := coulombOuterBump_gradient_bound N
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (g := fun n ↦ C / pointOuterRadius n) (fun n ↦ norm_nonneg _)
  · intro n
    exact hc (pointOuterRadius n) (pointOuterRadius_pos n) z
  · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    simpa [pointOuterRadius, div_eq_mul_inv] using h

theorem coulombBoundedSmoothCutoff_L2_error (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : CoulombConfig (N + 2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B : ℝ) (hb : ∀ z, |f z| ≤ B) :
    Tendsto (fun n ↦ ∫ z, (coulombBoundedSmoothCutoff N n f hf z - f z) ^ 2
      ∂coulombMeasure (N + 2) β) atTop (𝓝 0) := by
  let _ := coulombMeasure_isProbability (N := N + 2) hβ
  have hB : 0 ≤ B := (abs_nonneg (f 0)).trans (hb 0)
  have h := tendsto_integral_of_dominated_convergence (μ := coulombMeasure (N + 2) β)
    (F := fun n z ↦ (coulombBoundedSmoothCutoff N n f hf z - f z) ^ 2)
    (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ B ^ 2)
    (fun n ↦ ((coulombBoundedSmoothCutoff N n f hf).continuous.sub hf.continuous).pow 2 |>.aestronglyMeasurable)
    (integrable_const _) ?_ ?_
  · simpa only [integral_zero] using h
  · intro n
    exact Eventually.of_forall fun z ↦ by
      have h0 := (coulombOuterBump N (pointOuterRadius n) (pointOuterRadius_pos n)).nonneg (x := z)
      have h1 := (coulombOuterBump N (pointOuterRadius n) (pointOuterRadius_pos n)).le_one (x := z)
      have hv := hb z
      have hq : |coulombOuterTestFunction N n z - 1| ≤ 1 := by
        change |coulombOuterBump N (pointOuterRadius n) (pointOuterRadius_pos n) z - 1| ≤ 1
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have he : |coulombBoundedSmoothCutoff N n f hf z - f z| ≤ B := by
        change |coulombOuterTestFunction N n z * f z - f z| ≤ B
        rw [← sub_one_mul, abs_mul]
        exact (mul_le_mul_of_nonneg_right hq (abs_nonneg _)).trans (by simpa using hv)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hs := pow_le_pow_left₀ (abs_nonneg _) he 2
      simpa only [sq_abs] using hs
  · exact Eventually.of_forall fun z ↦ by
      have ht := ((coulombOuterTestFunction_tendsto_one N z).mul_const (f z)).sub_const (f z)
      simpa [coulombBoundedSmoothCutoff] using ht.pow 2

theorem coulombBoundedSmoothCutoff_gradient_L2_error (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : CoulombConfig (N + 2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B : ℝ) (hb : ∀ z, |f z| ≤ B) (hgb : ∀ z, ‖gradient f z‖ ≤ B) :
    Tendsto (fun n ↦ ∫ z,
      ‖gradient (coulombBoundedSmoothCutoff N n f hf : CoulombConfig (N + 2) → ℝ) z -
        gradient f z‖ ^ 2 ∂coulombMeasure (N + 2) β) atTop (𝓝 0) := by
  let _ := coulombMeasure_isProbability (N := N + 2) hβ
  have hB : 0 ≤ B := (abs_nonneg (f 0)).trans (hb 0)
  have hgc : Continuous (gradient f) := (hf.gradient_right (m := 0) (by simp)).continuous
  obtain ⟨C, hC, hc⟩ := coulombOuterBump_gradient_bound N
  have hcut (n : ℕ) (z : CoulombConfig (N + 2)) :
      ‖gradient (coulombOuterTestFunction N n : CoulombConfig (N + 2) → ℝ) z‖ ≤ C := by
    apply (hc (pointOuterRadius n) (pointOuterRadius_pos n) z).trans
    apply (div_le_iff₀ (pointOuterRadius_pos n)).mpr
    have hR : 1 ≤ pointOuterRadius n := by simp [pointOuterRadius]
    nlinarith
  have h := tendsto_integral_of_dominated_convergence (μ := coulombMeasure (N + 2) β)
    (F := fun n z ↦ ‖gradient (coulombBoundedSmoothCutoff N n f hf : CoulombConfig (N + 2) → ℝ) z - gradient f z‖ ^ 2)
    (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ (2 * B + B * C) ^ 2)
    (fun n ↦ ((TauCeti.continuous_gradient_testFunction (coulombBoundedSmoothCutoff N n f hf)).sub hgc).norm.pow 2 |>.aestronglyMeasurable)
    (integrable_const _) ?_ ?_
  · simpa only [integral_zero] using h
  · intro n
    exact Eventually.of_forall fun z ↦ by
      have h0 := (coulombOuterBump N (pointOuterRadius n) (pointOuterRadius_pos n)).nonneg (x := z)
      have h1 := (coulombOuterBump N (pointOuterRadius n) (pointOuterRadius_pos n)).le_one (x := z)
      have hq : |coulombOuterTestFunction N n z| ≤ 1 := by
        change |coulombOuterBump N (pointOuterRadius n) (pointOuterRadius_pos n) z| ≤ 1
        rwa [abs_of_nonneg h0]
      have hp : ‖gradient (coulombBoundedSmoothCutoff N n f hf : CoulombConfig (N + 2) → ℝ) z‖ ≤ B + B * C := by
        rw [coulombBoundedSmoothCutoff_gradient]
        calc
          _ ≤ ‖coulombOuterTestFunction N n z • gradient f z‖ +
              ‖f z • gradient (coulombOuterTestFunction N n : CoulombConfig (N + 2) → ℝ) z‖ := norm_add_le _ _
          _ = |coulombOuterTestFunction N n z| * ‖gradient f z‖ +
              |f z| * ‖gradient (coulombOuterTestFunction N n : CoulombConfig (N + 2) → ℝ) z‖ := by simp only [norm_smul, Real.norm_eq_abs]
          _ ≤ 1 * B + B * C := add_le_add
            (mul_le_mul hq (hgb z) (norm_nonneg _) (by norm_num))
            (mul_le_mul (hb z) (hcut n z) (norm_nonneg _) hB)
          _ = B + B * C := by ring
      have he := (norm_sub_le
        (gradient (coulombBoundedSmoothCutoff N n f hf : CoulombConfig (N + 2) → ℝ) z) (gradient f z)).trans
        (add_le_add hp (hgb z))
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
  · exact Eventually.of_forall fun z ↦ by
      have hfirst := (coulombOuterTestFunction_tendsto_one N z).smul
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ gradient f z) atTop (𝓝 (gradient f z)))
      have hsecond := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ f z) atTop (𝓝 (f z))).smul
        (coulombOuterTestFunction_gradient_tendsto_zero N z)
      have ht := ((hfirst.add hsecond).sub_const (gradient f z)).norm.pow 2
      simpa only [coulombBoundedSmoothCutoff_gradient, one_smul, smul_zero, add_zero,
        sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ht

def coulombBoundedSmoothJet (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : CoulombConfig (N + 2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B : ℝ) (hb : ∀ z, |f z| ≤ B) (hgb : ∀ z, ‖gradient f z‖ ≤ B) :
    CoulombJetL2 (N + 2) β := by
  let _ := coulombMeasure_isProbability (N := N + 2) hβ
  have hv : MemLp f 2 (coulombMeasure (N + 2) β) :=
    MemLp.of_bound hf.continuous.aestronglyMeasurable B
      (Eventually.of_forall fun z ↦ by simpa only [Real.norm_eq_abs] using hb z)
  have hgc : Continuous (gradient f) := (hf.gradient_right (m := 0) (by simp)).continuous
  have hg : MemLp (gradient f) 2 (coulombMeasure (N + 2) β) :=
    MemLp.of_bound hgc.aestronglyMeasurable B (Eventually.of_forall hgb)
  have hj : MemLp (fun z ↦ WithLp.toLp 2 (f z, gradient f z)) 2 (coulombMeasure (N + 2) β) := by
    apply MemLp.of_fst_of_snd_prodLp
    exact ⟨by simpa only [WithLp.toLp_fst] using hv, by simpa only [WithLp.toLp_snd] using hg⟩
  exact hj.toLp _

theorem coulombBoundedSmoothJet_coe (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : CoulombConfig (N + 2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B : ℝ) (hb : ∀ z, |f z| ≤ B) (hgb : ∀ z, ‖gradient f z‖ ≤ B) :
    coulombBoundedSmoothJet N hβ f hf B hb hgb =ᵐ[coulombMeasure (N + 2) β]
      (fun z ↦ WithLp.toLp 2 (f z, gradient f z)) := by
  unfold coulombBoundedSmoothJet
  exact MemLp.coeFn_toLp _

theorem coulombBoundedSmoothJet_value (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : CoulombConfig (N + 2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B : ℝ) (hb : ∀ z, |f z| ≤ B) (hgb : ∀ z, ‖gradient f z‖ ≤ B) :
    coulombJetValueL (N + 2) β (coulombBoundedSmoothJet N hβ f hf B hb hgb)
      =ᵐ[coulombMeasure (N + 2) β] f := by
  filter_upwards [coulombJetValueL_coe (N + 2) β (coulombBoundedSmoothJet N hβ f hf B hb hgb),
    coulombBoundedSmoothJet_coe N hβ f hf B hb hgb] with z hv hj
  simpa only [hj, WithLp.toLp_fst] using hv

theorem coulombBoundedSmoothJet_gradient (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : CoulombConfig (N + 2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B : ℝ) (hb : ∀ z, |f z| ≤ B) (hgb : ∀ z, ‖gradient f z‖ ≤ B) :
    coulombJetGradientL (N + 2) β (coulombBoundedSmoothJet N hβ f hf B hb hgb)
      =ᵐ[coulombMeasure (N + 2) β] gradient f := by
  filter_upwards [coulombJetGradientL_coe (N + 2) β (coulombBoundedSmoothJet N hβ f hf B hb hgb),
    coulombBoundedSmoothJet_coe N hβ f hf B hb hgb] with z hg hj
  simpa only [hj, WithLp.toLp_snd] using hg

theorem coulombBoundedSmoothCutoff_jet_tendsto (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : CoulombConfig (N + 2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B : ℝ) (hb : ∀ z, |f z| ≤ B) (hgb : ∀ z, ‖gradient f z‖ ≤ B) :
    Tendsto (fun n ↦ coulombAmbientJet N hβ (coulombBoundedSmoothCutoff N n f hf))
      atTop (𝓝 (coulombBoundedSmoothJet N hβ f hf B hb hgb)) := by
  apply coulombJet_tendsto_of_components N
  · apply coulomb_L2_tendsto_of_sq_integral N
    convert coulombBoundedSmoothCutoff_L2_error N hβ f hf B hb using 1
    ext n
    apply integral_congr_ae
    filter_upwards [coulombAmbientJet_value N hβ (coulombBoundedSmoothCutoff N n f hf),
      coulombBoundedSmoothJet_value N hβ f hf B hb hgb] with z hz hvz
    simp only [hz, hvz, Real.norm_eq_abs, sq_abs]
  · apply coulomb_L2_tendsto_of_sq_integral N
    convert coulombBoundedSmoothCutoff_gradient_L2_error N hβ f hf B hb hgb using 1
    ext n
    apply integral_congr_ae
    filter_upwards [coulombAmbientJet_gradient N hβ (coulombBoundedSmoothCutoff N n f hf),
      coulombBoundedSmoothJet_gradient N hβ f hf B hb hgb] with z hz hvz
    simp only [hz, hvz]

theorem coulombBoundedSmoothJet_mem_closedCore (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : CoulombConfig (N + 2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B : ℝ) (hb : ∀ z, |f z| ≤ B) (hgb : ∀ z, ‖gradient f z‖ ≤ B) :
    coulombBoundedSmoothJet N hβ f hf B hb hgb ∈ coulombCoreGraph (N + 2) hβ :=
  isClosed_closure.mem_of_tendsto (coulombBoundedSmoothCutoff_jet_tendsto N hβ f hf B hb hgb)
    (Eventually.of_forall fun n ↦ coulombAmbientJet_mem_closedCore N hβ (coulombBoundedSmoothCutoff N n f hf))

/-- The actual original closed form element of a bounded globally smooth function. -/
def coulombBoundedSmoothForm (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : CoulombConfig (N + 2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B : ℝ) (hb : ∀ z, |f z| ≤ B) (hgb : ∀ z, ‖gradient f z‖ ≤ B) :
    CoulombFormDomain (N + 2) hβ :=
  ⟨coulombBoundedSmoothJet N hβ f hf B hb hgb, by
    change coulombBoundedSmoothJet N hβ f hf B hb hgb ∈ (coulombFormSubmodule (N + 2) hβ : Set _)
    rw [coe_coulombFormSubmodule]
    exact coulombBoundedSmoothJet_mem_closedCore N hβ f hf B hb hgb⟩

theorem coulombBoundedSmoothForm_value (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : CoulombConfig (N + 2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B : ℝ) (hb : ∀ z, |f z| ≤ B) (hgb : ∀ z, ‖gradient f z‖ ≤ B) :
    coulombFormValueL (N + 2) hβ (coulombBoundedSmoothForm N hβ f hf B hb hgb)
      =ᵐ[coulombMeasure (N + 2) β] f :=
  coulombBoundedSmoothJet_value N hβ f hf B hb hgb

theorem coulombBoundedSmoothForm_gradient (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : CoulombConfig (N + 2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B : ℝ) (hb : ∀ z, |f z| ≤ B) (hgb : ∀ z, ‖gradient f z‖ ≤ B) :
    coulombFormGradientL (N + 2) hβ (coulombBoundedSmoothForm N hβ f hf B hb hgb)
      =ᵐ[coulombMeasure (N + 2) β] gradient f :=
  coulombBoundedSmoothJet_gradient N hβ f hf B hb hgb

theorem coulombBoundedSmoothForm_energy (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : CoulombConfig (N + 2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B : ℝ) (hb : ∀ z, |f z| ≤ B) (hgb : ∀ z, ‖gradient f z‖ ≤ B) :
    coulombFormEnergy (N + 2) hβ (coulombBoundedSmoothForm N hβ f hf B hb hgb) =
      ∫ z, ‖gradient f z‖ ^ 2 ∂coulombMeasure (N + 2) β := by
  rw [coulombFormEnergy_eq_integral]
  apply integral_congr_ae
  filter_upwards [coulombBoundedSmoothForm_gradient N hβ f hf B hb hgb] with z hz
  rw [hz]

end RepulsiveCoulomb
