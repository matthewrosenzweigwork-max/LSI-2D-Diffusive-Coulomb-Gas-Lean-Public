import LeanResearch.RepulsiveCoulomb.DbarBranchOutputSystemCoefficients

/-! The genuine weak equation for C div(Aw), written in the finite combined
system used by Friedrichs approximation. All coefficient-derivative terms
are retained and cancelled explicitly. The application supplies the actual
auxiliary adjoint and compatibility equations, not a graph-density premise. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators LinearPMap
namespace RepulsiveCoulomb

theorem dbarLocalWeakDivergenceSystem_output_weakSystem {N : ℕ} {ι κ η δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype η] [Fintype δ]
    (A : κ → ι → δ → CoulombConfig N → ℂ) (C : η → κ → CoulombConfig N → ℂ)
    (hA : ∀ a b d z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (A a b d) z)
    (hC : ∀ q a z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (C q a) z)
    (v : δ → CoulombConfig N) (u : ι → CoulombConfig N → ℂ)
    (g : κ → CoulombConfig N → ℂ)
    (hu : ∀ b, LocallyIntegrableOn (u b) (coulombDomain N) volume)
    (hg : ∀ a, LocallyIntegrableOn (g a) (coulombDomain N) volume)
    (hweak : DbarLocalWeakDivergenceSystem A (fun _ _ _ => 0) v u g) :
    DbarLocalWeakSystem (dbarOutputSystemPrincipal A C) (dbarOutputSystemLower A C v) v u
      (fun q z => ∑ a, C q a z * g a z) := by
  intro q φ
  let P : κ → ι → δ → CoulombConfig N → ℂ := fun a b d z =>
    (C q a z * (fderiv ℝ (φ : CoulombConfig N → ℝ) z (v d) : ℂ) +
      (φ z : ℂ) * fderiv ℝ (C q a) z (v d)) * (A a b d z * u b z)
  let Q : κ → ι → δ → CoulombConfig N → ℂ := fun a b d z =>
    (φ z : ℂ) * (C q a z * fderiv ℝ (A a b d) z (v d)) * u b z
  have hP (a : κ) (b : ι) (d : δ) : Integrable (P a b d) volume := by
    have h₁ := coulombLocalCoefficient_test_integrable (fun z => C q a z * A a b d z)
      (fun z hz => (hC q a z hz).mul (hA a b d z hz))
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (v d) φ) (hu b)
    have h₂ := coulombLocalCoefficient_test_integrable
      (fun z => fderiv ℝ (C q a) z (v d) * A a b d z)
      (fun z hz => (((hC q a z hz).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
        contDiffAt_const).mul (hA a b d z hz)) φ (hu b)
    apply (h₁.add h₂).congr
    exact Eventually.of_forall fun z => by
      dsimp only [P]
      simp only [Pi.add_apply, TestFunction.lineDerivCLM_eq_fderivCLM,
        TestFunction.fderivCLM_apply_of_le (n := ⊤) (k := ⊤) φ (by simp), Complex.real_smul]
      ring
  have hQ (a : κ) (b : ι) (d : δ) : Integrable (Q a b d) volume := by
    have h := coulombLocalCoefficient_test_integrable
      (fun z => C q a z * fderiv ℝ (A a b d) z (v d))
      (fun z hz => (hC q a z hz).mul
        (((hA a b d z hz).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const))
      φ (hu b)
    apply h.congr
    exact Eventually.of_forall fun z => by
      dsimp only [Q]
      rw [Complex.real_smul]
      ring
  have hfirst (b : ι) (d : δ) :
      (∫ z, ((fderiv ℝ (φ : CoulombConfig N → ℝ) z (v d)) • dbarOutputSystemPrincipal A C q b d z +
        φ z • fderiv ℝ (dbarOutputSystemPrincipal A C q b d) z (v d)) * u b z) =
        (∑ a, ∫ z, P a b d z) + ∑ a, ∫ z, Q a b d z := by
    calc
      _ = ∫ z, ∑ a, (P a b d z + Q a b d z) := by
        apply integral_congr_ae
        filter_upwards [coulombDomain_ae N] with z hz
        rw [dbarOutputSystemPrincipal_fderiv A C hA hC q b d hz (v d)]
        simp only [dbarOutputSystemPrincipal, Complex.real_smul, Finset.mul_sum,
          Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        dsimp only [P, Q]
        ring
      _ = _ := by
        have hs := integral_finsetSum Finset.univ (fun a _ => (hP a b d).add (hQ a b d))
        simp only [Pi.add_apply] at hs
        rw [hs]
        simp_rw [integral_add (hP _ b d) (hQ _ b d), Finset.sum_add_distrib]
  have hlast (b : ι) :
      (∫ z, φ z • (dbarOutputSystemLower A C v q b z * u b z)) =
        ∑ a, ∑ d, ∫ z, Q a b d z := by
    calc
      _ = ∫ z, ∑ a, ∑ d, Q a b d z := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          simp only [dbarOutputSystemLower, Q, Complex.real_smul, Finset.sum_mul, Finset.mul_sum,
            mul_assoc]
      _ = _ := by
        rw [integral_finsetSum Finset.univ (fun a _ =>
          integrable_finsetSum Finset.univ (fun d _ => hQ a b d))]
        simp_rw [integral_finsetSum Finset.univ (fun d _ => hQ _ b d)]
  have hsource := dbarLocalWeakDivergenceSystem_output_combination A (fun _ _ _ => 0)
    hA (fun _ _ _ _ => contDiffAt_const) v u g hu hg hweak (C q) (hC q) φ
  simp only [zero_mul, mul_zero, smul_zero, integral_zero, Finset.sum_const_zero, add_zero,
    Finset.sum_neg_distrib] at hsource
  change (∫ z, φ z • (∑ a, C q a z * g a z)) = -(∑ a, ∑ b, ∑ d, ∫ z, P a b d z) at hsource
  have hswap (F : κ → ι → δ → ℂ) : (∑ b, ∑ d, ∑ a, F a b d) = ∑ a, ∑ b, ∑ d, F a b d := by
    calc
      _ = ∑ b, ∑ a, ∑ d, F a b d := by
        apply Finset.sum_congr rfl
        intro b _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hlastswap : (∑ b, ∑ a, ∑ d, ∫ z, Q a b d z) = ∑ a, ∑ b, ∑ d, ∫ z, Q a b d z :=
    Finset.sum_comm
  simp_rw [hfirst, hlast, Finset.sum_add_distrib]
  rw [hsource, hswap, hswap, hlastswap]
  abel

theorem coulombAuxiliaryCutoff_joint_weakSystem {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (huh : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph)
    (hu : u ∈ coulombAuxiliaryCompatibility N hβ) :
    DbarLocalWeakSystem (coulombAuxiliaryJointPrincipal β) (coulombAuxiliaryJointLower β)
      (dbarSystemDirection N)
      (coulombDensityInputComponent β (coulombMetricCutoffL2L hR (CoulombConfig N) u))
      (coulombAuxiliaryCutoffJointOutput hR u h) := by
  have hs := dbarLocalWeakDivergenceSystem_output_weakSystem
    (coulombAuxiliaryRawSystemPrincipal β) (coulombAuxiliaryOutputMultiplier β)
    (fun a b d z hz => coulombAuxiliaryRawSystemPrincipal_contDiffAt hβ a b d hz)
    (fun q a z hz => coulombAuxiliaryOutputMultiplier_contDiffAt hβ q a hz)
    (dbarSystemDirection N)
    (coulombDensityInputComponent β (coulombMetricCutoffL2L hR (CoulombConfig N) u))
    (coulombAuxiliaryRawSystemSource hR u h)
    (coulombDensityInputComponent_locallyIntegrable hβ _)
    (coulombAuxiliaryRawSystemSource_locallyIntegrable hβ hR u h)
    (coulombAuxiliaryCutoff_joint_raw_weakSystem hβ hR huh hu)
  intro q φ
  have he : (∫ z, φ z • coulombAuxiliaryCutoffJointOutput hR u h q z) =
      ∫ z, φ z • (∑ a, coulombAuxiliaryOutputMultiplier β q a z *
        coulombAuxiliaryRawSystemSource hR u h a z) := by
    apply integral_congr_ae
    filter_upwards [coulombAuxiliaryOutputMultiplier_source hβ hR u h q] with z hz
    rw [hz]
  rw [he]
  exact hs q φ

end RepulsiveCoulomb
