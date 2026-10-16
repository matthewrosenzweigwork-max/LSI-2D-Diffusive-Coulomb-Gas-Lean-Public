module

public import LeanResearch.RepulsiveCoulomb.DbarBranchCompatibilityCutoffIntegral
public import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryScalarWeakSystem

@[expose] public section

/-! Literal raw exterior weak equations and their local integrability. The
untransformed coefficient Su is used only locally and in compact pairings. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulombAuxiliaryRaw_locallyIntegrable {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (i : Fin N) :
    LocallyIntegrableOn (fun z =>
      (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (u z)) i)
      (coulombDomain N) volume := by
  rw [locallyIntegrableOn_iff (coulombDomain N).isOpen.isLocallyClosed]
  intro K hKΩ hK
  simp_rw [dbarCLMMatrix_apply]
  apply integrable_finsetSum Finset.univ
  intro j _
  have hu := (EuclideanSpace.proj (𝕜 := ℂ) j).locallyIntegrableOn_comp
    (coulombL2_locallyIntegrableOn hβ u)
  exact (hu.integrableOn_compact_subset hKΩ hK).continuousOn_mul
    (fun z hz => (coulombRootMatrix_entry_contDiffAt i j (hKΩ hz)).continuousAt.continuousWithinAt) hK

theorem coulombAuxiliaryCurlConstraint_integral {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (i j : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombAuxiliaryCurlConstraintL hβ i j φ u =
      ∫ z, coulombDbarCoordinate (fun x => (φ x : ℂ)) z i *
        (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (u z)) j -
        coulombDbarCoordinate (fun x => (φ x : ℂ)) z j *
          (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (u z)) i := by
  let φxi := TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N i 1) φ
  let φyi := TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N i Complex.I) φ
  let φxj := TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N j 1) φ
  let φyj := TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N j Complex.I) φ
  let V := fun z => dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (u z)
  have hxi : Integrable (fun z => φxi z • V z j) volume :=
    coulombAuxiliaryRawPairing_integrable hβ j φxi u
  have hyi : Integrable (fun z => φyi z • V z j) volume :=
    coulombAuxiliaryRawPairing_integrable hβ j φyi u
  have hxj : Integrable (fun z => φxj z • V z i) volume :=
    coulombAuxiliaryRawPairing_integrable hβ i φxj u
  have hyj : Integrable (fun z => φyj z • V z i) volume :=
    coulombAuxiliaryRawPairing_integrable hβ i φyj u
  rw [coulombAuxiliaryCurlConstraintL_apply]
  change (1 / 2 : ℂ) * (coulombAuxiliaryRawPairingL hβ j φxi u +
    Complex.I * coulombAuxiliaryRawPairingL hβ j φyi u - coulombAuxiliaryRawPairingL hβ i φxj u -
      Complex.I * coulombAuxiliaryRawPairingL hβ i φyj u) = _
  simp_rw [coulombAuxiliaryRawPairingL_apply]
  calc
    _ = ∫ z, (1 / 2 : ℂ) * (φxi z • V z j + Complex.I * (φyi z • V z j) -
        φxj z • V z i - Complex.I * (φyj z • V z i)) := by
      have hadd := integral_add hxi (hyi.const_mul Complex.I)
      have hsub := integral_sub (hxi.add (hyi.const_mul Complex.I)) hxj
      have htotal := integral_sub ((hxi.add (hyi.const_mul Complex.I)).sub hxj)
        (hyj.const_mul Complex.I)
      simp only [Pi.add_apply, Pi.sub_apply, integral_const_mul] at hadd hsub htotal
      rw [hadd] at hsub
      rw [hsub] at htotal
      rw [integral_const_mul]
      simpa only [V] using congrArg (fun w : ℂ => (1 / 2 : ℂ) * w) htotal.symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        simp only [φxi, φyi, φxj, φyj, TestFunction.lineDerivCLM_eq_fderivCLM,
          TestFunction.fderivCLM_apply_of_le (n := ⊤) (k := ⊤) φ (by simp)]
        rw [coulombDbarCoordinate_real (φ.contDiff.differentiable (by simp) z),
          coulombDbarCoordinate_real (φ.contDiff.differentiable (by simp) z),
          coulomb_real_axis_derivative, coulomb_imag_axis_derivative,
          coulomb_real_axis_derivative, coulomb_imag_axis_derivative]
        simp only [Complex.real_smul]
        conv_rhs => rw [← Complex.re_add_im (gradient (φ : CoulombConfig N → ℝ) z i),
          ← Complex.re_add_im (gradient (φ : CoulombConfig N → ℝ) z j)]
        ring

theorem coulombAuxiliaryCutoff_raw_exterior_equation {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hu : u ∈ coulombAuxiliaryCompatibility N hβ)
    (i j : Fin N) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ z, φ z • dbarVectorWedge (coulombDbar (fun x => (coulombMetricCutoff R x : ℂ)) z)
      (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (u z)) i j) =
      -(∫ z, coulombDbarCoordinate (fun x => (φ x : ℂ)) z i *
        (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))
          (coulombMetricCutoffL2L hR (CoulombConfig N) u z)) j -
        coulombDbarCoordinate (fun x => (φ x : ℂ)) z j *
          (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))
            (coulombMetricCutoffL2L hR (CoulombConfig N) u z)) i) := by
  have h := coulombAuxiliaryCompatibility_cutoff_integral hβ hR hu i j φ
  rw [coulombAuxiliaryCurlConstraint_integral] at h
  linear_combination h

end RepulsiveCoulomb
