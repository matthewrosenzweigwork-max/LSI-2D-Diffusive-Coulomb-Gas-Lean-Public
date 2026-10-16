module

public import LeanResearch.RepulsiveCoulomb.DbarBranchCompatibilityCutoff

@[expose] public section

/-! The weak cutoff source is the actual integral of dbar(theta) wedge Su.
Every term is integrable by compact raw testing; this does not assert global
Euclidean-L2 integrability of the untransformed source. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombRealCutoff_raw_source_integral {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (θ φ : TestFunction (coulombDomain N) ℝ ⊤)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (i j : Fin N) :
    (1 / 2 : ℂ) *
      (coulombAuxiliaryRawPairingL hβ j (coulombRealCoreProduct
          (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N i 1) θ) φ) u +
        Complex.I * coulombAuxiliaryRawPairingL hβ j (coulombRealCoreProduct
          (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N i Complex.I) θ) φ) u -
        coulombAuxiliaryRawPairingL hβ i (coulombRealCoreProduct
          (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N j 1) θ) φ) u -
        Complex.I * coulombAuxiliaryRawPairingL hβ i (coulombRealCoreProduct
          (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N j Complex.I) θ) φ) u) =
      ∫ z, φ z • dbarVectorWedge (coulombDbar (fun x => (θ x : ℂ)) z)
        (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (u z)) i j := by
  let φxi := coulombRealCoreProduct
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N i 1) θ) φ
  let φyi := coulombRealCoreProduct
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N i Complex.I) θ) φ
  let φxj := coulombRealCoreProduct
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N j 1) θ) φ
  let φyj := coulombRealCoreProduct
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coulombCoordinateInjection N j Complex.I) θ) φ
  let V := fun z => dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (u z)
  have hxi : Integrable (fun z => φxi z • V z j) volume :=
    coulombAuxiliaryRawPairing_integrable hβ j φxi u
  have hyi : Integrable (fun z => φyi z • V z j) volume :=
    coulombAuxiliaryRawPairing_integrable hβ j φyi u
  have hxj : Integrable (fun z => φxj z • V z i) volume :=
    coulombAuxiliaryRawPairing_integrable hβ i φxj u
  have hyj : Integrable (fun z => φyj z • V z i) volume :=
    coulombAuxiliaryRawPairing_integrable hβ i φyj u
  change (1 / 2 : ℂ) *
    (coulombAuxiliaryRawPairingL hβ j φxi u + Complex.I * coulombAuxiliaryRawPairingL hβ j φyi u -
      coulombAuxiliaryRawPairingL hβ i φxj u - Complex.I * coulombAuxiliaryRawPairingL hβ i φyj u) = _
  simp_rw [coulombAuxiliaryRawPairingL_apply]
  calc
    _ = ∫ z, (1 / 2 : ℂ) *
        (φxi z • V z j + Complex.I * (φyi z • V z j) -
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
    _ = _ := integral_congr_ae (Eventually.of_forall fun z =>
      coulombRealCutoff_raw_source_pointwise θ φ z (V z) i j)

theorem coulombAuxiliaryCutoffRawSourceL_apply {N : ℕ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (i j : Fin N) (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    coulombAuxiliaryCutoffRawSourceL hβ hR i j φ u =
      ∫ z, φ z • dbarVectorWedge (coulombDbar (fun x => (coulombMetricCutoff R x : ℂ)) z)
        (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (u z)) i j := by
  change (1 / 2 : ℂ) * _ = _
  exact coulombRealCutoff_raw_source_integral hβ (coulombMetricCutoffTest hR) φ u i j

theorem coulombAuxiliaryCompatibility_cutoff_integral {N : ℕ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hu : u ∈ coulombAuxiliaryCompatibility N hβ)
    (i j : Fin N) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombAuxiliaryCurlConstraintL hβ i j φ (coulombMetricCutoffL2L hR (CoulombConfig N) u) =
      -(∫ z, φ z • dbarVectorWedge (coulombDbar (fun x => (coulombMetricCutoff R x : ℂ)) z)
        (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (u z)) i j) := by
  rw [coulombAuxiliaryCompatibility_cutoff_weak hβ hR hu, coulombAuxiliaryCutoffRawSourceL_apply]

end RepulsiveCoulomb
