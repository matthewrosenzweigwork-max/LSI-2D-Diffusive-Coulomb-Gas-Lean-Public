module

public import LeanResearch.RepulsiveCoulomb.CoulombLocalL2
public import LeanResearch.RepulsiveCoulomb.Imported.TauCeti.Analysis.Sobolev.W1p.Basic
public import LeanResearch.RepulsiveCoulomb.Imported.TauCeti.Analysis.Sobolev.TestFunctionLp
public meta import Lean.Meta.Tactic.AuxLemma
public meta import Lean.Elab.Command

@[expose] public section

/-! Literal value/real-Euclidean-gradient graph of the full collision-free
smooth core. Tau Ceti supplies the Hilbert jet, not a weighted Haar relation. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology ENNReal
namespace RepulsiveCoulomb

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
abbrev CoulombJetL2 (N : ℕ) (β : ℝ) := Lp (TauCeti.Sobolev1Jet (CoulombConfig N)) 2 (coulombMeasure N β)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def coulombJetValueL (N : ℕ) (β : ℝ) : CoulombJetL2 N β →L[ℝ] Lp ℝ 2 (coulombMeasure N β) :=
  (WithLp.fstL 2 ℝ ℝ (CoulombConfig N)).compLpL 2 (coulombMeasure N β)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def coulombJetGradientL (N : ℕ) (β : ℝ) : CoulombJetL2 N β →L[ℝ] Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (WithLp.sndL 2 ℝ ℝ (CoulombConfig N)).compLpL 2 (coulombMeasure N β)

theorem coulombJetValueL_coe (N : ℕ) (β : ℝ) (J : CoulombJetL2 N β) :
    ∀ᵐ z ∂coulombMeasure N β, coulombJetValueL N β J z = WithLp.fst (J z) :=
  (WithLp.fstL 2 ℝ ℝ (CoulombConfig N)).coeFn_compLp J

theorem coulombJetGradientL_coe (N : ℕ) (β : ℝ) (J : CoulombJetL2 N β) :
    ∀ᵐ z ∂coulombMeasure N β, coulombJetGradientL N β J z = WithLp.snd (J z) :=
  (WithLp.sndL 2 ℝ ℝ (CoulombConfig N)).coeFn_compLp J

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem coulombCoreJet_memLp {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    MemLp (fun z => WithLp.toLp 2 (φ z, gradient (φ : CoulombConfig N → ℝ) z)) 2 (coulombMeasure N β) := by
  let _ := coulombMeasure_isProbability (N := N) hβ
  apply MemLp.of_fst_of_snd_prodLp
  constructor
  · simpa only [WithLp.toLp_fst] using
      (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport : MemLp (φ : CoulombConfig N → ℝ) 2 (coulombMeasure N β))
  · simpa only [WithLp.toLp_snd] using
      ((TauCeti.continuous_gradient_testFunction φ).memLp_of_hasCompactSupport
        (TauCeti.hasCompactSupport_gradient_testFunction φ) :
        MemLp (fun z => gradient (φ : CoulombConfig N → ℝ) z) 2 (coulombMeasure N β))

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
def coulombCoreJet {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) : CoulombJetL2 N β :=
  (coulombCoreJet_memLp hβ φ).toLp _

theorem coulombCoreJet_coe {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    ∀ᵐ z ∂coulombMeasure N β, coulombCoreJet hβ φ z = WithLp.toLp 2 (φ z, gradient (φ : CoulombConfig N → ℝ) z) :=
  (coulombCoreJet_memLp hβ φ).coeFn_toLp

theorem coulombCoreJet_value {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombJetValueL N β (coulombCoreJet hβ φ) =ᵐ[coulombMeasure N β] φ := by
  filter_upwards [coulombJetValueL_coe N β (coulombCoreJet hβ φ), coulombCoreJet_coe hβ φ] with z hv hj
  simpa only [hj, WithLp.toLp_fst] using hv

theorem coulombCoreJet_gradient {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombJetGradientL N β (coulombCoreJet hβ φ) =ᵐ[coulombMeasure N β]
      fun z => gradient (φ : CoulombConfig N → ℝ) z := by
  filter_upwards [coulombJetGradientL_coe N β (coulombCoreJet hβ φ), coulombCoreJet_coe hβ φ] with z hg hj
  simpa only [hj, WithLp.toLp_snd] using hg

theorem coulombJet_norm_sq (N : ℕ) (β : ℝ) (J : CoulombJetL2 N β) :
    ‖J‖ ^ 2 = ‖coulombJetValueL N β J‖ ^ 2 + ‖coulombJetGradientL N β J‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq J, ← real_inner_self_eq_norm_sq (coulombJetValueL N β J),
    ← real_inner_self_eq_norm_sq (coulombJetGradientL N β J), L2.inner_def, L2.inner_def, L2.inner_def,
    ← integral_add (L2.integrable_inner (coulombJetValueL N β J) (coulombJetValueL N β J))
      (L2.integrable_inner (coulombJetGradientL N β J) (coulombJetGradientL N β J))]
  apply integral_congr_ae
  filter_upwards [coulombJetValueL_coe N β J, coulombJetGradientL_coe N β J] with z hv hg
  rw [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd, ← hv, ← hg]

end RepulsiveCoulomb
