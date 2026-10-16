module

public import LeanResearch.RepulsiveCoulomb.PointWeightLocalL2
public import LeanResearch.RepulsiveCoulomb.Imported.TauCeti.Analysis.Sobolev.W1p.Basic
public import LeanResearch.RepulsiveCoulomb.Imported.TauCeti.Analysis.Sobolev.TestFunctionLp

@[expose] public section

/-! The literal value/physical-gradient graph on the point-punctured smooth
core. The fibre uses Tau Ceti's Euclidean value-gradient jet, but integration
here is with respect to the actual normalized point measure. No Haar instance
is imposed on that measure. Graph closure and its injective L2 realization
are established in the subsequent closability module.
-/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology
namespace RepulsiveCoulomb

abbrev PointJetL2 {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) :=
  Lp (TauCeti.Sobolev1Jet ℂ) 2 (pointMeasure γ a y)

def pointJetValueL {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) :
    PointJetL2 γ a y →L[ℝ] Lp ℝ 2 (pointMeasure γ a y) :=
  (WithLp.fstL 2 ℝ ℝ ℂ).compLpL 2 (pointMeasure γ a y)

def pointJetGradientL {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) :
    PointJetL2 γ a y →L[ℝ] Lp ℂ 2 (pointMeasure γ a y) :=
  (WithLp.sndL 2 ℝ ℝ ℂ).compLpL 2 (pointMeasure γ a y)

theorem pointJetValueL_coe {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ)
    (J : PointJetL2 γ a y) :
    ∀ᵐ z ∂pointMeasure γ a y, pointJetValueL γ a y J z = WithLp.fst (J z) :=
  (WithLp.fstL 2 ℝ ℝ ℂ).coeFn_compLp J

theorem pointJetGradientL_coe {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ)
    (J : PointJetL2 γ a y) :
    ∀ᵐ z ∂pointMeasure γ a y, pointJetGradientL γ a y J z = WithLp.snd (J z) :=
  (WithLp.sndL 2 ℝ ℝ ℂ).coeFn_compLp J

theorem pointCoreJet_memLp {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    MemLp (fun z ↦ WithLp.toLp 2 (φ z, gradient (φ : ℂ → ℝ) z)) 2 (pointMeasure γ a y) := by
  let := pointMeasure_isProbability hγ ha y
  apply MemLp.of_fst_of_snd_prodLp
  constructor
  · simpa only [WithLp.toLp_fst] using
      (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport :
        MemLp (φ : ℂ → ℝ) 2 (pointMeasure γ a y))
  · simpa only [WithLp.toLp_snd] using
      ((TauCeti.continuous_gradient_testFunction φ).memLp_of_hasCompactSupport
        (TauCeti.hasCompactSupport_gradient_testFunction φ) :
        MemLp (fun z ↦ gradient (φ : ℂ → ℝ) z) 2 (pointMeasure γ a y))

def pointCoreJet {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) : PointJetL2 γ a y :=
  (pointCoreJet_memLp hγ ha y φ).toLp _

theorem pointCoreJet_coe {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    ∀ᵐ z ∂pointMeasure γ a y,
      pointCoreJet hγ ha y φ z = WithLp.toLp 2 (φ z, gradient (φ : ℂ → ℝ) z) :=
  (pointCoreJet_memLp hγ ha y φ).coeFn_toLp

theorem pointCoreJet_value {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    pointJetValueL γ a y (pointCoreJet hγ ha y φ) =ᵐ[pointMeasure γ a y] φ := by
  filter_upwards [pointJetValueL_coe γ a y (pointCoreJet hγ ha y φ),
    pointCoreJet_coe hγ ha y φ] with z hv hj
  simpa only [hj, WithLp.toLp_fst] using hv

theorem pointCoreJet_gradient {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    pointJetGradientL γ a y (pointCoreJet hγ ha y φ) =ᵐ[pointMeasure γ a y]
      (fun z ↦ gradient (φ : ℂ → ℝ) z) := by
  filter_upwards [pointJetGradientL_coe γ a y (pointCoreJet hγ ha y φ),
    pointCoreJet_coe hγ ha y φ] with z hg hj
  simpa only [hj, WithLp.toLp_snd] using hg

/-- The graph norm is the physical Hilbert norm, not the supremum norm on a
product. This adapts the elementary jet identity in Tau Ceti's W1p.Basic to
an arbitrary measure; no assertion about its Haar weak-derivative relation is used. -/
theorem pointJet_norm_sq {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ)
    (J : PointJetL2 γ a y) :
    ‖J‖ ^ 2 = ‖pointJetValueL γ a y J‖ ^ 2 + ‖pointJetGradientL γ a y J‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq J,
    ← real_inner_self_eq_norm_sq (pointJetValueL γ a y J),
    ← real_inner_self_eq_norm_sq (pointJetGradientL γ a y J),
    L2.inner_def, L2.inner_def, L2.inner_def,
    ← integral_add (L2.integrable_inner (pointJetValueL γ a y J) (pointJetValueL γ a y J))
      (L2.integrable_inner (pointJetGradientL γ a y J) (pointJetGradientL γ a y J))]
  apply integral_congr_ae
  filter_upwards [pointJetValueL_coe γ a y J, pointJetGradientL_coe γ a y J] with z hv hg
  rw [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd, ← hv, ← hg]

end RepulsiveCoulomb
