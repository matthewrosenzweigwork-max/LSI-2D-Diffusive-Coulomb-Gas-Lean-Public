module

public import Mathlib
public meta import Lean.Meta.Tactic.AuxLemma
public meta import Lean.Elab.Command

@[expose] public section

/-!
# Planar Coulomb full-form LSI and uniform point-Gaussian inequalities

This is the literal physical law and full closed smooth-core form from the
accepted source. The four selected rate/constant definitions are witness holes: their
Solution bodies are the original constructed rates, never caller hypotheses.
The compact rate is fixed before temperature, particle count and observable.
All `sorry` declarations are selected comparator holes. Solution imports the
original proofs and does not import this Challenge.
-/

noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology BigOperators ENNReal

-- Match canonical instance choices from the original source import contexts.
attribute [-instance] instCommCStarAlgebraComplex Complex.instFiniteDimensionalReal

namespace TauCeti
universe u_2
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The real scalar value/gradient fibre, with the Euclidean product norm on `ℝ × E`. -/
abbrev Sobolev1Jet (E : Type u_2) := WithLp 2 (ℝ × E)
end TauCeti

namespace PeriodicAttractiveLogGas
variable {α : Type*} [MeasurableSpace α]

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The shifted entropy integrand `t log t + 1`, nonnegative when `t ≥ 0`. -/
def entropyDensity (t : ℝ) : ℝ := t * Real.log t + 1

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- Extended-real entropy of `F` relative to `μ`: the nonnegative Lebesgue integral of
`F log F + 1`, minus `μ(univ) + (∫ F) log (∫ F)`. For a probability measure and
nonnegative integrable `F` this is the unnormalised entropy, possibly infinite. -/
def entropy (μ : Measure α) (F : α → ℝ) : EReal :=
  (∫⁻ x, ENNReal.ofReal (entropyDensity (F x)) ∂μ) -
    ((μ.real Set.univ + (∫ x, F x ∂μ) * Real.log (∫ x, F x ∂μ) : ℝ) : EReal)
end PeriodicAttractiveLogGas

namespace RepulsiveCoulomb

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The labeled `N`-particle configuration space `ℂᴺ`, equipped with its Euclidean
Hilbert norm (not the coordinatewise supremum norm). -/
abbrev CoulombConfig (N : ℕ) := EuclideanSpace ℂ (Fin N)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The finite set of particle-label pairs `(i,j)` with `i < j`, counting each
unordered pair exactly once. -/
def coulombPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p => p.1 < p.2)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The real continuous linear map extracting the `i`th complex particle coordinate. -/
def coulombCoordinate {N : ℕ} (i : Fin N) : CoulombConfig N →L[ℝ] ℂ :=
  (EuclideanSpace.proj i).restrictScalars ℝ

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The product of all particle differences `z i - z j` over `i < j`. It is nonzero
exactly when the labeled particles occupy distinct positions. -/
def coulombVandermonde {N : ℕ} (z : CoulombConfig N) : ℂ :=
  ∏ p ∈ coulombPairs N, (z p.1 - z p.2)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem coulombVandermonde_continuous (N : ℕ) : Continuous (coulombVandermonde (N := N)) := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The open collision-free configuration space, defined by a nonvanishing Vandermonde product. -/
def coulombDomain (N : ℕ) : Opens (CoulombConfig N) :=
  ⟨{z | coulombVandermonde z ≠ 0}, (isClosed_eq (coulombVandermonde_continuous N) continuous_const).isOpen_compl⟩

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The original repulsive Coulomb Gibbs weight:
`exp (-β ‖z‖² / 2) ∏_{i<j} ‖z i - z j‖^(β/N)` with respect to Euclidean Lebesgue measure. -/
def coulombWeight {N : ℕ} (β : ℝ) (z : CoulombConfig N) : ℝ :=
  Real.exp (-β * ‖z‖ ^ 2 / 2) *
    ∏ p ∈ coulombPairs N, ‖z p.1 - z p.2‖ ^ (β / (N : ℝ))

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The extended nonnegative integral of the Gibbs weight over the full labeled
configuration space, providing the original normalization constant. -/
def coulombPartition (N : ℕ) (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : CoulombConfig N, ENNReal.ofReal (coulombWeight β z)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The original labeled Gibbs law, obtained by multiplying Lebesgue measure by
the Gibbs weight and scaling by the inverse partition function. The Solution
proves finite positive normalization for `β > 0`. -/
def coulombMeasure (N : ℕ) (β : ℝ) : Measure (CoulombConfig N) :=
  (coulombPartition N β)⁻¹ • volume.withDensity (fun z => ENNReal.ofReal (coulombWeight β z))

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The `L²` space of value/real-gradient Hilbert jets for the original labeled Gibbs law. -/
abbrev CoulombJetL2 (N : ℕ) (β : ℝ) := Lp (TauCeti.Sobolev1Jet (CoulombConfig N)) 2 (coulombMeasure N β)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The continuous real linear projection from a Gibbs `L²` jet to its scalar value class. -/
def coulombJetValueL (N : ℕ) (β : ℝ) : CoulombJetL2 N β →L[ℝ] Lp ℝ 2 (coulombMeasure N β) :=
  (WithLp.fstL 2 ℝ ℝ (CoulombConfig N)).compLpL 2 (coulombMeasure N β)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The continuous real linear projection from a Gibbs `L²` jet to its gradient class. -/
def coulombJetGradientL (N : ℕ) (β : ℝ) : CoulombJetL2 N β →L[ℝ] Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (WithLp.sndL 2 ℝ ℝ (CoulombConfig N)).compLpL 2 (coulombMeasure N β)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem coulombCoreJet_memLp {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    MemLp (fun z => WithLp.toLp 2 (φ z, gradient (φ : CoulombConfig N → ℝ) z)) 2 (coulombMeasure N β) := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The Gibbs `L²` class of the literal value/gradient pair `(φ, ∇φ)` of a compactly
supported smooth test function on the full collision-free configuration space. -/
def coulombCoreJet {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) : CoulombJetL2 N β :=
  (coulombCoreJet_memLp hβ φ).toLp _

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem coulombCoreJet_add {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ ψ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombCoreJet hβ (φ + ψ) = coulombCoreJet hβ φ + coulombCoreJet hβ ψ := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem coulombCoreJet_smul {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (c : ℝ) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombCoreJet hβ (c • φ) = c • coulombCoreJet hβ φ := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The real linear map embedding the complete collision-free smooth test-function
core into Gibbs `L²` value/gradient jets. -/
def coulombCoreJetLinear (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    TestFunction (coulombDomain N) ℝ ⊤ →ₗ[ℝ] CoulombJetL2 N β where
  toFun := coulombCoreJet hβ
  map_add' := coulombCoreJet_add hβ
  map_smul' := coulombCoreJet_smul hβ

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The closure, in the Gibbs `L²` Hilbert jet norm, of the range of the full
collision-free smooth-core map. No smaller test core or supplied closed form is substituted. -/
def coulombFormSubmodule (N : ℕ) {β : ℝ} (hβ : 0 < β) : ClosedSubmodule ℝ (CoulombJetL2 N β) :=
  (LinearMap.range (coulombCoreJetLinear N hβ)).closure

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The original full closed Coulomb form domain, consisting of value/gradient jets
in the closed submodule generated by all collision-free smooth test functions. -/
abbrev CoulombFormDomain (N : ℕ) {β : ℝ} (hβ : 0 < β) := (coulombFormSubmodule N hβ).toSubmodule

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The continuous real linear value projection on the full closed Coulomb form domain. -/
def coulombFormValueL (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    CoulombFormDomain N hβ →L[ℝ] Lp ℝ 2 (coulombMeasure N β) :=
  (coulombJetValueL N β).comp (coulombFormSubmodule N hβ).toSubmodule.subtypeL

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The continuous real linear gradient projection on the full closed Coulomb form domain. -/
def coulombFormGradientL (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    CoulombFormDomain N hβ →L[ℝ] Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (coulombJetGradientL N β).comp (coulombFormSubmodule N hβ).toSubmodule.subtypeL

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The original closed-form Dirichlet energy: the squared Gibbs `L²` norm
of the full-domain gradient. -/
def coulombFormEnergy (N : ℕ) {β : ℝ} (hβ : 0 < β) (u : CoulombFormDomain N hβ) : ℝ :=
  ‖coulombFormGradientL N hβ u‖ ^ 2


run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The point-weighted planar Gaussian density before normalization:
`exp (-γ ‖z‖² / 2) ∏ j, ‖z - y j‖^(a j)`, with arbitrary finite point locations. -/
def pointWeight {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) : ℝ :=
  Real.exp (-γ * ‖z‖ ^ 2 / 2) * ∏ j, ‖z - y j‖ ^ a j

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- Exactly the locations carrying positive exponents. Coincident points are allowed,
and a zero exponent introduces no puncture. -/
def pointPunctures {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) : Set ℂ :=
  {z | ∃ j, 0 < a j ∧ z = y j}

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The extended nonnegative Lebesgue integral of the point-Gaussian density on `ℂ`. -/
def pointPartition {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) : ℝ≥0∞ :=
  ∫⁻ z : ℂ, ENNReal.ofReal (pointWeight γ a y z)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The original normalized point-Gaussian law: inverse partition function times
Lebesgue measure with density `pointWeight γ a y`. -/
def pointMeasure {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) : Measure ℂ :=
  (pointPartition γ a y)⁻¹ •
    volume.withDensity (fun z ↦ ENNReal.ofReal (pointWeight γ a y z))

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem pointPunctures_finite {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) :
    (pointPunctures a y).Finite := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The open plane with precisely the positive-exponent point locations removed. -/
def pointDomain {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) : TopologicalSpace.Opens ℂ :=
  ⟨(pointPunctures a y)ᶜ, (pointPunctures_finite a y).isClosed.isOpen_compl⟩

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem pointMeasure_isProbability {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    IsProbabilityMeasure (pointMeasure γ a y) := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The Hilbert `L²` space of scalar value/real planar-gradient jets for the point-Gaussian law. -/
abbrev PointJetL2 {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) :=
  Lp (TauCeti.Sobolev1Jet ℂ) 2 (pointMeasure γ a y)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The continuous real linear projection of a point-Gaussian `L²` jet onto its scalar value. -/
def pointJetValueL {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) :
    PointJetL2 γ a y →L[ℝ] Lp ℝ 2 (pointMeasure γ a y) :=
  (WithLp.fstL 2 ℝ ℝ ℂ).compLpL 2 (pointMeasure γ a y)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The continuous real linear projection of a point-Gaussian `L²` jet onto its real planar gradient. -/
def pointJetGradientL {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) :
    PointJetL2 γ a y →L[ℝ] Lp ℂ 2 (pointMeasure γ a y) :=
  (WithLp.sndL 2 ℝ ℝ ℂ).compLpL 2 (pointMeasure γ a y)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem pointCoreJet_memLp {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    MemLp (fun z ↦ WithLp.toLp 2 (φ z, gradient (φ : ℂ → ℝ) z)) 2 (pointMeasure γ a y) := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The literal value/gradient `L²` class of any compactly supported smooth test function
on the plane minus the positive-exponent punctures. -/
def pointCoreJet {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) : PointJetL2 γ a y :=
  (pointCoreJet_memLp hγ ha y φ).toLp _

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem pointCoreJet_add {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ ψ : TestFunction (pointDomain a y) ℝ ⊤) :
    pointCoreJet hγ ha y (φ + ψ) = pointCoreJet hγ ha y φ + pointCoreJet hγ ha y ψ := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem pointCoreJet_smul {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ) (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    pointCoreJet hγ ha y (c • φ) = c • pointCoreJet hγ ha y φ := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The real linear embedding of the full punctured smooth core into point-Gaussian Hilbert jets. -/
def pointCoreJetLinear {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    TestFunction (pointDomain a y) ℝ ⊤ →ₗ[ℝ] PointJetL2 γ a y where
  toFun := pointCoreJet hγ ha y
  map_add' := pointCoreJet_add hγ ha y
  map_smul' := pointCoreJet_smul hγ ha y

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The closure of the full punctured smooth-core range in the point-Gaussian value/gradient
Hilbert norm. No point-separation condition or smaller core is imposed. -/
def pointFormSubmodule {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    ClosedSubmodule ℝ (PointJetL2 γ a y) :=
  (LinearMap.range (pointCoreJetLinear hγ ha y)).closure

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The full closed Dirichlet-form domain generated by all real smooth compactly supported
functions off the positive-exponent punctures. -/
abbrev PointFormDomain {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :=
  (pointFormSubmodule hγ ha y).toSubmodule

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The continuous real linear scalar-value projection on the full closed point-Gaussian domain. -/
def pointFormValueL {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    PointFormDomain hγ ha y →L[ℝ] Lp ℝ 2 (pointMeasure γ a y) :=
  (pointJetValueL γ a y).comp (pointFormSubmodule hγ ha y).toSubmodule.subtypeL

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The continuous real linear physical-gradient projection on the full closed point-Gaussian domain. -/
def pointFormGradientL {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    PointFormDomain hγ ha y →L[ℝ] Lp ℂ 2 (pointMeasure γ a y) :=
  (pointJetGradientL γ a y).comp (pointFormSubmodule hγ ha y).toSubmodule.subtypeL

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The squared `L²` norm of the physical planar gradient for the original normalized point law. -/
def pointFormEnergy {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (u : PointFormDomain hγ ha y) : ℝ := ‖pointFormGradientL hγ ha y u‖ ^ 2

end RepulsiveCoulomb

open PeriodicAttractiveLogGas ProbabilityTheory
namespace RepulsiveCoulomb.PaperRoute

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- A positive fixed-temperature labeled LSI rate depending only on `β` and its
positivity proof, fixed independently of particle count and observable. This is
a selected definition hole: Solution supplies the original actual thermal-reference
construction, while its internal formula is not fixed by this Challenge. -/
def paperOriginalLabeledRate {β : ℝ} (hβ : 0 < β) : ℝ := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem paperOriginalLabeledRate_pos {β : ℝ} (hβ : 0 < β) :
    0 < paperOriginalLabeledRate hβ := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem paper_full_labeled_lsi_original {β : ℝ} (hβ : 0 < β)
    (N : ℕ) (hN : 2 ≤ N) (u : CoulombFormDomain N hβ) :
    entropy (coulombMeasure N β) (fun z => (coulombFormValueL N hβ u z)^2) ≤
      (((2 / paperOriginalLabeledRate hβ) * coulombFormEnergy N hβ u : ℝ) : EReal) := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- A compact-temperature labeled LSI rate depending only on the interval endpoints
`a,b` and the proof `0 < a`, fixed before `β ∈ [a,b]`, particle count and observable.
Positivity is required when `a ≤ b`. This is a selected definition hole: Solution
supplies the original thermal-reference/family-supremum construction, while its
internal formula is not fixed by this Challenge. -/
def paperOriginalCompactLabeledRate {a b : ℝ} (ha : 0 < a) : ℝ := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem paperOriginalCompactLabeledRate_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 < paperOriginalCompactLabeledRate (b := b) ha := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem paper_uniform_labeled_lsi_original {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    0 < paperOriginalCompactLabeledRate (b := b) ha ∧
      ∀ (β : Set.Icc a b) (N : ℕ), 2 ≤ N →
        ∀ u : CoulombFormDomain N (ha.trans_le β.2.1),
          entropy (coulombMeasure N β.1)
            (fun z => (coulombFormValueL N (ha.trans_le β.2.1) u z)^2) ≤
            (((2 / paperOriginalCompactLabeledRate (b := b) ha) *
              coulombFormEnergy N (ha.trans_le β.2.1) u : ℝ) : EReal) := by sorry


run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- A positive unit-confinement Poincare constant depending only on total-exponent bound `Q`,
independent of point count, locations, individual exponents, confinement and observable.
Selected definition hole: Solution supplies the original choice construction; its formula
is not fixed here. The `1/γ` scaling below is fixed exactly. -/
def paperWeightedP1 (Q : ℝ) : ℝ := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- A positive unit-confinement entropy-energy constant depending only on total-exponent bound `Q`,
independent of point count, locations, individual exponents, confinement and observable.
Selected definition hole: Solution supplies the original choice construction; its formula
is not fixed here. The associated LSI rate and its `γ` scaling below are fixed exactly. -/
def paperWeightedK1 (Q : ℝ) : ℝ := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem paperWeightedP1_pos (Q : ℝ) : 0 < paperWeightedP1 Q := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem paperWeightedK1_pos (Q : ℝ) : 0 < paperWeightedK1 Q := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The uniform Poincare constant at confinement `γ`: exactly the unit-confinement
constant divided by `γ`, depending only on `γ,Q`. -/
def paperCwt (γ Q : ℝ) : ℝ := paperWeightedP1 Q / γ

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- The uniform logarithmic Sobolev rate at confinement `γ`: exactly twice `γ` divided
by the unit-confinement entropy-energy constant, depending only on `γ,Q`. -/
def paperRhoWt (γ Q : ℝ) : ℝ := 2 * γ / paperWeightedK1 Q

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem paperCwt_pos {γ : ℝ} (hγ : 0 < γ) (Q : ℝ) :
    0 < paperCwt γ Q := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem paperRhoWt_pos {γ : ℝ} (hγ : 0 < γ) (Q : ℝ) :
    0 < paperRhoWt γ Q := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem paperCwt_scaling (γ Q : ℝ) :
    paperCwt γ Q = paperCwt 1 Q / γ := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem paperRhoWt_scaling (γ Q : ℝ) :
    paperRhoWt γ Q = γ * paperRhoWt 1 Q := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem paper_weighted_named_inequalities (Q : ℝ) {γ : ℝ} (hγ : 0 < γ)
    (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hQ : ∑ j, a j ≤ Q) (u : PointFormDomain hγ ha y) :
    variance (pointFormValueL hγ ha y u : ℂ → ℝ) (pointMeasure γ a y) ≤
      paperCwt γ Q * pointFormEnergy hγ ha y u ∧
    entropy (pointMeasure γ a y) (fun x => (pointFormValueL hγ ha y u x) ^ 2) ≤
      (((2 / paperRhoWt γ Q) * pointFormEnergy hγ ha y u : ℝ) : EReal) := by sorry

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
theorem paper_weighted_named_full_above (Q : ℝ) {γ₀ γ : ℝ}
    (hγ₀ : 0 < γ₀) (hγ : 0 < γ) (hγle : γ₀ ≤ γ)
    (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hQ : ∑ j, a j ≤ Q) (u : PointFormDomain hγ ha y) :
    variance (pointFormValueL hγ ha y u : ℂ → ℝ) (pointMeasure γ a y) ≤
      paperCwt γ₀ Q * pointFormEnergy hγ ha y u ∧
    entropy (pointMeasure γ a y) (fun x => (pointFormValueL hγ ha y u x) ^ 2) ≤
      (((2 / paperRhoWt γ₀ Q) * pointFormEnergy hγ ha y u : ℝ) : EReal) := by sorry

end RepulsiveCoulomb.PaperRoute
