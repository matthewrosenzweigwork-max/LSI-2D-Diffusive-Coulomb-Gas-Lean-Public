module

public import Mathlib

@[expose] public section

/-!
# Planar repulsive Coulomb gas: original full-form labeled LSI

This is the literal physical law and full closed smooth-core form from the
accepted source. The two selected rate definitions are witness holes: their
Solution bodies are the original constructed rates, never caller hypotheses.
The compact rate is fixed before temperature, particle count and observable.
All `sorry` declarations are selected comparator holes. Solution imports the
original proofs and does not import this Challenge.
-/

noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology BigOperators ENNReal

namespace TauCeti
/-- The real scalar value/gradient fibre, with the Euclidean product norm on `ℝ × E`. -/
abbrev Sobolev1Jet (E : Type*) := WithLp 2 (ℝ × E)
end TauCeti

namespace PeriodicAttractiveLogGas
variable {α : Type*} [MeasurableSpace α]

/-- The shifted entropy integrand `t log t + 1`, nonnegative when `t ≥ 0`. -/
def entropyDensity (t : ℝ) : ℝ := t * Real.log t + 1

/-- Extended-real entropy of `F` relative to `μ`: the nonnegative Lebesgue integral of
`F log F + 1`, minus `μ(univ) + (∫ F) log (∫ F)`. For a probability measure and
nonnegative integrable `F` this is the unnormalised entropy, possibly infinite. -/
def entropy (μ : Measure α) (F : α → ℝ) : EReal :=
  (∫⁻ x, ENNReal.ofReal (entropyDensity (F x)) ∂μ) -
    ((μ.real Set.univ + (∫ x, F x ∂μ) * Real.log (∫ x, F x ∂μ) : ℝ) : EReal)
end PeriodicAttractiveLogGas

namespace RepulsiveCoulomb

/-- The labeled `N`-particle configuration space `ℂᴺ`, equipped with its Euclidean
Hilbert norm (not the coordinatewise supremum norm). -/
abbrev CoulombConfig (N : ℕ) := EuclideanSpace ℂ (Fin N)

/-- The finite set of particle-label pairs `(i,j)` with `i < j`, counting each
unordered pair exactly once. -/
def coulombPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p => p.1 < p.2)

/-- The real continuous linear map extracting the `i`th complex particle coordinate. -/
def coulombCoordinate {N : ℕ} (i : Fin N) : CoulombConfig N →L[ℝ] ℂ :=
  (EuclideanSpace.proj i).restrictScalars ℝ

/-- The product of all particle differences `z i - z j` over `i < j`. It is nonzero
exactly when the labeled particles occupy distinct positions. -/
def coulombVandermonde {N : ℕ} (z : CoulombConfig N) : ℂ :=
  ∏ p ∈ coulombPairs N, (z p.1 - z p.2)

theorem coulombVandermonde_continuous (N : ℕ) : Continuous (coulombVandermonde (N := N)) := by sorry

/-- The open collision-free configuration space, defined by a nonvanishing Vandermonde product. -/
def coulombDomain (N : ℕ) : Opens (CoulombConfig N) :=
  ⟨{z | coulombVandermonde z ≠ 0}, (isClosed_eq (coulombVandermonde_continuous N) continuous_const).isOpen_compl⟩

/-- The original repulsive Coulomb Gibbs weight:
`exp (-β ‖z‖² / 2) ∏_{i<j} ‖z i - z j‖^(β/N)` with respect to Euclidean Lebesgue measure. -/
def coulombWeight {N : ℕ} (β : ℝ) (z : CoulombConfig N) : ℝ :=
  Real.exp (-β * ‖z‖ ^ 2 / 2) *
    ∏ p ∈ coulombPairs N, ‖z p.1 - z p.2‖ ^ (β / (N : ℝ))

/-- The extended nonnegative integral of the Gibbs weight over the full labeled
configuration space, providing the original normalization constant. -/
def coulombPartition (N : ℕ) (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : CoulombConfig N, ENNReal.ofReal (coulombWeight β z)

/-- The original labeled Gibbs law, obtained by multiplying Lebesgue measure by
the Gibbs weight and scaling by the inverse partition function. The Solution
proves finite positive normalization for `β > 0`. -/
def coulombMeasure (N : ℕ) (β : ℝ) : Measure (CoulombConfig N) :=
  (coulombPartition N β)⁻¹ • volume.withDensity (fun z => ENNReal.ofReal (coulombWeight β z))

/-- The `L²` space of value/real-gradient Hilbert jets for the original labeled Gibbs law. -/
abbrev CoulombJetL2 (N : ℕ) (β : ℝ) := Lp (TauCeti.Sobolev1Jet (CoulombConfig N)) 2 (coulombMeasure N β)

/-- The continuous real linear projection from a Gibbs `L²` jet to its scalar value class. -/
def coulombJetValueL (N : ℕ) (β : ℝ) : CoulombJetL2 N β →L[ℝ] Lp ℝ 2 (coulombMeasure N β) :=
  (WithLp.fstL 2 ℝ ℝ (CoulombConfig N)).compLpL 2 (coulombMeasure N β)

/-- The continuous real linear projection from a Gibbs `L²` jet to its gradient class. -/
def coulombJetGradientL (N : ℕ) (β : ℝ) : CoulombJetL2 N β →L[ℝ] Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (WithLp.sndL 2 ℝ ℝ (CoulombConfig N)).compLpL 2 (coulombMeasure N β)

theorem coulombCoreJet_memLp {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    MemLp (fun z => WithLp.toLp 2 (φ z, gradient (φ : CoulombConfig N → ℝ) z)) 2 (coulombMeasure N β) := by sorry

/-- The Gibbs `L²` class of the literal value/gradient pair `(φ, ∇φ)` of a compactly
supported smooth test function on the full collision-free configuration space. -/
def coulombCoreJet {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) : CoulombJetL2 N β :=
  (coulombCoreJet_memLp hβ φ).toLp _

theorem coulombCoreJet_add {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ ψ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombCoreJet hβ (φ + ψ) = coulombCoreJet hβ φ + coulombCoreJet hβ ψ := by sorry

theorem coulombCoreJet_smul {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (c : ℝ) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombCoreJet hβ (c • φ) = c • coulombCoreJet hβ φ := by sorry

/-- The real linear map embedding the complete collision-free smooth test-function
core into Gibbs `L²` value/gradient jets. -/
def coulombCoreJetLinear (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    TestFunction (coulombDomain N) ℝ ⊤ →ₗ[ℝ] CoulombJetL2 N β where
  toFun := coulombCoreJet hβ
  map_add' := coulombCoreJet_add hβ
  map_smul' := coulombCoreJet_smul hβ

/-- The closure, in the Gibbs `L²` Hilbert jet norm, of the range of the full
collision-free smooth-core map. No smaller test core or supplied closed form is substituted. -/
def coulombFormSubmodule (N : ℕ) {β : ℝ} (hβ : 0 < β) : ClosedSubmodule ℝ (CoulombJetL2 N β) :=
  (LinearMap.range (coulombCoreJetLinear N hβ)).closure

/-- The original full closed Coulomb form domain, consisting of value/gradient jets
in the closed submodule generated by all collision-free smooth test functions. -/
abbrev CoulombFormDomain (N : ℕ) {β : ℝ} (hβ : 0 < β) := (coulombFormSubmodule N hβ).toSubmodule

/-- The continuous real linear value projection on the full closed Coulomb form domain. -/
def coulombFormValueL (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    CoulombFormDomain N hβ →L[ℝ] Lp ℝ 2 (coulombMeasure N β) :=
  (coulombJetValueL N β).comp (coulombFormSubmodule N hβ).toSubmodule.subtypeL

/-- The continuous real linear gradient projection on the full closed Coulomb form domain. -/
def coulombFormGradientL (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    CoulombFormDomain N hβ →L[ℝ] Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (coulombJetGradientL N β).comp (coulombFormSubmodule N hβ).toSubmodule.subtypeL

/-- The original closed-form Dirichlet energy: the squared Gibbs `L²` norm
of the full-domain gradient. -/
def coulombFormEnergy (N : ℕ) {β : ℝ} (hβ : 0 < β) (u : CoulombFormDomain N hβ) : ℝ :=
  ‖coulombFormGradientL N hβ u‖ ^ 2

end RepulsiveCoulomb

open PeriodicAttractiveLogGas
namespace RepulsiveCoulomb.PaperRoute

/-- A positive fixed-temperature labeled LSI rate depending only on `β` and its
positivity proof, fixed independently of particle count and observable. This is
a selected definition hole: Solution supplies the original actual thermal-reference
construction, while its internal formula is not fixed by this Challenge. -/
def paperOriginalLabeledRate {β : ℝ} (hβ : 0 < β) : ℝ := by sorry

theorem paperOriginalLabeledRate_pos {β : ℝ} (hβ : 0 < β) :
    0 < paperOriginalLabeledRate hβ := by sorry

theorem paper_full_labeled_lsi_original {β : ℝ} (hβ : 0 < β)
    (N : ℕ) (hN : 2 ≤ N) (u : CoulombFormDomain N hβ) :
    entropy (coulombMeasure N β) (fun z => (coulombFormValueL N hβ u z)^2) ≤
      (((2 / paperOriginalLabeledRate hβ) * coulombFormEnergy N hβ u : ℝ) : EReal) := by sorry

/-- A compact-temperature labeled LSI rate depending only on the interval endpoints
`a,b` and the proof `0 < a`, fixed before `β ∈ [a,b]`, particle count and observable.
Positivity is required when `a ≤ b`. This is a selected definition hole: Solution
supplies the original thermal-reference/family-supremum construction, while its
internal formula is not fixed by this Challenge. -/
def paperOriginalCompactLabeledRate {a b : ℝ} (ha : 0 < a) : ℝ := by sorry

theorem paperOriginalCompactLabeledRate_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 < paperOriginalCompactLabeledRate (b := b) ha := by sorry

theorem paper_uniform_labeled_lsi_original {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    0 < paperOriginalCompactLabeledRate (b := b) ha ∧
      ∀ (β : Set.Icc a b) (N : ℕ), 2 ≤ N →
        ∀ u : CoulombFormDomain N (ha.trans_le β.2.1),
          entropy (coulombMeasure N β.1)
            (fun z => (coulombFormValueL N (ha.trans_le β.2.1) u z)^2) ≤
            (((2 / paperOriginalCompactLabeledRate (b := b) ha) *
              coulombFormEnergy N (ha.trans_le β.2.1) u : ℝ) : EReal) := by sorry

end RepulsiveCoulomb.PaperRoute
