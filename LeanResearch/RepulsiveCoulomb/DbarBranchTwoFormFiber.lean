module

public import LeanResearch.RepulsiveCoulomb.LabeledCoulombModel

@[expose] public section

/-! The fixed Hilbert fiber of alternating two-form coefficients is indexed
by i<j. Its norm is distinct from the ordinary matrix norm. -/
noncomputable section
namespace RepulsiveCoulomb

abbrev CoulombAuxiliaryTwoForm (N : ℕ) := EuclideanSpace ℂ (coulombPairs N)

end RepulsiveCoulomb
