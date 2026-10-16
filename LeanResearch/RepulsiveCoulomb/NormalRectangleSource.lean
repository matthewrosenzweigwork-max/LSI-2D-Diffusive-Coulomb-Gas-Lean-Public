module

public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
NEW shared source definition, extracted from the caller-observed contract of
lost MetricCleanRayCompactCollar. This is not a recovered historical module.
Both the horizontal and vertical intervals are closed. The source metric is
the inherited Euclidean metric on ℂ, not the product metric on ℝ × ℝ.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

def flatNormalRectangle (a b s : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc a b ∧ z.im ∈ Icc (0 : ℝ) s}

end RepulsiveCoulomb
