module

public import LeanResearch.RepulsiveCoulomb.MetricFlatPatchUniqueness
public import Mathlib.Analysis.Convex.Topology

@[expose] public section

/-! Post-freeze successor. Genuine germ uniqueness is propagated to a whole
closed convex rectangle, including its completed boundary, by continuity. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- Actual local chart geometry on the interior and an initial open agreement
force equality of two entire closed convex stages. No family compatibility is
an input or a conclusion hidden in a certificate. -/
theorem flat_isometries_eqOn_closed_convex_of_open_germ {Y : Type*} [MetricSpace Y]
    {K : Set ℂ} (hK : Convex ℝ K) (hclosed : IsClosed K) (hne : (interior K).Nonempty)
    {f g : ℂ → Y}
    (hf : ∀ x ∈ K, ∀ z ∈ K, dist (f x) (f z) = dist x z)
    (hg : ∀ x ∈ K, ∀ z ∈ K, dist (g x) (g z) = dist x z)
    (hcharts : ∀ x ∈ interior K, ∃ p : Y, ∃ C : MetricFlatDiskChart Y p,
      f x ∈ ball p C.radius)
    {V : Set ℂ} (hV : IsOpen V) (hVne : V.Nonempty) (hVK : V ⊆ interior K)
    (hagree : EqOn f g V) : EqOn f g K := by
  have hfi : ∀ x ∈ interior K, ∀ z ∈ interior K, dist (f x) (f z) = dist x z :=
    fun x hx z hz ↦ hf x (interior_subset hx) z (interior_subset hz)
  have hgi : ∀ x ∈ interior K, ∀ z ∈ interior K, dist (g x) (g z) = dist x z :=
    fun x hx z hz ↦ hg x (interior_subset hx) z (interior_subset hz)
  have heq := flat_isometries_eqOn_of_open_germ isOpen_interior hK.interior.isPreconnected
    hfi hgi hcharts hV hVne hVK hagree
  have hfl : LipschitzOnWith 1 f K := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx z hz
    simpa only [NNReal.coe_one, one_mul, hf x hx z hz] using (le_refl (dist x z))
  have hgl : LipschitzOnWith 1 g K := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx z hz
    simpa only [NNReal.coe_one, one_mul, hg x hx z hz] using (le_refl (dist x z))
  apply heq.of_subset_closure hfl.continuousOn hgl.continuousOn interior_subset
  rw [hK.closure_interior_eq_closure_of_nonempty_interior hne, hclosed.closure_eq]

end RepulsiveCoulomb
