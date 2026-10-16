import LeanResearch.RepulsiveCoulomb.CenteredLocalMetricGlobalization
import LeanResearch.RepulsiveCoulomb.FiniteClosedPieceOpenChart
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Order.Filter.Finite

/-! SOURCE-ONLY, UNCOMPILED. Sharp metric estimates for actual finite pastes.
Finite closedness gives an incident-piece neighborhood at each center. This
is enough for centered-local globalization and does not assert a pairwise
estimate on one common neighborhood before proving it. Covers are finite;
the number of crossings of a curve through their boundaries is unrestricted.
The convex-domain wrappers construct the necessary segments explicitly. -/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace RepulsiveCoulomb

/-- Near a point, only closed cover members which contain that point can
occur. No cover hypothesis is needed for this finite-family fact. -/
theorem finiteClosedFamily_eventually_incident
    {ι X : Type*} [Finite ι] [TopologicalSpace X]
    (S : ι → Set X) (hclosed : ∀ i, IsClosed (S i)) (x : X) :
    ∀ᶠ y in 𝓝 x, ∀ i, y ∈ S i → x ∈ S i := by
  classical
  apply Filter.eventually_all.mpr
  intro i
  by_cases hx : x ∈ S i
  · exact Filter.Eventually.of_forall (fun _ _ ↦ hx)
  · filter_upwards [(hclosed i).isOpen_compl.mem_nhds hx] with y hy hys
    exact (hy hys).elim

/-- Piecewise sharp estimates produce a genuinely centered local estimate
for the same actual map. Points on several seams cause no ambiguity. -/
theorem centered_local_bound_of_finite_closed_cover
    {ι X Y : Type*} [Finite ι] [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {K : ℝ≥0} {F : X → Y} (S : ι → Set X)
    (hclosed : ∀ i, IsClosed (S i)) (hcover : ∀ x, ∃ i, x ∈ S i)
    (hbound : ∀ i, LipschitzOnWith K F (S i)) :
    ∀ x, ∀ᶠ y in 𝓝 x, dist (F x) (F y) ≤ K * dist x y := by
  intro x
  filter_upwards [finiteClosedFamily_eventually_incident S hclosed x] with y hy
  obtain ⟨i, hi⟩ := hcover y
  exact (hbound i).dist_le_mul x (hy i hi) y hi

/-- The sharp branch constant globalizes on a source with genuine minimizing
segments. The function is estimated from its restrictions, rather than
being assumed globally Lipschitz. -/
theorem lipschitzWith_of_finite_closed_cover_of_segments
    {ι X Y : Type*} [Finite ι] [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {K : ℝ≥0} {F : X → Y} (S : ι → Set X)
    (hclosed : ∀ i, IsClosed (S i)) (hcover : ∀ x, ∃ i, x ∈ S i)
    (hbound : ∀ i, LipschitzOnWith K F (S i))
    (hsegment : ∀ x z : X, ∃ γ : Icc (0 : ℝ) 1 → X,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z) :
    LipschitzWith K F :=
  lipschitzWith_of_centered_local_dist_bound_of_segments hsegment
    (centered_local_bound_of_finite_closed_cover S hclosed hcover hbound)

/-- Applied to the chosen actual paste, branch agreement transports the
individual estimates before any global bound is concluded. -/
theorem finiteCoverGlue_lipschitzWith_of_segments
    {ι X Y : Type*} [Finite ι] [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {K : ℝ≥0} (S : ι → Set X) (hclosed : ∀ i, IsClosed (S i))
    (hcover : ∀ x, ∃ i, x ∈ S i) (f : ι → X → Y)
    (hagrees : ∀ i j x, x ∈ S i → x ∈ S j → f i x = f j x)
    (hbound : ∀ i, LipschitzOnWith K (f i) (S i))
    (hsegment : ∀ x z : X, ∃ γ : Icc (0 : ℝ) 1 → X,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z) :
    LipschitzWith K (finiteCoverGlue S hcover f) := by
  apply lipschitzWith_of_finite_closed_cover_of_segments S hclosed hcover
    (hsegment := hsegment)
  intro i
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx z hz
  rw [finiteCoverGlue_eq S hcover f hagrees hx,
    finiteCoverGlue_eq S hcover f hagrees hz]
  exact (hbound i).dist_le_mul x hx z hz

/-- Relative closedness is sufficient on a domain. Only paths contained in
that domain are used; no metric on a quotient or intrinsic-distance change
is introduced. -/
theorem lipschitzOnWith_of_finite_closed_cover_of_segmentsWithin
    {ι X Y : Type*} [Finite ι] [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {K : ℝ≥0} {F : X → Y} (U : Set X) (S : ι → Set X)
    (hclosed : ∀ i, IsClosed {x : U | x.1 ∈ S i})
    (hcover : ∀ x ∈ U, ∃ i, x ∈ S i)
    (hbound : ∀ i, LipschitzOnWith K F (U ∩ S i))
    (hsegment : ∀ x ∈ U, ∀ z ∈ U, ∃ γ : Icc (0 : ℝ) 1 → X,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      (∀ t, γ t ∈ U) ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z) :
    LipschitzOnWith K F U := by
  let P : ι → Set U := fun i ↦ {x | x.1 ∈ S i}
  have hcover' : ∀ x : U, ∃ i, x ∈ P i := fun x ↦ hcover x.1 x.2
  have hbound' : ∀ i, LipschitzOnWith K (fun x : U ↦ F x.1) (P i) := by
    intro i
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx z hz
    exact (hbound i).dist_le_mul x.1 ⟨x.2, hx⟩ z.1 ⟨z.2, hz⟩
  have hsegment' : ∀ x z : U, ∃ γ : Icc (0 : ℝ) 1 → U,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z := by
    intro x z
    obtain ⟨γ, h0, h1, hγ, hmem, hd⟩ := hsegment x.1 x.2 z.1 z.2
    refine ⟨fun t ↦ ⟨γ t, hmem t⟩, Subtype.ext h0, Subtype.ext h1,
      hγ.subtype_mk _, ?_⟩
    exact hd
  have h := lipschitzWith_of_finite_closed_cover_of_segments
    P hclosed hcover' hbound' hsegment'
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx z hz
  exact h.dist_le_mul ⟨x, hx⟩ ⟨z, hz⟩

/-- Actual-paste version on a relative closed cover of a local domain. -/
theorem finiteCoverGlueWithin_lipschitzOnWith_of_segmentsWithin
    {ι X Y : Type*} [Finite ι] [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {K : ℝ≥0} (U : Set X) (S : ι → Set X)
    (hclosed : ∀ i, IsClosed {x : U | x.1 ∈ S i})
    (hcover : ∀ x ∈ U, ∃ i, x ∈ S i) (f : ι → X → Y) (fallback : Y)
    (hagrees : ∀ i j x, x ∈ U → x ∈ S i → x ∈ S j → f i x = f j x)
    (hbound : ∀ i, LipschitzOnWith K (f i) (U ∩ S i))
    (hsegment : ∀ x ∈ U, ∀ z ∈ U, ∃ γ : Icc (0 : ℝ) 1 → X,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      (∀ t, γ t ∈ U) ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z) :
    LipschitzOnWith K (finiteCoverGlueWithin U S hcover f fallback) U := by
  apply lipschitzOnWith_of_finite_closed_cover_of_segmentsWithin U S hclosed hcover
    (hsegment := hsegment)
  intro i
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx z hz
  rw [finiteCoverGlueWithin_eq U S hcover f fallback hagrees hx.1 hx.2,
    finiteCoverGlueWithin_eq U S hcover f fallback hagrees hz.1 hz.2]
  exact (hbound i).dist_le_mul x hx z hz

/-- Euclidean/real normed convex-domain wrapper, with minimizing segments
constructed here rather than packaged as an extra surgery input. -/
theorem lipschitzOnWith_of_finite_closed_cover_of_convex
    {ι E Y : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [PseudoMetricSpace Y] {K : ℝ≥0} {F : E → Y}
    (U : Set E) (hU : Convex ℝ U) (S : ι → Set E)
    (hclosed : ∀ i, IsClosed {x : U | x.1 ∈ S i})
    (hcover : ∀ x ∈ U, ∃ i, x ∈ S i)
    (hbound : ∀ i, LipschitzOnWith K F (U ∩ S i)) :
    LipschitzOnWith K F U :=
  lipschitzOnWith_of_finite_closed_cover_of_segmentsWithin U S hclosed hcover hbound
    (fun _ hx _ hz ↦ exists_minimizing_segment_of_convex hU hx hz)

/-- In particular, the actual local surgery paste inherits the sharp
constant of its finite Euclidean branches on every convex old domain. -/
theorem finiteCoverGlueWithin_lipschitzOnWith_of_convex
    {ι E Y : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [PseudoMetricSpace Y] {K : ℝ≥0}
    (U : Set E) (hU : Convex ℝ U) (S : ι → Set E)
    (hclosed : ∀ i, IsClosed {x : U | x.1 ∈ S i})
    (hcover : ∀ x ∈ U, ∃ i, x ∈ S i) (f : ι → E → Y) (fallback : Y)
    (hagrees : ∀ i j x, x ∈ U → x ∈ S i → x ∈ S j → f i x = f j x)
    (hbound : ∀ i, LipschitzOnWith K (f i) (U ∩ S i)) :
    LipschitzOnWith K (finiteCoverGlueWithin U S hcover f fallback) U :=
  finiteCoverGlueWithin_lipschitzOnWith_of_segmentsWithin U S hclosed hcover f fallback
    hagrees hbound (fun _ hx _ hz ↦ exists_minimizing_segment_of_convex hU hx hz)

/-- Unit bounds on the actual forward and inverse pastes imply an isometry
on the actual trimmed source. Only the inverse identity is assumed here;
the open-chart constructor proves it from branchwise inverse data. The
trimmed source need not be convex. -/
theorem finiteCoverGlueWithin_isometry_of_convex_unit_bounds
    {ι κ E H : Type*} [Finite ι] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (U : Set E) (V : Set H) (hU : Convex ℝ U) (hV : Convex ℝ V)
    (S : ι → Set E) (T : κ → Set H)
    (hSclosed : ∀ i, IsClosed {x : U | x.1 ∈ S i})
    (hTclosed : ∀ j, IsClosed {y : V | y.1 ∈ T j})
    (hScover : ∀ x ∈ U, ∃ i, x ∈ S i)
    (hTcover : ∀ y ∈ V, ∃ j, y ∈ T j)
    (f : ι → E → H) (g : κ → H → E) (x₀ : E) (y₀ : H)
    (hfseam : ∀ i j x, x ∈ U → x ∈ S i → x ∈ S j → f i x = f j x)
    (hgseam : ∀ i j y, y ∈ V → y ∈ T i → y ∈ T j → g i y = g j y)
    (hf : ∀ i, LipschitzOnWith 1 (f i) (U ∩ S i))
    (hg : ∀ j, LipschitzOnWith 1 (g j) (V ∩ T j))
    (hleft : ∀ x ∈ U,
      finiteCoverGlueWithin U S hScover f y₀ x ∈ V →
      finiteCoverGlueWithin V T hTcover g x₀
        (finiteCoverGlueWithin U S hScover f y₀ x) = x) :
    Isometry (fun x : ↥(U ∩ (finiteCoverGlueWithin U S hScover f y₀) ⁻¹' V) ↦
      finiteCoverGlueWithin U S hScover f y₀ x.1) := by
  have hF := finiteCoverGlueWithin_lipschitzOnWith_of_convex
    U hU S hSclosed hScover f y₀ hfseam hf
  have hG := finiteCoverGlueWithin_lipschitzOnWith_of_convex
    V hV T hTclosed hTcover g x₀ hgseam hg
  apply Isometry.of_dist_eq
  intro x z
  change dist (finiteCoverGlueWithin U S hScover f y₀ x.1)
    (finiteCoverGlueWithin U S hScover f y₀ z.1) = dist x.1 z.1
  apply le_antisymm
  · simpa only [NNReal.coe_one, one_mul] using
      hF.dist_le_mul x.1 x.2.1 z.1 z.2.1
  · have h := hG.dist_le_mul
      (finiteCoverGlueWithin U S hScover f y₀ x.1) x.2.2
      (finiteCoverGlueWithin U S hScover f y₀ z.1) z.2.2
    simpa only [hleft x.1 x.2.1 x.2.2, hleft z.1 z.2.1 z.2.2,
      NNReal.coe_one, one_mul] using h

/-- The final elementary squeeze used for chart transitions. The forward
and inverse bounds are only needed on larger comparison neighborhoods;
the actual chart source itself need not be convex. -/
theorem openPartialHomeomorph_dist_eq_of_unit_bounds
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (e : OpenPartialHomeomorph X Y) {U : Set X} {V : Set Y}
    (hsource : e.source ⊆ U) (htarget : e.target ⊆ V)
    (hf : LipschitzOnWith 1 e U) (hg : LipschitzOnWith 1 e.symm V)
    {x z : X} (hx : x ∈ e.source) (hz : z ∈ e.source) :
    dist (e x) (e z) = dist x z := by
  apply le_antisymm
  · simpa only [NNReal.coe_one, one_mul] using
      hf.dist_le_mul x (hsource hx) z (hsource hz)
  · have h := hg.dist_le_mul (e x) (htarget (e.map_source hx))
      (e z) (htarget (e.map_source hz))
    simpa only [e.left_inv hx, e.left_inv hz, NNReal.coe_one, one_mul] using h

/-- A genuinely homeomorphic transition with finite unit-Lipschitz branch
covers in both directions is isometric on its actual source. This theorem
constructs both metric bounds from the covers. It assumes neither an
isometric transition nor a final atlas. -/
theorem openPartialHomeomorph_isometry_of_finite_closed_covers_of_convex
    {ι κ E H : Type*} [Finite ι] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (e : OpenPartialHomeomorph E H)
    (U : Set E) (V : Set H) (hU : Convex ℝ U) (hV : Convex ℝ V)
    (hsource : e.source ⊆ U) (htarget : e.target ⊆ V)
    (S : ι → Set E) (T : κ → Set H)
    (hSclosed : ∀ i, IsClosed {x : U | x.1 ∈ S i})
    (hTclosed : ∀ j, IsClosed {y : V | y.1 ∈ T j})
    (hScover : ∀ x ∈ U, ∃ i, x ∈ S i)
    (hTcover : ∀ y ∈ V, ∃ j, y ∈ T j)
    (hf : ∀ i, LipschitzOnWith 1 e (U ∩ S i))
    (hg : ∀ j, LipschitzOnWith 1 e.symm (V ∩ T j)) :
    Isometry (fun x : e.source ↦ e x.1) := by
  have hF := lipschitzOnWith_of_finite_closed_cover_of_convex U hU S hSclosed hScover hf
  have hG := lipschitzOnWith_of_finite_closed_cover_of_convex V hV T hTclosed hTcover hg
  apply Isometry.of_dist_eq
  intro x z
  exact openPartialHomeomorph_dist_eq_of_unit_bounds e hsource htarget hF hG x.2 z.2

end RepulsiveCoulomb
