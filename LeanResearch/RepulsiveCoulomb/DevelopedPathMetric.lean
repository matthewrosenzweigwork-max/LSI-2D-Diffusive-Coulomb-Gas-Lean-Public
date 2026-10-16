module

public import LeanResearch.RepulsiveCoulomb.MetricRegionPathBisection
public import LeanResearch.RepulsiveCoulomb.LocalMetricBoundGlobalization
public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Analysis.Complex.Norm

@[expose] public section

/-!
SOURCE-ONLY, UNCOMPILED, UNSTAGED.

The competitors are continuous in the ORIGINAL metric topology. Their length
is the Euclidean partition variation of D composed with the competitor. D is
not assumed injective, isometric, complete, or globally co-Lipschitz.
-/
noncomputable section
open Set Filter
open scoped ENNReal NNReal Topology
namespace RepulsiveCoulomb
variable {X : Type*} [MetricSpace X]

namespace MetricRegionLengthPath

/-- Compose an actual original-topology path with a continuous development. -/
def developed {x z : X} (γ : MetricRegionLengthPath (univ : Set X) x z)
    (D : X → ℂ) (hD : Continuous D) :
    MetricRegionLengthPath (univ : Set ℂ) (D x) (D z) where
  toFun := D ∘ γ.toFun
  continuous := hD.comp γ.continuous
  source := by simp only [Function.comp_apply, γ.source]
  target := by simp only [Function.comp_apply, γ.target]
  mapsTo := fun _ _ ↦ mem_univ _

end MetricRegionLengthPath

/-- Length measured in developed Euclidean coordinates, while continuity of
competitors is still measured in the original topology. -/
def developedPathLength (D : X → ℂ) {x z : X}
    (γ : MetricRegionLengthPath (univ : Set X) x z) : ℝ≥0∞ :=
  eVariationOn (D ∘ γ.toFun) (Icc (0 : ℝ) 1)

/-- The genuine intrinsic path infimum. No separation is built into its definition. -/
def developedPathEDist (D : X → ℂ) (x z : X) : ℝ≥0∞ :=
  ⨅ γ : MetricRegionLengthPath (univ : Set X) x z, developedPathLength D γ

theorem developedPathEDist_le_length (D : X → ℂ) {x z : X}
    (γ : MetricRegionLengthPath (univ : Set X) x z) :
    developedPathEDist D x z ≤ developedPathLength D γ := iInf_le _ γ

theorem developed_edist_le_length (D : X → ℂ) {x z : X}
    (γ : MetricRegionLengthPath (univ : Set X) x z) :
    edist (D x) (D z) ≤ developedPathLength D γ := by
  simpa only [developedPathLength, Function.comp_apply, γ.source, γ.target] using
    eVariationOn.edist_le (D ∘ γ.toFun) (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      (by norm_num : (1 : ℝ) ∈ Icc 0 1)

theorem developed_edist_le_pathEDist (D : X → ℂ) (x z : X) :
    edist (D x) (D z) ≤ developedPathEDist D x z :=
  le_iInf fun γ ↦ developed_edist_le_length D γ

theorem developedPathEDist_self (D : X → ℂ) (x : X) :
    developedPathEDist D x x = 0 := by
  apply le_antisymm _ bot_le
  apply (developedPathEDist_le_length D
    (MetricRegionLengthPath.const (mem_univ x))).trans_eq
  simp [developedPathLength, MetricRegionLengthPath.const, eVariationOn]

theorem developedPathLength_reverse (D : X → ℂ) {x z : X}
    (γ : MetricRegionLengthPath (univ : Set X) x z) :
    developedPathLength D γ.reverse = developedPathLength D γ := by
  have h := eVariationOn_affine_unitInterval (D ∘ γ.toFun) 1 0
  simpa only [developedPathLength, MetricRegionLengthPath.reverse,
    Function.comp_def, zero_sub, mul_neg, mul_one, ← sub_eq_add_neg,
    uIcc_of_ge (by norm_num : (0 : ℝ) ≤ 1)] using h

theorem developedPathLength_subpath (D : X → ℂ) {x z : X}
    (γ : MetricRegionLengthPath (univ : Set X) x z) (s t : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    developedPathLength D (γ.subpath s t hs ht) =
      eVariationOn (D ∘ γ.toFun) (uIcc s t) :=
  eVariationOn_affine_unitInterval (D ∘ γ.toFun) s t

theorem developedPathEDist_comm (D : X → ℂ) (x z : X) :
    developedPathEDist D x z = developedPathEDist D z x := by
  have h (x z : X) : developedPathEDist D x z ≤ developedPathEDist D z x := by
    apply le_iInf
    intro γ
    exact (developedPathEDist_le_length D γ.reverse).trans_eq
      (developedPathLength_reverse D γ)
  exact le_antisymm (h x z) (h z x)

theorem developedPathLength_trans_le (D : X → ℂ) (hD : Continuous D)
    {x y z : X} (γ : MetricRegionLengthPath (univ : Set X) x y)
    (η : MetricRegionLengthPath (univ : Set X) y z) :
    developedPathLength D (γ.trans η) ≤
      developedPathLength D γ + developedPathLength D η := by
  have heq : developedPathLength D (γ.trans η) =
      ((γ.developed D hD).trans (η.developed D hD)).length := by
    apply eVariationOn.eq_of_eqOn
    intro t _
    change D (if t ≤ 1 / 2 then γ.toFun (2 * t) else η.toFun (2 * t - 1)) =
      if t ≤ 1 / 2 then D (γ.toFun (2 * t)) else D (η.toFun (2 * t - 1))
    split_ifs <;> rfl
  rw [heq]
  exact (γ.developed D hD).length_trans_le (η.developed D hD)

theorem developedPathEDist_triangle (D : X → ℂ) (hD : Continuous D) (x y z : X) :
    developedPathEDist D x z ≤ developedPathEDist D x y + developedPathEDist D y z := by
  apply ENNReal.le_iInf_add_iInf
  intro γ η
  exact (developedPathEDist_le_length D (γ.trans η)).trans
    (developedPathLength_trans_le D hD γ η)

/-- Compactness supplies a finite open-cover subdivision of each actual path.
The lower estimate is accumulated only over that subdivision, with no bound
on seam crossings and no globally uniform chart radius. -/
theorem local_lower_le_developedPathLength (D : X → ℂ) (c : ℝ≥0)
    (hlower : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ u ∈ U, ∀ v ∈ U, (c : ℝ≥0∞) * edist u v ≤ edist (D u) (D v))
    {x z : X} (γ : MetricRegionLengthPath (univ : Set X) x z) :
    (c : ℝ≥0∞) * edist x z ≤ developedPathLength D γ := by
  classical
  choose U hU hm hd using hlower
  let f : Icc (0 : ℝ) 1 → X := fun t ↦ γ.toFun t.1
  have hf : Continuous f := γ.continuous.comp continuous_subtype_val
  obtain ⟨p, hp0, hpmono, ⟨N, hN⟩, hp⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc (by norm_num : (0 : ℝ) ≤ 1)
      (c := fun i ↦ f ⁻¹' U i) (fun i ↦ (hU i).preimage hf) (by
        intro t _
        exact mem_iUnion.mpr ⟨f t, hm (f t)⟩)
  have hstep (n : ℕ) : (c : ℝ≥0∞) * edist (f (p n)) (f (p (n + 1))) ≤
      edist (D (f (p (n + 1)))) (D (f (p n))) := by
    obtain ⟨i, hi⟩ := hp n
    have hn := hpmono (Nat.le_succ n)
    have hl := hi (show p n ∈ Icc (p n) (p (n + 1)) from ⟨le_rfl, hn⟩)
    have hr := hi (show p (n + 1) ∈ Icc (p n) (p (n + 1)) from ⟨hn, le_rfl⟩)
    simpa only [edist_comm] using hd i _ hl _ hr
  have hpoly := mul_le_mul_right (edist_le_range_sum_edist (f ∘ p) N) (c : ℝ≥0∞)
  rw [Finset.mul_sum] at hpoly
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun n _ ↦ hstep n)
  have hvar := eVariationOn.sum_le (f := D ∘ γ.toFun)
    (show Monotone (fun n ↦ (p n).1) from fun i j hij ↦ hpmono hij)
    (fun n ↦ (p n).2) (n := N)
  have hbound := hpoly.trans (hsum.trans hvar)
  have hfirst : f (p 0) = x := by change γ.toFun (p 0).1 = x; rw [hp0, γ.source]
  have hlast : f (p N) = z := by change γ.toFun (p N).1 = z; rw [hN N le_rfl, γ.target]
  simpa only [developedPathLength, Function.comp_apply, hfirst, hlast] using hbound

theorem local_lower_le_developedPathEDist (D : X → ℂ) (c : ℝ≥0)
    (hlower : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ u ∈ U, ∀ v ∈ U, (c : ℝ≥0∞) * edist u v ≤ edist (D u) (D v))
    (x z : X) : (c : ℝ≥0∞) * edist x z ≤ developedPathEDist D x z :=
  le_iInf fun γ ↦ local_lower_le_developedPathLength D c hlower γ

/-- The only source-geometric premise: literal minimizing paths for the OLD
metric. It is proved for the original conformal plane in PointConformalGeodesic. -/
def HasMinimizingSegments (X : Type*) [MetricSpace X] : Prop :=
  ∀ x z : X, ∃ γ : Icc (0 : ℝ) 1 → X,
    γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
    ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z

/-- A real-line representative of an OLD minimizing segment has precisely
its endpoint distance as genuine partition-variation length. -/
theorem exists_minimizing_lengthPath (hsegment : HasMinimizingSegments X) (x z : X) :
    ∃ γ : MetricRegionLengthPath (univ : Set X) x z, γ.length = edist x z := by
  obtain ⟨η, h0, h1, hc, hd⟩ := hsegment x z
  let f := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) η
  have hfc : Continuous f := continuous_IccExtend_iff.mpr hc
  have hf0 : f 0 = x := (IccExtend_of_mem _ _ (by norm_num)).trans h0
  have hf1 : f 1 = z := (IccExtend_of_mem _ _ (by norm_num)).trans h1
  let γ : MetricRegionLengthPath (univ : Set X) x z :=
    ⟨f, hfc, hf0, hf1, fun _ _ ↦ mem_univ _⟩
  have hLip : LipschitzOnWith (nndist x z) f (Icc (0 : ℝ) 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    dsimp only [f]
    rw [IccExtend_of_mem _ _ hs, IccExtend_of_mem _ _ ht, hd]
    simp only [coe_nndist, Real.dist_eq, abs_sub_comm, mul_comm, le_refl]
  have hvar := hLip.comp_eVariationOn_le (g := id) (s := Icc (0 : ℝ) 1)
    (fun t ht ↦ ht)
  have hu : γ.length ≤ edist x z := by
    simpa only [MetricRegionLengthPath.length, Function.comp_id, eVariationOn_id_Icc,
      sub_zero, ENNReal.ofReal_one, mul_one, coe_nnreal_ennreal_nndist] using hvar
  exact ⟨γ, le_antisymm hu γ.endpoint_le_length⟩

theorem developedPathEDist_le_edist (D : X → ℂ)
    (hsegment : HasMinimizingSegments X)
    (hupper : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ u ∈ U, ∀ v ∈ U, dist (D u) (D v) ≤ dist u v) (x z : X) :
    developedPathEDist D x z ≤ edist x z := by
  have hLip : LipschitzWith 1 D :=
    lipschitzWith_of_local_dist_bound_of_segments hsegment (by simpa using hupper)
  obtain ⟨γ, hγ⟩ := exists_minimizing_lengthPath hsegment x z
  have hvar := hLip.lipschitzOnWith.comp_eVariationOn_le
    (g := γ.toFun) (s := Icc (0 : ℝ) 1) (fun _ _ ↦ mem_univ _)
  change developedPathLength D γ ≤ (1 : ℝ≥0∞) * γ.length at hvar
  exact (developedPathEDist_le_length D γ).trans (by simpa only [one_mul, hγ] using hvar)

/-- Separation follows from the strictly positive local lower constant. -/
@[instance_reducible] def developedPathEMetricSpace (D : X → ℂ) (hD : Continuous D)
    (c : ℝ≥0) (hc : 0 < c)
    (hlower : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ u ∈ U, ∀ v ∈ U, (c : ℝ≥0∞) * edist u v ≤ edist (D u) (D v)) :
    EMetricSpace X where
  edist := developedPathEDist D
  edist_self := developedPathEDist_self D
  edist_comm := developedPathEDist_comm D
  edist_triangle := developedPathEDist_triangle D hD
  eq_of_edist_eq_zero := by
    intro x z heq
    have h := local_lower_le_developedPathEDist D c hlower x z
    rw [heq] at h
    have hz : (c : ℝ≥0∞) * edist x z = 0 := le_antisymm h bot_le
    have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
    exact edist_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hc')

/-- Finiteness is derived from OLD minimizing paths before taking toReal. -/
@[instance_reducible] def developedPathMetricSpace (D : X → ℂ) (hD : Continuous D)
    (c : ℝ≥0) (hc : 0 < c) (hsegment : HasMinimizingSegments X)
    (hlower : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ u ∈ U, ∀ v ∈ U, (c : ℝ≥0∞) * edist u v ≤ edist (D u) (D v))
    (hupper : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ u ∈ U, ∀ v ∈ U, dist (D u) (D v) ≤ dist u v) : MetricSpace X :=
  have hfin : ∀ x z : X, developedPathEDist D x z ≠ ⊤ := fun x z ↦
    ne_top_of_le_ne_top (edist_ne_top x z) (developedPathEDist_le_edist D hsegment hupper x z)
  letI := developedPathEMetricSpace D hD c hc hlower
  EMetricSpace.toMetricSpace hfin

end RepulsiveCoulomb
