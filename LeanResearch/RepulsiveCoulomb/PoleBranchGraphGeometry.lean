module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Order.Interval.Set.Infinite

@[expose] public section

/-! Geometry needed for finite-graph Hartogs continuation. Distinct linear graph
heights are distinct on a dense set of transverse parameters. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

def poleBranchGraphRegular {ι E : Type*} (L : ι → E → ℂ) : Set (E × ℂ) :=
  {q | ∀ i j, i ≠ j → q.2 ≠ L i q.1 ∨ q.2 ≠ L j q.1}

theorem poleBranch_graphRegular_isOpen
    {ι E : Type*} [Finite ι] [TopologicalSpace E] (L : ι → E → ℂ)
    (hL : ∀ i, Continuous (L i)) : IsOpen (poleBranchGraphRegular L) := by
  simp only [poleBranchGraphRegular, setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro hij
  exact (isOpen_ne_fun continuous_snd ((hL i).comp continuous_fst)).union
    (isOpen_ne_fun continuous_snd ((hL j).comp continuous_fst))

theorem poleBranch_dense_nonzero_linear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E →L[ℂ] ℂ) (hL : L ≠ 0) : Dense {x | L x ≠ 0} := by
  have hker : interior (L.ker : Set E) = ∅ := by
    by_contra h
    have htop := L.ker.eq_top_of_nonempty_interior' (nonempty_iff_ne_empty.mpr h)
    have hzero := LinearMap.ker_eq_top.mp htop
    apply hL
    ext x
    exact LinearMap.congr_fun hzero x
  have he : (L.ker : Set E)ᶜ = {x | L x ≠ 0} := by
    ext x
    rfl
  rw [← he]
  exact interior_eq_empty_iff_dense_compl.mp hker

theorem poleBranch_dense_distinct_linear_heights
    {ι E : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (L : ι → E →L[ℂ] ℂ) (hL : Function.Injective L) :
    Dense {p : E | Function.Injective (fun i => L i p)} := by
  classical
  letI : ProperSpace E := FiniteDimensional.proper ℂ E
  let J := {ij : ι × ι // ij.1 ≠ ij.2}
  have ho : ∀ ij : J, IsOpen {p : E | L ij.1.1 p ≠ L ij.1.2 p} :=
    fun ij => isOpen_ne_fun (L ij.1.1).continuous (L ij.1.2).continuous
  have hd : ∀ ij : J, Dense {p : E | L ij.1.1 p ≠ L ij.1.2 p} := by
    intro ij
    have hn : L ij.1.1 - L ij.1.2 ≠ 0 := sub_ne_zero.mpr (fun h => ij.2 (hL h))
    simpa only [ContinuousLinearMap.sub_apply, sub_ne_zero] using
      poleBranch_dense_nonzero_linear (L ij.1.1 - L ij.1.2) hn
  have H := dense_iInter_of_isOpen ho hd
  apply H.mono
  intro p hp i j hij
  by_contra hne
  have := mem_iInter.mp hp (⟨(i, j), hne⟩ : J)
  exact this hij

theorem poleBranch_exists_graph_contour
    {ι E : Type*} [Finite ι] (L : ι → E → ℂ) (p : E) (c : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, dist (L i p) c ≠ r := by
  obtain ⟨r, hr, havoid⟩ := (Ioo_infinite (by norm_num : (0 : ℝ) < 1)).exists_notMem_finite
    (finite_range (fun i => dist (L i p) c))
  exact ⟨r, hr.1, fun i h => havoid ⟨i, h⟩⟩

end RepulsiveCoulomb
