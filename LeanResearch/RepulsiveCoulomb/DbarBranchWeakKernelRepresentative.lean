import LeanResearch.RepulsiveCoulomb.DbarBranchWeakKernelLocalRegularity
import LeanResearch.RepulsiveCoulomb.DbarBranchWeakKernelProjection
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Genuine global holomorphic representatives of the actual weighted-L2
weak kernel, obtained by local mollification and countable gluing. This
forward regularity theorem holds for every N and beta>0. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombWeakKernel_holomorphic_representative {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℂ 2 (coulombMeasure N β)) (hf : (f, 0) ∈ coulombMaxDbarGraph hβ) :
    ∃ h : CoulombConfig N → ℂ, DifferentiableOn ℂ h (coulombDomain N) ∧
      f =ᵐ[coulombMeasure N β] h := by
  classical
  choose r hr hsub g hg hrep using
    (fun c : (coulombDomain N) => coulombWeakKernel_local_holomorphic_representative hβ f hf c c.property)
  let U : (coulombDomain N) → Set (CoulombConfig N) := fun c => ball c (r c)
  have hopen (c : (coulombDomain N)) : IsOpen (U c) := isOpen_ball
  have hoverlap (a b : (coulombDomain N)) : EqOn (g a) (g b) (U a ∩ U b) := by
    have ha : f =ᵐ[volume.restrict (U a ∩ U b)] g a :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hrep a)
    have hb : f =ᵐ[volume.restrict (U a ∩ U b)] g b :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hrep b)
    exact Measure.eqOn_open_of_ae_eq (ha.symm.trans hb) ((hopen a).inter (hopen b))
      ((hg a).continuousOn.mono inter_subset_left) ((hg b).continuousOn.mono inter_subset_right)
  let h : CoulombConfig N → ℂ := fun z => if hz : z ∈ coulombDomain N then g ⟨z, hz⟩ z else 0
  have heq (a : (coulombDomain N)) : EqOn h (g a) (U a) := by
    intro z hz
    have hzΩ : z ∈ coulombDomain N := hsub a hz
    change (if hz : z ∈ coulombDomain N then g ⟨z, hz⟩ z else 0) = g a z
    rw [dif_pos hzΩ]
    exact hoverlap ⟨z, hzΩ⟩ a ⟨mem_ball_self (hr ⟨z, hzΩ⟩), hz⟩
  have hh : DifferentiableOn ℂ h (coulombDomain N) := by
    intro z hz
    let a : (coulombDomain N) := ⟨z, hz⟩
    have hza : z ∈ U a := mem_ball_self (hr a)
    exact (((hg a).congr (heq a) z hza).differentiableAt
      ((hopen a).mem_nhds hza)).differentiableWithinAt
  have hlocal (a : (coulombDomain N)) : f =ᵐ[volume.restrict (U a)] h := by
    filter_upwards [hrep a, ae_restrict_mem (hopen a).measurableSet] with z hfz hz
    exact hfz.trans (heq a hz).symm
  have hcover : (coulombDomain N : Set (CoulombConfig N)) ⊆ ⋃ a, U a := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hr ⟨z, hz⟩)⟩
  obtain ⟨A, hAc, hAcov⟩ :=
    (HereditarilyLindelofSpace.isLindelof (coulombDomain N : Set (CoulombConfig N))).elim_countable_subcover U hopen hcover
  have hcountable : f =ᵐ[volume.restrict (⋃ a ∈ A, U a)] h :=
    (ae_eq_restrict_biUnion_iff U hAc f h).mpr (fun a _ => hlocal a)
  have hΩ : f =ᵐ[volume.restrict (coulombDomain N)] h :=
    ae_restrict_of_ae_restrict_of_subset hAcov hcountable
  have hv : f =ᵐ[volume] h := by
    filter_upwards [(ae_restrict_iff' (coulombDomain N).isOpen.measurableSet).mp hΩ,
      coulombDomain_ae N] with z he hz
    exact he hz
  exact ⟨h, hh, (coulombMeasure_ae_iff hβ).mpr hv⟩

theorem coulombHolomorphic_representative_unique {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {g h : CoulombConfig N → ℂ}
    (hg : DifferentiableOn ℂ g (coulombDomain N)) (hh : DifferentiableOn ℂ h (coulombDomain N))
    (heq : g =ᵐ[coulombMeasure N β] h) : EqOn g h (coulombDomain N) :=
  Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae ((coulombMeasure_ae_iff hβ).mp heq))
    (coulombDomain N).isOpen hg.continuousOn hh.continuousOn

theorem coulombDbarWeakProjection_holomorphic {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℂ 2 (coulombMeasure N β)) :
    ∃ h : CoulombConfig N → ℂ, DifferentiableOn ℂ h (coulombDomain N) ∧
      coulombDbarWeakProjection N hβ f =ᵐ[coulombMeasure N β] h :=
  coulombWeakKernel_holomorphic_representative hβ _
    ((coulombDbarWeakKernel_mem_iff hβ _).mp
      (coulombDbarWeakProjection_mem_kernel hβ f))

end RepulsiveCoulomb
