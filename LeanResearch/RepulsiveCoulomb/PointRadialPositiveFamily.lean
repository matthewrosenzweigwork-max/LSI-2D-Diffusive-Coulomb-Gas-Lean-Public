import LeanResearch.RepulsiveCoulomb.JordanFiniteCornerPositiveTraversal
import LeanResearch.RepulsiveCoulomb.PointRadialPlaneArcArgumentTurn

/-! Choose positive orientation while retaining the literal radial plane-arc
objects, source-derived geodesic argument transport and puncture-free open
edges. This is the actual-data adapter used before geometric Gauss--Bonnet. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_point_radial_positive_family
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (arcs : ℕ → PointRadialC1PlaneArc ha y) (n : ℕ)
    (hv : ∀ k < n, (arcs k).curve 1 = (arcs (k + 1)).curve 0)
    (hclose : (arcs n).curve 1 = (arcs 0).curve 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      (arcs i).curve s = (arcs j).curve t → i = j ∧ s = t)
    (harg : ∀ k ≤ n, (arcs k).HasArgumentTurn)
    (havoid : ∀ k ≤ n, ∀ t ∈ Ioo (0 : ℝ) 1, (arcs k).curve t ∉ pointPunctures a y)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hK : IsCompact (closure U))
    (hcover : U ∪ V = (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1)ᶜ) :
    ∃ B : ℕ → PointRadialC1PlaneArc ha y,
      (B = arcs ∨ B = fun k => (arcs (n - k)).reverse) ∧
      (∀ k < n, (B k).curve 1 = (B (k + 1)).curve 0) ∧
      (B n).curve 1 = (B 0).curve 0 ∧
      (∀ i j, i ≤ n → j ≤ n → ∀ s t,
        s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
        (B i).curve s = (B j).curve t → i = j ∧ s = t) ∧
      (∀ k ≤ n, (B k).HasArgumentTurn) ∧
      (∀ k ≤ n, ∀ t ∈ Ioo (0 : ℝ) 1, (B k).curve t ∉ pointPunctures a y) ∧
      (⋃ k ≤ n, (B k).curve '' Icc (0 : ℝ) 1) = (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1) ∧
      FiniteCornerPositiveInside (fun k => (B k).curve) n U := by
  obtain ⟨g, hcase, hg, hgv, hgc, hgi, hgr, himage, hplus⟩ :=
    exists_finite_corner_positive_traversal (fun k => (arcs k).curve) n
      (fun k _ => (arcs k).smooth) hv hclose hinj (fun k _ => (arcs k).regular)
      hU hUc hV hVc hK hcover
  rcases hcase with rfl | rfl
  · exact ⟨arcs, Or.inl rfl, hgv, hgc, hgi, harg, havoid, himage, hplus⟩
  · refine ⟨(fun k => (arcs (n - k)).reverse), Or.inr rfl,
      hgv, hgc, hgi, ?_, ?_, himage, hplus⟩
    · intro k hk
      exact (harg (n - k) (Nat.sub_le _ _)).reverse
    · intro k hk t ht
      exact havoid (n - k) (Nat.sub_le _ _) (1 - t)
        (by constructor <;> linarith [ht.1, ht.2])

end RepulsiveCoulomb
