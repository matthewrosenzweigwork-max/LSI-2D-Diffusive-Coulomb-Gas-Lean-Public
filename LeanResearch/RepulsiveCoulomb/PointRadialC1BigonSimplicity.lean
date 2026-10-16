import LeanResearch.RepulsiveCoulomb.PointRadialC1BigonCyclicChain
import Mathlib.Data.List.Pairwise

/-! Actual joint half-open injectivity for the cyclic macro-list. The two
sides meet only at the actual bigon endpoints, and opposite half-open
conventions allocate each shared endpoint to exactly one side. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem simple_bigon_halfOpen_images_disjoint {γ₁ γ₂ : Icc (0 : ℝ) 1 → ℂ}
    {p q : ℂ} (hi₁ : Function.Injective γ₁) (hi₂ : Function.Injective γ₂)
    (h11 : γ₁ ⟨1, by norm_num⟩ = q) (h20 : γ₂ ⟨0, by norm_num⟩ = p)
    (hmeet : range γ₁ ∩ range γ₂ = {p, q}) :
    Disjoint (γ₁ '' Ico (0 : Icc (0 : ℝ) 1) 1) (γ₂ '' Ioc (0 : Icc (0 : ℝ) 1) 1) := by
  apply disjoint_left.mpr
  rintro z ⟨s, hs, hsz⟩ ⟨t, ht, htz⟩
  have hz : z ∈ range γ₁ ∩ range γ₂ := ⟨⟨s, hsz⟩, ⟨t, htz⟩⟩
  rw [hmeet] at hz
  rcases mem_insert_iff.mp hz with hzp | hzq
  · have he : t = ⟨0, by norm_num⟩ := hi₂ ((htz.trans hzp).trans h20.symm)
    exact ht.1.ne' he
  · have he : s = ⟨1, by norm_num⟩ := hi₁ ((hsz.trans (mem_singleton_iff.mp hzq)).trans h11.symm)
    exact hs.2.ne he

namespace PointRadialC1ArcChain
variable {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
  {γ : Icc (0 : ℝ) 1 → ℂ}

theorem toPlane_halfOpen_pairwise {s t : Icc (0 : ℝ) 1}
    {es : List (PointRadialC1ArcPiece ha y γ)} (h : PointRadialC1ArcChain ha y γ s t es)
    (hi : Function.Injective γ) :
    (es.map PointRadialC1ArcPiece.toPlane).Pairwise
      (fun e f => Disjoint (e.curve '' Ico (0 : ℝ) 1) (f.curve '' Ico (0 : ℝ) 1)) := by
  rw [List.pairwise_map]
  exact h.nodup.pairwise_of_forall_ne (fun e he f hf hef =>
    h.halfOpen_pairwise_disjoint hi he hf hef)

theorem toPlane_reverse_halfOpen_pairwise {s t : Icc (0 : ℝ) 1}
    {es : List (PointRadialC1ArcPiece ha y γ)} (h : PointRadialC1ArcChain ha y γ s t es)
    (hi : Function.Injective γ) :
    ((es.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse.Pairwise
      (fun e f => Disjoint (e.curve '' Ico (0 : ℝ) 1) (f.curve '' Ico (0 : ℝ) 1)) := by
  rw [List.pairwise_reverse, List.pairwise_map, List.pairwise_map]
  apply h.nodup.pairwise_of_forall_ne
  intro e he f hf hef
  rw [PointRadialC1PlaneArc.reverse_halfOpen_image, PointRadialC1PlaneArc.reverse_halfOpen_image]
  exact (h.reverseHalfOpen_pairwise_disjoint hi he hf hef).symm

end PointRadialC1ArcChain

/-- A simple minimizing bigon yields a literal finite cyclic family with
actual half-open joint simplicity and common chosen-chart radial germs.
The two-edge case is included: its second shared endpoint is allocated to
the opposite half-open side, not assumed absent. -/
theorem exists_pointConformal_simple_radial_C1_cyclic_chain {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p q : ℂ} (hpq : p ≠ q)
    (γ₁ γ₂ : Icc (0 : ℝ) 1 → ℂ)
    (h10 : γ₁ ⟨0, by norm_num⟩ = p) (h11 : γ₁ ⟨1, by norm_num⟩ = q)
    (h20 : γ₂ ⟨0, by norm_num⟩ = p) (h21 : γ₂ ⟨1, by norm_num⟩ = q)
    (hd₁ : ∀ s t, (pointSmoothConformalEDist a y (γ₁ s) (γ₁ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hd₂ : ∀ s t, (pointSmoothConformalEDist a y (γ₂ s) (γ₂ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hmeet : range γ₁ ∩ range γ₂ = {p, q}) :
    ∃ L : List (PointRadialC1PlaneArc ha y), PointRadialC1PlaneChain ha y p p L ∧
      2 ≤ L.length ∧ pointRadialC1PlaneCarrier L = range γ₁ ∪ range γ₂ ∧
      L.Pairwise (fun e f => Disjoint (e.curve '' Ico (0 : ℝ) 1) (f.curve '' Ico (0 : ℝ) 1)) := by
  obtain ⟨es₁, es₂, h₁, h₂, hloop, hlen, hcarrier⟩ :=
    exists_pointConformal_radial_C1_bigon_cyclic_chain ha y hpq γ₁ γ₂ h10 h11 h20 h21 hd₁ hd₂
  have hi₁ := pointConformal_geodesic_injective ha y hpq γ₁ hd₁
  have hi₂ := pointConformal_geodesic_injective ha y hpq γ₂ hd₂
  have hcross := simple_bigon_halfOpen_images_disjoint hi₁ hi₂ h11 h20 hmeet
  refine ⟨es₁.map PointRadialC1ArcPiece.toPlane ++
    ((es₂.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse,
    hloop, hlen, hcarrier, ?_⟩
  rw [List.pairwise_append]
  refine ⟨h₁.toPlane_halfOpen_pairwise hi₁, h₂.toPlane_reverse_halfOpen_pairwise hi₂, ?_⟩
  intro e he f hf
  obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
  obtain ⟨f₁, hf₁, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hf)
  obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf₁
  rw [PointRadialC1PlaneArc.reverse_halfOpen_image]
  exact hcross.mono (h₁.halfOpen_subset_total hi₁ he₀) (h₂.reverseHalfOpen_subset_total hi₂ hf₀)

end RepulsiveCoulomb
