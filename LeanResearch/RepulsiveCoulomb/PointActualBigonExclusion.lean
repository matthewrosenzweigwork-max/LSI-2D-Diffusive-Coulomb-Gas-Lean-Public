import LeanResearch.RepulsiveCoulomb.PointRadialGeodesicGaussBonnet
import LeanResearch.RepulsiveCoulomb.PointRadialListSlots
import LeanResearch.RepulsiveCoulomb.PointRadialBigonPassageReverse
import LeanResearch.RepulsiveCoulomb.PointRadialPlanePassageAngle
import LeanResearch.RepulsiveCoulomb.PointRadialPhysicalTurn
import LeanResearch.RepulsiveCoulomb.FiniteTwoCornerTurnBound

/-! Exclude a genuine simple minimizing bigon for the literal point metric.
Original source macro-arcs, Jordan regions, positive traversal, point/tangent
lifts, full corner sectors and Gauss--Bonnet are all constructed. The only
possible positive turns are at the two original endpoints, and each is
strictly below pi. No global uniqueness or turning certificate is assumed. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

theorem not_pointConformal_simple_geodesic_bigon
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {p q : ℂ} (hpq : p ≠ q) (γ₁ γ₂ : Icc (0 : ℝ) 1 → ℂ)
    (h10 : γ₁ ⟨0, by norm_num⟩ = p) (h11 : γ₁ ⟨1, by norm_num⟩ = q)
    (h20 : γ₂ ⟨0, by norm_num⟩ = p) (h21 : γ₂ ⟨1, by norm_num⟩ = q)
    (hd₁ : ∀ s t, (pointSmoothConformalEDist a y (γ₁ s) (γ₁ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hd₂ : ∀ s t, (pointSmoothConformalEDist a y (γ₂ s) (γ₂ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hmeet : range γ₁ ∩ range γ₂ = {p, q}) : False := by
  obtain ⟨es₁, es₂, hsource₁, hsource₂, hchain, hlen, hcarrier, hpair, harg⟩ :=
    exists_pointConformal_simple_radial_C1_bigon_argument_turn ha y hpq γ₁ γ₂
      h10 h11 h20 h21 hd₁ hd₂ hmeet
  let L := es₁.map PointRadialC1ArcPiece.toPlane ++
    ((es₂.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse
  have havoid := point_radial_bigon_piece_no_interior_puncture ha y hpq γ₁ γ₂ hd₁ hd₂ es₁ es₂
  obtain ⟨n, A, hnlen, hn, hmem, hv, hclose, hinj, hAcarrier⟩ :=
    exists_point_radial_closed_list_slots L hchain hlen hpair
  obtain ⟨B, hBcase, hBv, hBc, hBi, hBcarrier, U, V, hU, hV, hUc, hVc, hdisj, hK,
      hcover, hfrontU, hfrontV, θ, hθ, hD, hprincipal, hGB⟩ :=
    exists_point_radial_geodesic_gauss_bonnet ha y A n hn hv hclose hinj
      (fun k hk => harg _ (hmem k)) (fun k hk => havoid _ (hmem k))
  have hadditive (i k : ℕ) (hj : (B i).curve 1 = (B k).curve 0)
      (hpi : (B i).curve 1 ≠ p) (hqi : (B i).curve 1 ≠ q)
      (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
      (pointSmoothConformalEDist a y ((B i).curve s) ((B k).curve t)).toReal =
        (pointSmoothConformalEDist a y ((B i).curve s) ((B i).curve 1)).toReal +
          (pointSmoothConformalEDist a y ((B i).curve 1) ((B k).curve t)).toReal := by
    rcases hBcase with hB | hB
    · have hjA : (A i).curve 1 = (A k).curve 0 := by simpa only [hB] using hj
      have hpA : (A i).curve 1 ≠ p := by simpa only [hB] using hpi
      have hqA : (A i).curve 1 ≠ q := by simpa only [hB] using hqi
      simpa only [hB] using point_radial_bigon_internal_join_additive ha y hpq γ₁ γ₂
        hd₁ hd₂ hmeet es₁ es₂ (A i) (hmem i) (A k) (hmem k) hjA hpA hqA s t hs ht
    · have hjA : (A (n - i)).reverse.curve 1 = (A (n - k)).reverse.curve 0 := by
        simpa only [hB] using hj
      have hpA : (A (n - i)).reverse.curve 1 ≠ p := by simpa only [hB] using hpi
      have hqA : (A (n - i)).reverse.curve 1 ≠ q := by simpa only [hB] using hqi
      simpa only [hB] using point_radial_bigon_internal_reversed_join_additive ha y hpq γ₁ γ₂
        hd₁ hd₂ hmeet es₁ es₂ (A (n - i)) (hmem _) (A (n - k)) (hmem _) hjA hpA hqA s t hs ht
  let turn : ℕ → ℝ := fun k => Real.pi -
    (1 + coalescedPointExponent a y ((B k).curve 0) / 2) * θ k
  have hstrict (k : ℕ) (hk : k ≤ n) : turn k < Real.pi := by
    have hκ := coalescedPointExponent_nonneg a y ((B k).curve 0)
    have hpositive : 0 < (1 + coalescedPointExponent a y ((B k).curve 0) / 2) * θ k :=
      mul_pos (by positivity) (hθ k hk).1
    exact sub_lt_self _ hpositive
  have hnonpos (k : ℕ) (hk : k ≤ n) (hkp : (B k).curve 0 ≠ p) (hkq : (B k).curve 0 ≠ q) : turn k ≤ 0 := by
    obtain ⟨D⟩ := hD k hk
    have hj : (B (D.order n)).curve 1 = (B k).curve 0 := by
      simpa only [D.order_zero] using D.closing
    have hpi : (B (D.order n)).curve 1 ≠ p := by rwa [hj]
    have hqi : (B (D.order n)).curve 1 ≠ q := by rwa [hj]
    have hraw := (B (D.order n)).local_passage_sector_turns_nonpos (B k) hj (by norm_num : (0 : ℝ) < 1)
      (fun s t hs ht _ _ => hadditive (D.order n) k hj hpi hqi s t hs ht)
    rw [hj] at hraw
    have hphysical := (B (D.order n)).physical_sector_turns_nonpos (B k) hj
      (coalescedPointExponent a y ((B k).curve 0) / 2) hraw.1 hraw.2
    have hdir := D.directed_turn_nonpos (fun i _ => (B i).smooth)
      (fun i _ => (B i).regular) hphysical.1 hphysical.2
    simpa only [turn, add_comm] using hdir
  have hinjvertex : Set.InjOn (fun k => (B k).curve 0) (Finset.range (n + 1) : Set ℕ) := by
    intro i hi j hj he
    exact (hBi i j (by have := Finset.mem_range.mp hi; omega)
      (by have := Finset.mem_range.mp hj; omega) 0 0 (by norm_num) (by norm_num) he).1
  have hless := finite_sum_lt_two_pi_of_two_exceptional_vertices (Finset.range (n + 1))
    (fun k => (B k).curve 0) turn hinjvertex hpq
    (fun k hk => hstrict k (by have := Finset.mem_range.mp hk; omega))
    (fun k hk => hnonpos k (by have := Finset.mem_range.mp hk; omega))
  have hmass : 0 ≤ ∑ j, if y j ∈ U then a j / 2 else 0 := by
    apply Finset.sum_nonneg
    intro j hj
    split_ifs
    · exact div_nonneg (ha j) (by norm_num)
    · exact le_rfl
  change (∑ k ∈ Finset.range (n + 1), turn k) =
    2 * Real.pi + 2 * Real.pi * (∑ j, if y j ∈ U then a j / 2 else 0) at hGB
  have hbudget : 2 * Real.pi ≤ ∑ k ∈ Finset.range (n + 1), turn k := by
    rw [hGB]
    have := mul_nonneg (show 0 ≤ 2 * Real.pi by positivity) hmass
    linarith
  exact (not_lt_of_ge hbudget) hless

end RepulsiveCoulomb
