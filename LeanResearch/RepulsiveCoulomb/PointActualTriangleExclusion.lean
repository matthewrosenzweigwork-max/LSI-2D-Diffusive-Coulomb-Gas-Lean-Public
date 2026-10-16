import LeanResearch.RepulsiveCoulomb.PointRadialGeodesicGaussBonnet
import LeanResearch.RepulsiveCoulomb.PointRadialListSlots
import LeanResearch.RepulsiveCoulomb.PointRadialTrianglePunctures
import LeanResearch.RepulsiveCoulomb.PointRadialTriangleLocalAdditivity
import LeanResearch.RepulsiveCoulomb.PointRadialTriangleLocalAdditivityReverse
import LeanResearch.RepulsiveCoulomb.PointRadialPlanePassageAngle
import LeanResearch.RepulsiveCoulomb.PointRadialPhysicalTurn
import LeanResearch.RepulsiveCoulomb.FiniteTwoCornerTurnBound

/-! Exclude a genuine simple minimizing triangle whose retained corner is
locally metric-additive. All source geometry and full oriented Gauss--Bonnet
are constructed; only the two actual outer vertices can have positive turn. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

theorem not_pointSimpleGeodesicTriangle_locally_minimizing_corner
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {q : ℂ} (T : PointSimpleGeodesicTriangle a y q) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hlocal : ∀ x ∈ range T.left.curve, ∀ z ∈ range T.right.curve,
      (pointSmoothConformalEDist a y x q).toReal ≤ r₀ →
      (pointSmoothConformalEDist a y z q).toReal ≤ r₀ →
      (pointSmoothConformalEDist a y x z).toReal =
        (pointSmoothConformalEDist a y x q).toReal + (pointSmoothConformalEDist a y q z).toReal) : False := by
  obtain ⟨esL, esC, esR, hsourceL, hsourceC, hsourceR, hchain, hlen, hcarrier, hpair, harg⟩ :=
    exists_pointSimpleGeodesicTriangle_radial_C1_argument_turn ha y T
  let L := (esL.map PointRadialC1ArcPiece.toPlane ++ esC.map PointRadialC1ArcPiece.toPlane) ++
    ((esR.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse
  have havoid := point_radial_triangle_piece_no_interior_puncture ha y T esL esC esR
  obtain ⟨n, A, hnlen, hn, hmem, hv, hclose, hinj, hAcarrier⟩ :=
    exists_point_radial_closed_list_slots L hchain
      ((by norm_num : 2 ≤ 3).trans (show 3 ≤ L.length from hlen)) hpair
  obtain ⟨B, hBcase, hBv, hBc, hBi, hBcarrier, U, V, hU, hV, hUc, hVc, hdisj, hK,
      hcover, hfrontU, hfrontV, θ, hθ, hD, hprincipal, hGB⟩ :=
    exists_point_radial_geodesic_gauss_bonnet ha y A n hn hv hclose hinj
      (fun k hk => harg _ (hmem k)) (fun k hk => havoid _ (hmem k))
  have hpq : T.left.finish ≠ T.right.finish := by
    rw [← T.cross_start, ← T.cross_finish]
    exact T.cross.distinct
  have hadditive (i k : ℕ) (hj : (B i).curve 1 = (B k).curve 0)
      (hpi : (B i).curve 1 ≠ T.left.finish) (hqi : (B i).curve 1 ≠ T.right.finish)
      (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
      (hsr : (pointSmoothConformalEDist a y ((B i).curve s) ((B i).curve 1)).toReal ≤ min r₀ 1)
      (htr : (pointSmoothConformalEDist a y ((B k).curve t) ((B i).curve 1)).toReal ≤ min r₀ 1) :
      (pointSmoothConformalEDist a y ((B i).curve s) ((B k).curve t)).toReal =
        (pointSmoothConformalEDist a y ((B i).curve s) ((B i).curve 1)).toReal +
          (pointSmoothConformalEDist a y ((B i).curve 1) ((B k).curve t)).toReal := by
    rcases hBcase with hB | hB
    · have hjA : (A i).curve 1 = (A k).curve 0 := by simpa only [hB] using hj
      have hpA : (A i).curve 1 ≠ T.left.finish := by simpa only [hB] using hpi
      have hqA : (A i).curve 1 ≠ T.right.finish := by simpa only [hB] using hqi
      have hsA : (pointSmoothConformalEDist a y ((A i).curve s) ((A i).curve 1)).toReal ≤ min r₀ 1 := by
        simpa only [hB] using hsr
      have htA : (pointSmoothConformalEDist a y ((A k).curve t) ((A i).curve 1)).toReal ≤ min r₀ 1 := by
        simpa only [hB] using htr
      simpa only [hB] using point_radial_triangle_internal_join_locally_additive ha y T hr₀ hlocal esL esC esR
        (A i) (hmem i) (A k) (hmem k) hjA hpA hqA s t hs ht hsA htA
    · have hjA : (A (n - i)).reverse.curve 1 = (A (n - k)).reverse.curve 0 := by simpa only [hB] using hj
      have hpA : (A (n - i)).reverse.curve 1 ≠ T.left.finish := by simpa only [hB] using hpi
      have hqA : (A (n - i)).reverse.curve 1 ≠ T.right.finish := by simpa only [hB] using hqi
      have hsA : (pointSmoothConformalEDist a y ((A (n - i)).reverse.curve s)
          ((A (n - i)).reverse.curve 1)).toReal ≤ min r₀ 1 := by simpa only [hB] using hsr
      have htA : (pointSmoothConformalEDist a y ((A (n - k)).reverse.curve t)
          ((A (n - i)).reverse.curve 1)).toReal ≤ min r₀ 1 := by simpa only [hB] using htr
      simpa only [hB] using point_radial_triangle_internal_reversed_join_locally_additive ha y T hr₀ hlocal esL esC esR
        (A (n - i)) (hmem _) (A (n - k)) (hmem _) hjA hpA hqA s t hs ht hsA htA
  let turn : ℕ → ℝ := fun k => Real.pi -
    (1 + coalescedPointExponent a y ((B k).curve 0) / 2) * θ k
  have hstrict (k : ℕ) (hk : k ≤ n) : turn k < Real.pi := by
    have hκ := coalescedPointExponent_nonneg a y ((B k).curve 0)
    have hpositive : 0 < (1 + coalescedPointExponent a y ((B k).curve 0) / 2) * θ k :=
      mul_pos (by positivity) (hθ k hk).1
    exact sub_lt_self _ hpositive
  have hnonpos (k : ℕ) (hk : k ≤ n) (hkp : (B k).curve 0 ≠ T.left.finish) (hkq : (B k).curve 0 ≠ T.right.finish) : turn k ≤ 0 := by
    obtain ⟨D⟩ := hD k hk
    have hj : (B (D.order n)).curve 1 = (B k).curve 0 := by
      simpa only [D.order_zero] using D.closing
    have hpi : (B (D.order n)).curve 1 ≠ T.left.finish := by rwa [hj]
    have hqi : (B (D.order n)).curve 1 ≠ T.right.finish := by rwa [hj]
    have hraw := (B (D.order n)).local_passage_sector_turns_nonpos (B k) hj
      (lt_min hr₀ zero_lt_one)
      (fun s t hs ht hsr htr => hadditive (D.order n) k hj hpi hqi s t hs ht hsr htr)
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
