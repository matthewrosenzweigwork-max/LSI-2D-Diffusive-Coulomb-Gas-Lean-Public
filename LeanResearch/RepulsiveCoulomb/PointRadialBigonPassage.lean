import LeanResearch.RepulsiveCoulomb.PointRadialBigonArgumentTurn
import LeanResearch.RepulsiveCoulomb.PointRadialC1PassageAngle

/-! Internal passage additivity on the actual source-preserving bigon list.
A join away from the two original endpoints lies on one original minimizing
side. Source injectivity then identifies its two source endpoint parameters;
no passage-angle or turn inequality is assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Every actual joined pair in the original bigon macro-list is metrically
additive at a vertex other than the two genuine bigon endpoints. -/
theorem point_radial_bigon_internal_join_additive
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {p q : ℂ} (hpq : p ≠ q) (γ₁ γ₂ : Icc (0 : ℝ) 1 → ℂ)
    (hd₁ : ∀ s t, (pointSmoothConformalEDist a y (γ₁ s) (γ₁ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hd₂ : ∀ s t, (pointSmoothConformalEDist a y (γ₂ s) (γ₂ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hmeet : range γ₁ ∩ range γ₂ = {p, q})
    (es₁ : List (PointRadialC1ArcPiece ha y γ₁))
    (es₂ : List (PointRadialC1ArcPiece ha y γ₂)) :
    let L := es₁.map PointRadialC1ArcPiece.toPlane ++
      ((es₂.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse
    ∀ e ∈ L, ∀ f ∈ L, e.curve 1 = f.curve 0 → e.curve 1 ≠ p → e.curve 1 ≠ q →
      ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      (pointSmoothConformalEDist a y (e.curve s) (f.curve t)).toReal =
        (pointSmoothConformalEDist a y (e.curve s) (e.curve 1)).toReal +
          (pointSmoothConformalEDist a y (e.curve 1) (f.curve t)).toReal := by
  have hi₁ := pointConformal_geodesic_injective ha y hpq γ₁ hd₁
  have hi₂ := pointConformal_geodesic_injective ha y hpq γ₂ hd₂
  dsimp only
  intro e he f hf hj hp hq s t hs ht
  rcases List.mem_append.mp he with he | he
  · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
      change e₀.curve 1 = f₀.curve 0 at hj
      have hsource : e₀.finish = f₀.start := hi₁ ((e₀.at_one.symm.trans hj).trans f₀.at_zero)
      simpa only [PointRadialC1ArcPiece.toPlane, e₀.at_one] using
        e₀.join_metric_additive f₀ hsource hd₁ hs ht
    · obtain ⟨f₁, hf₁, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hf)
      obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf₁
      change e₀.curve 1 = f₀.curve (1 - (0 : ℝ)) at hj
      rw [sub_zero] at hj
      have hvertex : e₀.curve 1 ∈ range γ₁ ∩ range γ₂ :=
        ⟨⟨e₀.finish, e₀.at_one.symm⟩, ⟨f₀.finish, f₀.at_one.symm.trans hj.symm⟩⟩
      rw [hmeet] at hvertex
      rcases mem_insert_iff.mp hvertex with he | he
      · exact False.elim (hp he)
      · exact False.elim (hq (mem_singleton_iff.mp he))
  · obtain ⟨e₁, he₁, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he₁
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
      change e₀.curve (1 - (1 : ℝ)) = f₀.curve 0 at hj
      rw [sub_self] at hj
      have hvertex : e₀.curve 0 ∈ range γ₁ ∩ range γ₂ :=
        ⟨⟨f₀.start, f₀.at_zero.symm.trans hj.symm⟩, ⟨e₀.start, e₀.at_zero.symm⟩⟩
      rw [hmeet] at hvertex
      rcases mem_insert_iff.mp hvertex with he | he
      · apply False.elim
        apply hp
        simpa only [PointRadialC1PlaneArc.reverse, PointRadialC1ArcPiece.toPlane, sub_self] using he
      · apply False.elim
        apply hq
        simpa only [PointRadialC1PlaneArc.reverse, PointRadialC1ArcPiece.toPlane, sub_self] using mem_singleton_iff.mp he
    · obtain ⟨f₁, hf₁, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hf)
      obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf₁
      change e₀.curve (1 - (1 : ℝ)) = f₀.curve (1 - (0 : ℝ)) at hj
      rw [sub_self, sub_zero] at hj
      have hsource : f₀.finish = e₀.start := hi₂ ((f₀.at_one.symm.trans hj.symm).trans e₀.at_zero)
      have hadd := f₀.join_metric_additive e₀ hsource hd₂
        (show 1 - t ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [ht.1, ht.2])
        (show 1 - s ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hs.1, hs.2])
      have hbase : γ₂ f₀.finish = e₀.curve 0 := (congrArg γ₂ hsource).trans e₀.at_zero.symm
      rw [hbase] at hadd
      change (pointSmoothConformalEDist a y (e₀.curve (1 - s)) (f₀.curve (1 - t))).toReal =
        (pointSmoothConformalEDist a y (e₀.curve (1 - s)) (e₀.curve (1 - (1 : ℝ)))).toReal +
          (pointSmoothConformalEDist a y (e₀.curve (1 - (1 : ℝ))) (f₀.curve (1 - t))).toReal
      rw [sub_self, pointSmoothConformalEDist_comm a y (e₀.curve (1 - s)) (f₀.curve (1 - t)), hadd,
        pointSmoothConformalEDist_comm a y (f₀.curve (1 - t)) (e₀.curve 0),
        pointSmoothConformalEDist_comm a y (e₀.curve 0) (e₀.curve (1 - s))]
      exact add_comm _ _

end RepulsiveCoulomb
