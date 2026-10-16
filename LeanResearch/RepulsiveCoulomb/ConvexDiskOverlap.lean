module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Affine.AddTorsor

@[expose] public section

/-! NEW implementation after workspace loss. The two public geometric
statements are retained; these proof bodies are not a recovery of old bytes. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem convex_interior_inter_ball_nonempty {K : Set ℂ}
    (hK : Convex ℝ K) (hne : (interior K).Nonempty) {x : ℂ} (hx : x ∈ K)
    {r : ℝ} (hr : 0 < r) : (interior K ∩ ball x r).Nonempty := by
  have hxc : x ∈ closure (interior K) := by
    rw [hK.closure_interior_eq_closure_of_nonempty_interior hne]
    exact subset_closure hx
  obtain ⟨z, hz, hzx⟩ := Metric.mem_closure_iff.mp hxc r hr
  exact ⟨z, hz, by simpa only [mem_ball, dist_comm] using hzx⟩

theorem convex_centered_balls_old_interior_overlap {K : Set ℂ}
    (hK : Convex ℝ K) (hne : (interior K).Nonempty)
    {x z : ℂ} (hx : x ∈ K) (hz : z ∈ K) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hinter : (ball x r ∩ ball z s).Nonempty) :
    (interior K ∩ (ball x r ∩ ball z s)).Nonempty := by
  obtain ⟨w, hwx, hwz⟩ := hinter
  have hxw : dist x w < r := by simpa only [mem_ball, dist_comm] using hwx
  have hwz' : dist w z < s := hwz
  have hdist : dist x z < r + s :=
    (dist_triangle x w z).trans_lt (add_lt_add hxw hwz')
  have hrs : 0 < r + s := add_pos hr hs
  let t : ℝ := r / (r + s)
  have ht0 : 0 < t := div_pos hr hrs
  have ht1 : t < 1 := (div_lt_one hrs).mpr (by linarith)
  have htmul : t * (r + s) = r := div_mul_cancel₀ _ hrs.ne'
  have homul : (1 - t) * (r + s) = s := by nlinarith [htmul]
  let q : ℂ := AffineMap.lineMap x z t
  have hqK : q ∈ K := hK.segment_subset hx hz (lineMap_mem_segment ℝ x z ⟨ht0.le, ht1.le⟩)
  have hqx : dist q x < r := by
    calc
      dist q x = t * dist x z := by
        dsimp only [q]
        rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_pos ht0]
      _ < t * (r + s) := mul_lt_mul_of_pos_left hdist ht0
      _ = r := htmul
  have hqz : dist q z < s := by
    calc
      dist q z = (1 - t) * dist x z := by
        dsimp only [q]
        rw [dist_lineMap_right, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht1)]
      _ < (1 - t) * (r + s) := mul_lt_mul_of_pos_left hdist (sub_pos.mpr ht1)
      _ = s := homul
  obtain ⟨ε, hε, hεB⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_ball.inter isOpen_ball).mem_nhds (show q ∈ ball x r ∩ ball z s from ⟨hqx, hqz⟩))
  obtain ⟨v, hvK, hvq⟩ := convex_interior_inter_ball_nonempty hK hne hqK hε
  exact ⟨v, hvK, hεB hvq⟩

end RepulsiveCoulomb
