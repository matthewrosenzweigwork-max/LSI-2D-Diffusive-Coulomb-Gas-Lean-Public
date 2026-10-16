module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Geometry produced by an actual weakly quasisymmetric map

The input is the literal three-point distance inequality for a map. From it
we prove the factor-two comparison with constant `H * (1 + H)`, quantitative
image-ball inclusions, and a diameter buffer inside the image of the exact
source dilate `B(c, 2*r)`. Homeomorphism assumptions provide actual inverse
points, open images, compactness and connectedness; none of these conclusions
is an input certificate.

This module does not prove analytic quasiconformality implies weak
quasisymmetry, the area formula, the David--Semmes oscillation inequality, or
the main manuscript endpoint. Its source imports only Mathlib.
-/

noncomputable section
open Set Metric

namespace RepulsiveCoulomb.PaperRoute

section Metric
variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- Weak quasisymmetry is exactly three-point distance control, with `H ≥ 1`.
It carries no ball, diameter, measure, or downstream analytic conclusions. -/
structure WeakQuasisymmetricWith (F : X → Y) (H : ℝ) : Prop where
  one_le : 1 ≤ H
  control : ∀ a b c : X, dist a b ≤ dist a c →
    dist (F a) (F b) ≤ H * dist (F a) (F c)

/-- The elementary factor-two constant. -/
def weakQSTwoScale (H : ℝ) : ℝ := H * (1 + H)

variable {F : X → Y} {H : ℝ}

theorem WeakQuasisymmetricWith.constant_pos (hF : WeakQuasisymmetricWith F H) :
    0 < H := lt_of_lt_of_le zero_lt_one hF.one_le

theorem WeakQuasisymmetricWith.twoScale_pos (hF : WeakQuasisymmetricWith F H) :
    0 < weakQSTwoScale H :=
  mul_pos hF.constant_pos (by linarith [hF.one_le])

/-- The outer image bound is closed: weak quasisymmetry need not give a strict
inequality at the target radius. This stronger version includes source boundary. -/
theorem WeakQuasisymmetricWith.image_closedBall_subset (hF : WeakQuasisymmetricWith F H)
    {c y : X} {r : ℝ} (hy : dist c y = r) :
    F '' closedBall c r ⊆ closedBall (F c) (H * dist (F c) (F y)) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_closedBall] at hx ⊢
  rw [dist_comm] at hx ⊢
  exact hF.control c x y (by simpa only [hy] using hx)

/-- Actual surjectivity supplies the preimage of every target point in the
inner ball. No assertion about a mapped boundary is used. -/
theorem WeakQuasisymmetricWith.ball_subset_image (hF : WeakQuasisymmetricWith F H)
    (hsurj : Function.Surjective F) {c y : X} {r : ℝ} (hy : dist c y = r) :
    ball (F c) (dist (F c) (F y) / H) ⊆ F '' ball c r := by
  intro v hv
  obtain ⟨x, rfl⟩ := hsurj v
  refine ⟨x, ?_, rfl⟩
  by_contra hx
  have hx' : dist c y ≤ dist c x := by
    rw [hy, dist_comm]
    exact le_of_not_gt hx
  have hcontrol := hF.control c y x hx'
  have hv' : dist (F c) (F x) < dist (F c) (F y) / H := by
    simpa only [mem_ball, dist_comm] using hv
  have : H * dist (F c) (F x) < dist (F c) (F y) := by
    have := (lt_div_iff₀ hF.constant_pos).1 hv'
    simpa only [mul_comm] using this
  exact (not_lt_of_ge hcontrol) this

/-- Both image-ball inclusions for the same map and the same boundary point. -/
theorem WeakQuasisymmetricWith.image_ball_inclusions
    (hF : WeakQuasisymmetricWith F H) (hsurj : Function.Surjective F)
    {c y : X} {r : ℝ} (hy : dist c y = r) :
    ball (F c) (dist (F c) (F y) / H) ⊆ F '' ball c r ∧
    F '' ball c r ⊆ closedBall (F c) (H * dist (F c) (F y)) :=
  ⟨hF.ball_subset_image hsurj hy,
    (image_mono ball_subset_closedBall).trans (hF.image_closedBall_subset hy)⟩

end Metric

section Normed
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace Y] {F : E → Y} {H : ℝ}

/-- A real midpoint gives factor-two control directly from weak quasisymmetry. -/
theorem WeakQuasisymmetricWith.factor_two (hF : WeakQuasisymmetricWith F H)
    {z x p : E} (hxp : dist z x ≤ 2 * dist z p) :
    dist (F z) (F x) ≤ weakQSTwoScale H * dist (F z) (F p) := by
  let m := midpoint ℝ z x
  have hzm : dist z m = dist z x / 2 := by
    simp [m, dist_left_midpoint, div_eq_mul_inv, mul_comm]
  have hmz : dist m z = dist z x / 2 := by rwa [dist_comm]
  have hmx : dist m x = dist z x / 2 := by
    simp [m, dist_midpoint_right, div_eq_mul_inv, mul_comm]
  have h₁ := hF.control z m p (by rw [hzm]; linarith)
  have h₂ := hF.control m x z (by rw [hmx, hmz])
  rw [dist_comm (F m) (F z)] at h₂
  calc
    dist (F z) (F x) ≤ dist (F z) (F m) + dist (F m) (F x) := dist_triangle _ _ _
    _ ≤ H * dist (F z) (F p) + H * (H * dist (F z) (F p)) :=
      add_le_add h₁ (h₂.trans (mul_le_mul_of_nonneg_left h₁ hF.constant_pos.le))
    _ = weakQSTwoScale H * dist (F z) (F p) := by unfold weakQSTwoScale; ring

omit [NormedSpace ℝ E] in
/-- Source geometry behind the exact-dilate buffer: from any point of the
closed ball, every other point is at most twice as far as an exterior point. -/
theorem closedBall_dist_le_two_mul_dist {c z x p : E} {r : ℝ}
    (hz : z ∈ closedBall c r) (hx : x ∈ closedBall c r)
    (hp : p ∉ ball c (2 * r)) : dist z x ≤ 2 * dist z p := by
  have hz' : dist z c ≤ r := hz
  have hx' : dist c x ≤ r := by simpa only [mem_closedBall, dist_comm] using hx
  have hp' : 2 * r ≤ dist p c := le_of_not_gt hp
  have hzx := dist_triangle z c x
  have hpc := dist_triangle p z c
  rw [dist_comm p z] at hpc
  linarith

/-- The diameter is bounded by every distance from the image of the closed
ball to the complement of the image of the exact double ball. -/
theorem WeakQuasisymmetricWith.image_diam_le_separation
    (hF : WeakQuasisymmetricWith F H) (hsurj : Function.Surjective F)
    {c : E} {r : ℝ} {u v : Y} (hu : u ∈ F '' closedBall c r)
    (hv : v ∉ F '' ball c (2 * r)) :
    diam (F '' closedBall c r) ≤ 2 * weakQSTwoScale H * dist u v := by
  obtain ⟨z, hz, rfl⟩ := hu
  obtain ⟨p, rfl⟩ := hsurj v
  have hp : p ∉ ball c (2 * r) := fun hp => hv ⟨p, hp, rfl⟩
  apply diam_le_of_forall_dist_le (mul_nonneg
    (mul_nonneg zero_le_two hF.twoScale_pos.le) dist_nonneg)
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have h₁ := hF.factor_two (closedBall_dist_le_two_mul_dist hz hx hp)
  have h₂ := hF.factor_two (closedBall_dist_le_two_mul_dist hz hy hp)
  calc
    dist (F x) (F y) ≤ dist (F x) (F z) + dist (F z) (F y) := dist_triangle _ _ _
    _ ≤ weakQSTwoScale H * dist (F z) (F p) +
        weakQSTwoScale H * dist (F z) (F p) := by
      rw [dist_comm (F x) (F z)]
      exact add_le_add h₁ h₂
    _ = 2 * weakQSTwoScale H * dist (F z) (F p) := by ring

/-- The open target ball at the full quantitative buffer radius lies inside
`F(B(c,2*r))`. There is no unspecified enlargement of the source ball. -/
theorem WeakQuasisymmetricWith.ball_subset_image_doubleBall
    (hF : WeakQuasisymmetricWith F H) (hsurj : Function.Surjective F)
    {c : E} {r : ℝ} {u : Y} (hu : u ∈ F '' closedBall c r) :
    ball u (diam (F '' closedBall c r) / (2 * weakQSTwoScale H)) ⊆
      F '' ball c (2 * r) := by
  intro v hv
  by_contra hnot
  have hsep := hF.image_diam_le_separation hsurj hu hnot
  have hv' : dist u v < diam (F '' closedBall c r) / (2 * weakQSTwoScale H) := by
    simpa only [mem_ball, dist_comm] using hv
  have hpos : 0 < 2 * weakQSTwoScale H := mul_pos zero_lt_two hF.twoScale_pos
  have := (lt_div_iff₀ hpos).1 hv'
  nlinarith

/-- A closed target ball of any strictly smaller radius is also contained in
the same exact source dilate's image. -/
theorem WeakQuasisymmetricWith.closedBall_subset_image_doubleBall
    (hF : WeakQuasisymmetricWith F H) (hsurj : Function.Surjective F)
    {c : E} {r s : ℝ} {u : Y} (hu : u ∈ F '' closedBall c r)
    (hs : s < diam (F '' closedBall c r) / (2 * weakQSTwoScale H)) :
    closedBall u s ⊆ F '' ball c (2 * r) :=
  (closedBall_subset_ball hs).trans (hF.ball_subset_image_doubleBall hsurj hu)

end Normed

section Homeomorph
variable {E Y : Type*} [NormedAddCommGroup E] [MetricSpace Y]

/-- A homeomorphism maps the actual source ball to an open set. -/
theorem image_ball_isOpen (F : E ≃ₜ Y) (c : E) (r : ℝ) :
    IsOpen (F '' ball c r) := F.isOpenMap _ isOpen_ball

/-- A continuous map sends the connected source closed ball to a connected set. -/
theorem image_closedBall_isConnected [NormedSpace ℝ E] (F : E ≃ₜ Y) (c : E) {r : ℝ} (hr : 0 ≤ r) :
    IsConnected (F '' closedBall c r) :=
  ((convex_closedBall c r).isConnected (nonempty_closedBall.2 hr)).image F
    F.continuous.continuousOn

/-- Positive radius places the closed source ball in the exact open double ball. -/
theorem image_closedBall_subset_image_doubleBall (F : E ≃ₜ Y) (c : E) {r : ℝ}
    (hr : 0 < r) : F '' closedBall c r ⊆ F '' ball c (2 * r) :=
  image_mono (closedBall_subset_ball (by linarith))

/-- Properness makes the source closed ball compact; the image is literally its
continuous image under the supplied homeomorphism. -/
theorem image_closedBall_isCompact [ProperSpace E] (F : E ≃ₜ Y) (c : E) (r : ℝ) :
    IsCompact (F '' closedBall c r) := (isCompact_closedBall c r).image F.continuous

/-- The real diameter is positive for positive radius in a nontrivial proper
normed space. Compactness also proves the extended diameter is finite. -/
theorem image_closedBall_diam_pos [NormedSpace ℝ E] [ProperSpace E] [Nontrivial E]
    (F : E ≃ₜ Y) (c : E) {r : ℝ} (hr : 0 < r) :
    0 < diam (F '' closedBall c r) := by
  obtain ⟨y, hy⟩ := (NormedSpace.sphere_nonempty (x := c)).2 hr.le
  have hcy : c ≠ y := by
    intro h
    subst y
    have : r = 0 := by simpa using hy.symm
    linarith
  have hnontrivial : (closedBall c r).Nontrivial :=
    ⟨c, mem_closedBall_self hr.le, y, sphere_subset_closedBall hy, hcy⟩
  exact diam_pos (hnontrivial.image F.injective) (image_closedBall_isCompact F c r).isBounded

/-- Finite extended diameter records genuine boundedness, so subsequent uses
of the real diameter cannot rely on its default value for unbounded sets. -/
theorem image_closedBall_ediam_ne_top [ProperSpace E]
    (F : E ≃ₜ Y) (c : E) (r : ℝ) : ediam (F '' closedBall c r) ≠ ⊤ :=
  (image_closedBall_isCompact F c r).isBounded.ediam_ne_top

end Homeomorph
end RepulsiveCoulomb.PaperRoute
