module

public import LeanResearch.RepulsiveCoulomb.MetricFlatDiskPatchExtension
public import Mathlib.Topology.Connected.Basic

@[expose] public section

/-! NEW post-loss proof bodies. The main public interface is grounded in
recovered callers; the common-chart helper spelling is new. Agreement spreads
through actual metric charts and continuity, with no continuation certificate. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem flat_isometries_eqOn_of_common_flat_chart {Y : Type*} [MetricSpace Y]
    {p : Y} (C : MetricFlatDiskChart Y p) {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ → Y}
    (hf : ∀ x ∈ U, ∀ z ∈ U, dist (f x) (f z) = dist x z)
    (hg : ∀ x ∈ U, ∀ z ∈ U, dist (g x) (g z) = dist x z)
    (hfball : ∀ x ∈ U, f x ∈ ball p C.radius)
    (hgball : ∀ x ∈ U, g x ∈ ball p C.radius)
    {V : Set ℂ} (hV : IsOpen V) (hVne : V.Nonempty) (hVU : V ⊆ U)
    (hagree : EqOn f g V) : EqOn f g U := by
  let fC : U → ℂ := fun x ↦ (C.toEuclidean ⟨f x.1, hfball x.1 x.2⟩).1
  let gC : U → ℂ := fun x ↦ (C.toEuclidean ⟨g x.1, hgball x.1 x.2⟩).1
  have hfC : Isometry fC := by
    apply Isometry.of_dist_eq
    intro x z
    change dist (C.toEuclidean ⟨f x.1, hfball x.1 x.2⟩)
      (C.toEuclidean ⟨f z.1, hfball z.1 z.2⟩) = dist x z
    rw [C.toEuclidean.dist_eq]
    exact hf x.1 x.2 z.1 z.2
  have hgC : Isometry gC := by
    apply Isometry.of_dist_eq
    intro x z
    change dist (C.toEuclidean ⟨g x.1, hgball x.1 x.2⟩)
      (C.toEuclidean ⟨g z.1, hgball z.1 z.2⟩) = dist x z
    rw [C.toEuclidean.dist_eq]
    exact hg x.1 x.2 z.1 z.2
  have hUne : (interior U).Nonempty := by
    rw [hU.interior_eq]
    exact hVne.mono hVU
  obtain ⟨ef, hef⟩ := exists_complex_isometry_extension_of_open_overlap fC hfC hUne
  obtain ⟨eg, heg⟩ := exists_complex_isometry_extension_of_open_overlap gC hgC hUne
  have heV : EqOn ef eg V := by
    intro x hx
    calc
      ef x = fC ⟨x, hVU hx⟩ := hef ⟨x, hVU hx⟩
      _ = gC ⟨x, hVU hx⟩ := by
        change (C.toEuclidean ⟨f x, hfball x (hVU hx)⟩).1 =
          (C.toEuclidean ⟨g x, hgball x (hVU hx)⟩).1
        exact congrArg (fun y : ball p C.radius ↦ (C.toEuclidean y).1)
          (Subtype.ext (hagree hx))
      _ = eg x := (heg ⟨x, hVU hx⟩).symm
  have heq : ef = eg := complex_isometry_eq_of_agree_on_nonempty_open hV hVne heV
  intro x hx
  have hcoord : fC ⟨x, hx⟩ = gC ⟨x, hx⟩ :=
    (hef ⟨x, hx⟩).symm.trans
      ((congrArg (fun e : ℂ ≃ᵢ ℂ ↦ e x) heq).trans (heg ⟨x, hx⟩))
  have hchart : C.toEuclidean ⟨f x, hfball x hx⟩ = C.toEuclidean ⟨g x, hgball x hx⟩ :=
    Subtype.ext hcoord
  exact congrArg Subtype.val (C.toEuclidean.injective hchart)

theorem flat_isometries_eqOn_of_open_germ {Y : Type*} [MetricSpace Y]
    {K : Set ℂ} (hK : IsOpen K) (hconn : IsPreconnected K)
    {f g : ℂ → Y}
    (hf : ∀ x ∈ K, ∀ z ∈ K, dist (f x) (f z) = dist x z)
    (hg : ∀ x ∈ K, ∀ z ∈ K, dist (g x) (g z) = dist x z)
    (hcharts : ∀ x ∈ K, ∃ p : Y, ∃ C : MetricFlatDiskChart Y p,
      f x ∈ ball p C.radius)
    {V : Set ℂ} (hV : IsOpen V) (hVne : V.Nonempty) (hVK : V ⊆ K)
    (hagree : EqOn f g V) : EqOn f g K := by
  let E : Set ℂ := interior {x | x ∈ K ∧ f x = g x}
  have hEopen : IsOpen E := isOpen_interior
  have hEK : E ⊆ K := by
    intro x hx
    have hx' : x ∈ K ∧ f x = g x := interior_subset (s := {z : ℂ | z ∈ K ∧ f z = g z}) hx
    exact hx'.1
  have heqE : EqOn f g E := by
    intro x hx
    have hx' : x ∈ K ∧ f x = g x := interior_subset (s := {z : ℂ | z ∈ K ∧ f z = g z}) hx
    exact hx'.2
  have hVE : V ⊆ E := by
    have hsub : V ⊆ {x | x ∈ K ∧ f x = g x} := fun x hx ↦ ⟨hVK hx, hagree hx⟩
    intro x hx
    exact interior_mono hsub (by simpa only [hV.interior_eq] using hx)
  have hfl : LipschitzOnWith 1 f K := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx z hz
    simpa only [NNReal.coe_one, one_mul, hf x hx z hz] using (le_refl (dist x z))
  have hgl : LipschitzOnWith 1 g K := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx z hz
    simpa only [NNReal.coe_one, one_mul, hg x hx z hz] using (le_refl (dist x z))
  have heqLimit : EqOn f g (closure E ∩ K) :=
    heqE.of_subset_closure (hfl.continuousOn.mono inter_subset_right)
      (hgl.continuousOn.mono inter_subset_right)
      (fun x hx ↦ ⟨subset_closure hx, hEK hx⟩) inter_subset_left
  have hlimit : closure E ∩ K ⊆ E := by
    intro x hx
    have hxeq : f x = g x := heqLimit hx
    obtain ⟨p, C, hfx⟩ := hcharts x hx.2
    obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.mp (hK.mem_nhds hx.2)
    let ε : ℝ := min r (C.radius - dist (f x) p)
    have hgap : 0 < C.radius - dist (f x) p := sub_pos.mpr hfx
    have hε : 0 < ε := lt_min hr hgap
    have hεgap : ε ≤ C.radius - dist (f x) p := min_le_right _ _
    have hUK : ball x ε ⊆ K := by
      intro z hz
      have hz' : dist z x < ε := hz
      exact hrK (hz'.trans_le (min_le_left _ _))
    have hfball : ∀ z ∈ ball x ε, f z ∈ ball p C.radius := by
      intro z hz
      have hz' : dist z x < ε := hz
      have ht := dist_triangle (f z) (f x) p
      rw [hf z (hUK hz) x hx.2] at ht
      change dist (f z) p < C.radius
      linarith
    have hgball : ∀ z ∈ ball x ε, g z ∈ ball p C.radius := by
      intro z hz
      have hz' : dist z x < ε := hz
      have ht := dist_triangle (g z) (g x) p
      rw [hg z (hUK hz) x hx.2, ← hxeq] at ht
      change dist (g z) p < C.radius
      linarith
    obtain ⟨y, hyE, hxy⟩ := Metric.mem_closure_iff.mp hx.1 ε hε
    have hyU : y ∈ ball x ε := by simpa only [mem_ball, dist_comm] using hxy
    have hWne : (E ∩ ball x ε).Nonempty := ⟨y, hyE, hyU⟩
    have heqU : EqOn f g (ball x ε) :=
      flat_isometries_eqOn_of_common_flat_chart C isOpen_ball
        (fun z hz w hw ↦ hf z (hUK hz) w (hUK hw))
        (fun z hz w hw ↦ hg z (hUK hz) w (hUK hw)) hfball hgball
        (hEopen.inter isOpen_ball) hWne inter_subset_right (fun z hz ↦ heqE hz.1)
    have hsub : ball x ε ⊆ {z | z ∈ K ∧ f z = g z} := fun z hz ↦ ⟨hUK hz, heqU hz⟩
    apply interior_mono hsub
    rw [isOpen_ball.interior_eq]
    exact mem_ball_self hε
  have hKEnonempty : (K ∩ E).Nonempty := by
    obtain ⟨x, hx⟩ := hVne
    exact ⟨x, hVK hx, hVE hx⟩
  have hKE : K ⊆ E := hconn.subset_of_closure_inter_subset hEopen hKEnonempty hlimit
  intro x hx
  exact heqE (hKE hx)

end RepulsiveCoulomb
