module

public import LeanResearch.RepulsiveCoulomb.PoleBranchParametricCircle

@[expose] public section

/-! A proved Hartogs-cylinder continuation principle. Its hypotheses refer only
to an open holomorphic domain, a fixed admissible contour, and a dense family
of nonsingular disk fibers. It does not assume an extension exists. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

def poleBranchCauchyAt {E : Type*} (f : E × ℂ → ℂ) (c : ℂ) (r : ℝ) (p : E × ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ∮ z in C(c, r), (z - p.2)⁻¹ • f (p.1, z)

theorem poleBranch_cauchyAt_differentiableOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} {V : Set (E × ℂ)} (hV : IsOpen V)
    (hf : DifferentiableOn ℂ f V) {U : Set E} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hc : ∀ p ∈ U, ∀ z ∈ sphere c r, (p, z) ∈ V) :
    DifferentiableOn ℂ (poleBranchCauchyAt f c r) (U ×ˢ ball c r) := by
  let S : Set ((E × ℂ) × ℂ) :=
    (fun q => (q.1.1, q.2)) ⁻¹' V ∩ {q | q.2 - q.1.2 ≠ 0}
  have hS : IsOpen S := (hV.preimage (by fun_prop)).inter
    (isOpen_ne.preimage (by fun_prop))
  let g : (E × ℂ) × ℂ → ℂ := fun q => (q.2 - q.1.2)⁻¹ • f (q.1.1, q.2)
  have hg : DifferentiableOn ℂ g S := by
    dsimp only [g]
    simp only [smul_eq_mul]
    apply DifferentiableOn.mul
    · exact (differentiableOn_snd.sub differentiableOn_fst.snd).inv (fun q hq => hq.2)
    · exact hf.comp (differentiableOn_fst.fst.prodMk differentiableOn_snd) (fun _ hq => hq.1)
  intro p hp
  have hc' : ∀ z ∈ sphere c |r|, (p, z) ∈ S := by
    intro z hz
    have hzr : z ∈ sphere c r := by simpa only [abs_of_pos hr] using hz
    refine ⟨hc p.1 hp.1 z hzr, sub_ne_zero.mpr ?_⟩
    intro heq
    have hdist := mem_sphere.mp hzr
    have hp2 := mem_ball.mp hp.2
    rw [← heq, hdist] at hp2
    exact lt_irrefl r hp2
  exact ((poleBranch_differentiableAt_circleIntegral hS hg hc').const_smul
    (2 * Real.pi * Complex.I : ℂ)⁻¹).differentiableWithinAt

theorem poleBranch_cauchyAt_eq_of_disk
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E × ℂ → ℂ} {V : Set (E × ℂ)}
    (hf : DifferentiableOn ℂ f V) {p : E} {c w : ℂ} {r : ℝ}
    (hdisc : ∀ z ∈ closedBall c r, (p, z) ∈ V) (hw : w ∈ ball c r) :
    poleBranchCauchyAt f c r (p, w) = f (p, w) := by
  have hd : DifferentiableOn ℂ (fun z => f (p, z)) (closedBall c r) :=
    hf.comp ((differentiableOn_const p).prodMk differentiableOn_id) hdisc
  rw [poleBranchCauchyAt, hd.circleIntegral_sub_inv_smul hw, inv_smul_smul₀]
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

theorem poleBranch_hartogs_cylinder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E × ℂ → ℂ} {V : Set (E × ℂ)} (hV : IsOpen V)
    (hf : DifferentiableOn ℂ f V) {U D : Set E} (hU : IsOpen U) (hD : Dense D)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ∀ p ∈ U, ∀ z ∈ sphere c r, (p, z) ∈ V)
    (hdisc : ∀ p ∈ U ∩ D, ∀ z ∈ closedBall c r, (p, z) ∈ V) :
    DifferentiableOn ℂ (poleBranchCauchyAt f c r) (U ×ˢ ball c r) ∧
      EqOn (poleBranchCauchyAt f c r) f ((U ×ˢ ball c r) ∩ V) := by
  have hF := poleBranch_cauchyAt_differentiableOn hV hf hr hc
  refine ⟨hF, ?_⟩
  rintro ⟨p, w⟩ ⟨⟨hp, hw⟩, hpw⟩
  let W : Set E := U ∩ (fun q => (q, w)) ⁻¹' V
  have hW : IsOpen W := hU.inter (hV.preimage (by fun_prop))
  have hpW : p ∈ W := ⟨hp, hpw⟩
  have hFc : ContinuousOn (fun q => poleBranchCauchyAt f c r (q, w)) W :=
    hF.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun q hq => ⟨hq.1, hw⟩)
  have hfc : ContinuousOn (fun q => f (q, w)) W :=
    hf.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun q hq => hq.2)
  have heq : EqOn (fun q => poleBranchCauchyAt f c r (q, w)) (fun q => f (q, w)) (W ∩ D) := by
    intro q hq
    exact poleBranch_cauchyAt_eq_of_disk hf (hdisc q ⟨hq.1.1, hq.2⟩) hw
  exact heq.of_subset_closure hFc hfc inter_subset_left (hD.open_subset_closure_inter hW) hpW

end RepulsiveCoulomb
