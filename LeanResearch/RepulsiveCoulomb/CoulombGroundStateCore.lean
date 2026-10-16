import LeanResearch.RepulsiveCoulomb.CoulombDensitySmooth
import LeanResearch.RepulsiveCoulomb.CoulombPotentialWeight
import LeanResearch.RepulsiveCoulomb.CoulombCutoffCore

/-! The literal normalized ground-state transform on the original
collision-avoiding core, in the full physical configuration space. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombGroundState_contDiff {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => φ z * Real.sqrt (coulombDensity N β z)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ coulombDomain N
  · have hd : ContDiffAt ℝ (⊤ : ℕ∞) (coulombDensity N β) z :=
      (coulombDensity_contDiffAt β hz).of_le (by simp)
    exact φ.contDiff.contDiffAt.mul
      (hd.sqrt (ne_of_gt (coulombDensity_pos_off_collisions hβ hz)))
  · have hn : z ∉ tsupport (φ : CoulombConfig N → ℝ) := fun ht => hz (φ.tsupport_subset ht)
    have he := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun _ : CoulombConfig N => (0 : ℝ)) z).congr_of_eventuallyEq
    filter_upwards [he] with x hx
    simp [hx]

def coulombGroundStateCore {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) : TestFunction (coulombDomain N) ℝ ⊤ :=
  ⟨fun z => φ z * Real.sqrt (coulombDensity N β z),
    coulombGroundState_contDiff hβ φ, φ.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans φ.tsupport_subset⟩

theorem coulombGroundStateCore_apply {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (z : CoulombConfig N) :
    coulombGroundStateCore hβ φ z = φ z * Real.sqrt (coulombDensity N β z) := rfl

theorem coulombGroundStateCore_sq {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (z : CoulombConfig N) :
    (coulombGroundStateCore hβ φ z) ^ 2 = coulombDensity N β z * φ z ^ 2 := by
  rw [coulombGroundStateCore_apply, mul_pow, Real.sq_sqrt (coulombDensity_nonneg β z), mul_comm]

theorem coulombDensity_hasFDerivAt {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    HasFDerivAt (coulombDensity N β)
      (coulombDensity N β z • innerSL ℝ (-gradient (coulombPotential β) z)) z := by
  let c : ℝ := (∫ x : CoulombConfig N, coulombWeight β x)⁻¹
  have hU := (coulombPotential_contDiffAt β hz).differentiableAt (by simp)
  have h := ((hU.hasFDerivAt.neg).exp).const_mul c
  have he : coulombDensity N β =ᶠ[𝓝 z] (fun x => c * Real.exp (-coulombPotential β x)) := by
    filter_upwards [(coulombDomain N).isOpen.mem_nhds hz] with x hx
    rw [coulombDensity, coulombWeight_eq_exp_neg_potential β hx]
  have hh := h.congr_of_eventuallyEq he
  have heD : innerSL ℝ (-gradient (coulombPotential β) z) =
      -fderiv ℝ (coulombPotential β) z := by
    ext v
    change inner ℝ (-gradient (coulombPotential β) z) v =
      -(fderiv ℝ (coulombPotential β) z v)
    rw [inner_neg_left, inner_gradient_left]
  rw [heD]
  simpa only [smul_smul, coulombDensity, coulombWeight_eq_exp_neg_potential β hz, Pi.neg_apply, c] using! hh

theorem coulombSqrtDensity_hasFDerivAt {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    HasFDerivAt (fun x => Real.sqrt (coulombDensity N β x))
      ((Real.sqrt (coulombDensity N β z) / 2) •
        innerSL ℝ (-gradient (coulombPotential β) z)) z := by
  have hp := coulombDensity_pos_off_collisions hβ hz
  have h := (coulombDensity_hasFDerivAt β hz).sqrt hp.ne'
  have hs : 0 < Real.sqrt (coulombDensity N β z) := Real.sqrt_pos.mpr hp
  have hc : (1 / (2 * Real.sqrt (coulombDensity N β z))) * coulombDensity N β z =
      Real.sqrt (coulombDensity N β z) / 2 := by
    have hsq := Real.sq_sqrt hp.le
    field_simp
    nlinarith
  simpa only [smul_smul, hc] using h

theorem coulombSqrtDensity_gradient {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    gradient (fun x => Real.sqrt (coulombDensity N β x)) z =
      (Real.sqrt (coulombDensity N β z) / 2) • (-gradient (coulombPotential β) z) := by
  apply (InnerProductSpace.toDual ℝ (CoulombConfig N)).injective
  rw [toDual_gradient, (coulombSqrtDensity_hasFDerivAt hβ hz).fderiv, map_smul]
  rfl

theorem coulombGroundStateCore_gradient_identity {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (z : CoulombConfig N) :
    Real.sqrt (coulombDensity N β z) • gradient (φ : CoulombConfig N → ℝ) z =
      gradient (coulombGroundStateCore hβ φ : CoulombConfig N → ℝ) z +
        (coulombGroundStateCore hβ φ z / 2) • gradient (coulombPotential β) z := by
  by_cases hz : z ∈ coulombDomain N
  · change Real.sqrt (coulombDensity N β z) • gradient (φ : CoulombConfig N → ℝ) z =
      gradient (fun x => φ x * Real.sqrt (coulombDensity N β x)) z +
        (φ z * Real.sqrt (coulombDensity N β z) / 2) • gradient (coulombPotential β) z
    rw [coulomb_gradient_mul (φ.contDiff.differentiable (by simp) z)
      (coulombSqrtDensity_hasFDerivAt hβ hz).differentiableAt,
      coulombSqrtDensity_gradient hβ hz]
    module
  · have hn : z ∉ tsupport (φ : CoulombConfig N → ℝ) := fun ht => hz (φ.tsupport_subset ht)
    have hn' : z ∉ tsupport (coulombGroundStateCore hβ φ : CoulombConfig N → ℝ) :=
      fun ht => hz ((coulombGroundStateCore hβ φ).tsupport_subset ht)
    rw [TauCeti.gradient_of_notMem_tsupport hn, TauCeti.gradient_of_notMem_tsupport hn',
      image_eq_zero_of_notMem_tsupport hn']
    simp

end RepulsiveCoulomb
