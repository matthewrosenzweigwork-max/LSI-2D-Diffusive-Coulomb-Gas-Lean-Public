import LeanResearch.RepulsiveCoulomb.JordanTurnAngleLift
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Analysis.Calculus.DSlope

/-! A genuine geometric construction for the Hopf secant proof of total turn.
The open ordered-parameter triangle is constructed, proved contractible, and
its secant direction is lifted to a continuous real angle using injectivity of
the actual curve.  There are no triangulation, winding, or angle-sum inputs.
This does not yet extend the lift to the diagonal and corner blow-ups. -/
noncomputable section
open Set
open scoped Topology
namespace RepulsiveCoulomb

/-- Ordered, distinct interior parameters. -/
def euclideanSecantTriangle : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1}

theorem euclideanSecantTriangle_convex : Convex ℝ euclideanSecantTriangle := by
  have h₁ := (convex_Ioi (0 : ℝ)).linear_preimage (LinearMap.fst ℝ ℝ ℝ)
  have h₂ := (convex_Ioi (0 : ℝ)).linear_preimage
    (LinearMap.snd ℝ ℝ ℝ - LinearMap.fst ℝ ℝ ℝ)
  have h₃ := (convex_Iio (1 : ℝ)).linear_preimage (LinearMap.snd ℝ ℝ ℝ)
  convert h₁.inter (h₂.inter h₃) using 1
  ext p
  simp [euclideanSecantTriangle, sub_pos]

theorem euclideanSecantTriangle_open : IsOpen euclideanSecantTriangle :=
  (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const))

theorem euclideanSecantTriangle_nonempty : euclideanSecantTriangle.Nonempty :=
  ⟨(1 / 3, 2 / 3), by norm_num [euclideanSecantTriangle]⟩

/-- The secant of the actual curve at an ordered pair of distinct parameters. -/
def euclideanSecant (γ : ℝ → ℂ) (p : euclideanSecantTriangle) : ℂ :=
  γ p.1.2 - γ p.1.1

theorem euclideanSecant_ne_zero {γ : ℝ → ℂ}
    (hinj : InjOn γ (Ioo (0 : ℝ) 1)) (p : euclideanSecantTriangle) :
    euclideanSecant γ p ≠ 0 := by
  intro h
  have heq : γ p.1.2 = γ p.1.1 := sub_eq_zero.mp h
  have hp := p.2
  have hsame := hinj ⟨lt_trans hp.1 hp.2.1, hp.2.2⟩
    ⟨hp.1, lt_trans hp.2.1 hp.2.2⟩ heq
  exact (ne_of_lt hp.2.1) hsame.symm

theorem euclideanSecant_continuous {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Ioo (0 : ℝ) 1)) :
    Continuous (euclideanSecant γ) := by
  have h₁ : Continuous (fun p : euclideanSecantTriangle => γ p.1.1) :=
    hγ.comp_continuous (continuous_fst.comp continuous_subtype_val)
      (fun p => ⟨p.2.1, lt_trans p.2.2.1 p.2.2.2⟩)
  have h₂ : Continuous (fun p : euclideanSecantTriangle => γ p.1.2) :=
    hγ.comp_continuous (continuous_snd.comp continuous_subtype_val)
      (fun p => ⟨lt_trans p.2.1 p.2.2.1, p.2.2.2⟩)
  exact h₂.sub h₁

/-- A simple continuous curve has a single continuous real branch of the
argument of all its ordered secants.  The domain and the lift are constructed,
not supplied as geometric certificates. -/
theorem exists_simple_curve_secant_angle {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Ioo (0 : ℝ) 1))
    (hinj : InjOn γ (Ioo (0 : ℝ) 1)) :
    ∃ A : euclideanSecantTriangle → ℝ, Continuous A ∧
      ∀ p, Complex.exp ((A p : ℂ) * Complex.I) =
        (γ p.1.2 - γ p.1.1) / (‖γ p.1.2 - γ p.1.1‖ : ℂ) := by
  letI : ContractibleSpace euclideanSecantTriangle :=
    euclideanSecantTriangle_convex.contractibleSpace euclideanSecantTriangle_nonempty
  letI : LocallyPathConnectedSpace euclideanSecantTriangle :=
    euclideanSecantTriangle_open.locallyPathConnectedSpace
  let p₀ : euclideanSecantTriangle := ⟨(1 / 3, 2 / 3), by
    norm_num [euclideanSecantTriangle]⟩
  let θ₀ := Complex.arg (euclideanSecant γ p₀)
  obtain ⟨A, hA, _, hlift⟩ := exists_euclidean_angle_lift
    (euclideanSecant_continuous hγ) (euclideanSecant_ne_zero hinj) p₀ θ₀ (by
      dsimp only [θ₀]
      rw [← euclideanDirection_arg (euclideanSecant γ p₀)
        (euclideanSecant_ne_zero hinj p₀)]
      exact Circle.exp_arg _)
  refine ⟨A, hA, fun p => ?_⟩
  exact congrArg (fun z : Circle => (z : ℂ)) (hlift p)

/-- The forward secant directions converge to the normalized actual derivative.
This is a boundary value for the secant map, not an assumed tangent winding. -/
theorem normalized_forward_secant_tendsto {γ : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (hγ : HasDerivAt γ v t) (hv : v ≠ 0) :
    Filter.Tendsto (fun s : ℝ =>
      slope γ t s / (‖slope γ t s‖ : ℂ)) (𝓝[>] t) (𝓝 (v / (‖v‖ : ℂ))) := by
  have hslope := hγ.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t)
  exact hslope.div ((Complex.continuous_ofReal.tendsto ‖v‖).comp hslope.norm)
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv))

end RepulsiveCoulomb
