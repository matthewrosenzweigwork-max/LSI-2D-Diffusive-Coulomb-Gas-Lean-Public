module

public import LeanResearch.RepulsiveCoulomb.DbarBranchMetricCoefficientSmoothness
public import LeanResearch.RepulsiveCoulomb.DbarBranchProperMetricCutoff
public import LeanResearch.RepulsiveCoulomb.DbarBranchLocalCoreMultiplier

@[expose] public section

/-! Proper metric cutoffs extend every locally smooth coefficient to an
actual compact smooth function equal to it near a prescribed compact set.
One cutoff radius works for an entire finite operator coefficient system. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

def coulombGraphRadiusSublevel (N : ℕ) (R : ℝ) : Set (CoulombConfig N) :=
  {z | z ∈ coulombDomain N ∧ coulombGraphRadius z < R}

theorem coulombGraphRadiusSublevel_isOpen (N : ℕ) (R : ℝ) :
    IsOpen (coulombGraphRadiusSublevel N R) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  exact inter_mem ((coulombDomain N).isOpen.mem_nhds hz.1)
    ((coulombGraphRadius_contDiffAt hz.1).continuousAt.eventually (Iio_mem_nhds hz.2))

theorem coulombCompact_in_radius_sublevel {N : ℕ} {K : Set (CoulombConfig N)}
    (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N) :
    ∃ R : ℝ, 0 < R ∧ K ⊆ coulombGraphRadiusSublevel N R := by
  have hc : ContinuousOn (coulombGraphRadius (N := N)) K :=
    fun z hz => (coulombGraphRadius_contDiffAt (hKΩ hz)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.bddAbove_image hc
  refine ⟨max M 0 + 1, by positivity, ?_⟩
  intro z hz
  refine ⟨hKΩ hz, ?_⟩
  have hm : coulombGraphRadius z ≤ M := hM ⟨z, hz, rfl⟩
  exact hm.trans_lt (lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one)

def coulombCoefficientExtension {N : ℕ} (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    {R : ℝ} (hR : 0 < R) : TestFunction (coulombDomain N) ℂ ⊤ :=
  coulombComplexCoreMulLocal a ha
    (TestFunction.postcompCLM Complex.ofRealCLM (coulombMetricCutoffTest (N := N) hR))

theorem coulombCoefficientExtension_eq {N : ℕ} (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    {R : ℝ} (hR : 0 < R) {z : CoulombConfig N}
    (hz : z ∈ coulombGraphRadiusSublevel N R) :
    coulombCoefficientExtension a ha hR z = a z := by
  change a z * (coulombMetricCutoff R z : ℂ) = a z
  rw [coulombMetricCutoff_eq_one hR hz.1 hz.2.le]
  simp

theorem coulombCoefficientExtension_eventuallyEq {N : ℕ} (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    {R : ℝ} (hR : 0 < R) {z : CoulombConfig N}
    (hz : z ∈ coulombGraphRadiusSublevel N R) :
    (coulombCoefficientExtension a ha hR : CoulombConfig N → ℂ) =ᶠ[𝓝 z] a := by
  filter_upwards [(coulombGraphRadiusSublevel_isOpen N R).mem_nhds hz] with w hw
  exact coulombCoefficientExtension_eq a ha hR hw

theorem coulombCoefficientExtension_fderiv {N : ℕ} (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    {R : ℝ} (hR : 0 < R) {z : CoulombConfig N}
    (hz : z ∈ coulombGraphRadiusSublevel N R) :
    fderiv ℝ (coulombCoefficientExtension a ha hR : CoulombConfig N → ℂ) z = fderiv ℝ a z :=
  (coulombCoefficientExtension_eventuallyEq a ha hR hz).fderiv_eq

def coulombCoefficientExtensionGlobal {N : ℕ} (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    {R : ℝ} (hR : 0 < R) : TestFunction (⊤ : TopologicalSpace.Opens (CoulombConfig N)) ℂ ⊤ :=
  ⟨coulombCoefficientExtension a ha hR, (coulombCoefficientExtension a ha hR).contDiff,
    (coulombCoefficientExtension a ha hR).hasCompactSupport, subset_univ _⟩

end RepulsiveCoulomb
