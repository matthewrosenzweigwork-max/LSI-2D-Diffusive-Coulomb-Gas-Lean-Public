import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-! Uncompiled additive successor. Construct a complete isometric line from
compact rational-time samples whose finite distances are eventually exact.
The pointwise subsequence is obtained from compactness of a countable product;
the real line is constructed by uniform extension along the dense rational
embedding. No preexisting line or Arzela-Ascoli certificate is assumed. -/
noncomputable section
open Set Filter Topology
namespace RepulsiveCoulomb

theorem exists_rational_isometry_limit_of_compact_coordinates
    {X : Type*} [MetricSpace X] (f : ℕ → ℚ → X) (K : ℚ → Set X)
    (hK : ∀ q, IsCompact (K q)) (hmem : ∀ n q, f n q ∈ K q)
    (hexact : ∀ q r : ℚ, ∀ᶠ n in atTop, dist (f n q) (f n r) = dist q r) :
    ∃ g : ℚ → X, Isometry g ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ q : ℚ, Tendsto (fun n => f (σ n) q) atTop (𝓝 (g q)) := by
  have hcompact : IsCompact {g : ℚ → X | ∀ q, g q ∈ K q} := isCompact_pi_infinite hK
  obtain ⟨g, hgK, σ, hσ, hlim⟩ := hcompact.tendsto_subseq (fun n => hmem n)
  have hpoint (q : ℚ) : Tendsto (fun n => f (σ n) q) atTop (𝓝 (g q)) := by
    simpa only [Function.comp_def] using ((continuous_apply q).tendsto g).comp hlim
  have hgi : Isometry g := by
    apply Isometry.of_dist_eq
    intro q r
    have hd := (hpoint q).dist (hpoint r)
    have he : ∀ᶠ n in atTop, dist (f (σ n) q) (f (σ n) r) = dist q r :=
      hσ.tendsto_atTop.eventually (hexact q r)
    have hc : Tendsto (fun n => dist (f (σ n) q) (f (σ n) r)) atTop (𝓝 (dist q r)) :=
      tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)
    exact tendsto_nhds_unique hd hc
  exact ⟨g, hgi, σ, hσ, hpoint⟩

theorem exists_real_isometry_extending_rational
    {X : Type*} [MetricSpace X] [CompleteSpace X] (g : ℚ → X) (hg : Isometry g) :
    ∃ c : ℝ → X, Isometry c ∧ ∀ q : ℚ, c q = g q := by
  let hi := Rat.isUniformEmbedding_coe_real.isUniformInducing
  let hd := hi.isDenseInducing Rat.denseRange_cast
  let c : ℝ → X := hd.extend g
  have huc : UniformContinuous c :=
    uniformContinuous_uniformly_extend hi Rat.denseRange_cast hg.uniformContinuous
  have hrestrict (q : ℚ) : c q = g q :=
    uniformly_extend_of_ind hi Rat.denseRange_cast hg.uniformContinuous q
  have hclosed : IsClosed {v : ℝ × ℝ | dist (c v.1) (c v.2) = dist v.1 v.2} :=
    isClosed_eq ((huc.continuous.comp continuous_fst).dist (huc.continuous.comp continuous_snd))
      (continuous_fst.dist continuous_snd)
  have hiso : Isometry c := by
    apply Isometry.of_dist_eq
    intro x y
    refine (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).induction_on₂
      (p := fun x y : ℝ => dist (c x) (c y) = dist x y) hclosed ?_ x y
    intro q r
    rw [hrestrict q, hrestrict r, hg.dist_eq, Rat.dist_cast]
  exact ⟨c, hiso, hrestrict⟩

theorem exists_real_isometric_line_limit_of_compact_rational_samples
    {X : Type*} [MetricSpace X] [CompleteSpace X] (f : ℕ → ℚ → X) (K : ℚ → Set X)
    (hK : ∀ q, IsCompact (K q)) (hmem : ∀ n q, f n q ∈ K q)
    (hexact : ∀ q r : ℚ, ∀ᶠ n in atTop, dist (f n q) (f n r) = dist q r) :
    ∃ c : ℝ → X, Isometry c ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ q : ℚ, Tendsto (fun n => f (σ n) q) atTop (𝓝 (c q)) := by
  obtain ⟨g, hg, σ, hσ, hpoint⟩ :=
    exists_rational_isometry_limit_of_compact_coordinates f K hK hmem hexact
  obtain ⟨c, hc, hrestrict⟩ := exists_real_isometry_extending_rational g hg
  refine ⟨c, hc, σ, hσ, ?_⟩
  intro q
  rw [hrestrict]
  exact hpoint q

end RepulsiveCoulomb
