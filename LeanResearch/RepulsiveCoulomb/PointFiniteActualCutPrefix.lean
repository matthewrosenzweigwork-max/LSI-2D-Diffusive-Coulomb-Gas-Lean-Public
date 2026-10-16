import LeanResearch.RepulsiveCoulomb.PointActualUnmarkedPreparationState

/-! SOURCE-ONLY, UNCOMPILED. A well-founded construction using only currently
available actual geometric transitions. It returns a finite actual prefix,
ending either with zero budget or with the exact unresolved marked-boundary
preparation case. It does NOT prove that the latter endpoint is impossible,
and hence does NOT assert the finite-allocation theorem prematurely.
No hypothetical stage family or move-existence premise occurs in the builder.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Geometry of an actual selected sector, independent of its varying current
state, so the finite prefix can return one ordinary list of actual embeddings. -/
structure PointActualAllocatedSector {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) where
  beta : ℝ
  positive : 0 < beta
  le_pi : beta ≤ Real.pi
  map : closedEuclideanSector beta → ℂ
  metric : ∀ x z, (pointSmoothConformalEDist a y (map x) (map z)).toReal = dist x z

def PointActualAllocatedSector.apex {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) : ℂ := S.map (flatLinkSectorApex S.positive.le)

def PointConstructedCutSector.allocated {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (S : PointConstructedCutSector a y P ν α) :
    PointActualAllocatedSector a y :=
  ⟨S.beta, S.positive, S.le_pi, S.map, S.metric⟩

/-- This inductive object records only already-constructed geometry. Its
blocked constructor openly identifies the missing mathematical input; its
terminal constructor requires only spent budget, never terminal coverage. -/
inductive PointFiniteActualCutPrefix {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) :
    {P : Set ℂ} → {ν α : ℂ →₀ ℝ} → PointGeometricCutState a y P ν α → Type
  | blocked {P ν α} (K : PointGeometricCutState a y P ν α)
      (marked : ∃ x, x ∈ pointSignedMarked ν α ∧ x ∈ frontier P)
      (no_clean : ¬ Nonempty K.CleanRay) : PointFiniteActualCutPrefix a y K
  | terminal {P ν α} (K : PointGeometricCutState a y P ν α)
      (B : PointConstructedPreparation a y P ν α)
      (S : PointConstructedCutSector a y B.Q B.curvature α)
      (spent : α = Finsupp.single S.apex S.beta) : PointFiniteActualCutPrefix a y K
  | next {P ν α} (K : PointGeometricCutState a y P ν α)
      (B : PointConstructedPreparation a y P ν α)
      (S : PointConstructedCutSector a y B.Q B.curvature α)
      (O : PointConstructedSectorResidual a y B.Q B.curvature α S)
      (tail : PointFiniteActualCutPrefix a y O.state) : PointFiniteActualCutPrefix a y K

/-- The genuine finite construction stops only at an exhausted budget or the
explicit geometric blocker. Recursion is on the rank proved from each actual
sector/contact output and preserved by actual preparation. -/
theorem point_construct_finite_actual_cut_prefix
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (K : PointGeometricCutState a y P ν α) :
    Nonempty (PointFiniteActualCutPrefix a y K) := by
  classical
  have build : ∀ n : ℕ, ∀ (P : Set ℂ) (ν α : ℂ →₀ ℝ)
      (K : PointGeometricCutState a y P ν α), pointCutOuterRank P ν α = n →
        Nonempty (PointFiniteActualCutPrefix a y K) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P ν α K hn
      rcases K.preparation_or_marked_obstruction ha y with hprep | ⟨hm, hc⟩
      · obtain ⟨B⟩ := hprep
        obtain ⟨S, hterminal | hnext⟩ := B.state.construct_sector_and_step ha y B.clean
        · exact ⟨PointFiniteActualCutPrefix.terminal K B S hterminal.2⟩
        · obtain ⟨O⟩ := hnext
          have hd : pointCutOuterRank O.Q O.curvature (retainedApexBudget α S.apex S.beta) < n :=
            hn ▸ O.rank_lt.trans_le B.rank_le
          obtain ⟨tail⟩ := ih _ hd _ _ _ O.state rfl
          exact ⟨PointFiniteActualCutPrefix.next K B S O tail⟩
      · exact ⟨PointFiniteActualCutPrefix.blocked K hm hc⟩
  exact build _ P ν α K rfl

namespace PointFiniteActualCutPrefix
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}

def sectors : {P : Set ℂ} → {ν α : ℂ →₀ ℝ} → {K : PointGeometricCutState a y P ν α} →
    PointFiniteActualCutPrefix a y K → List (PointActualAllocatedSector a y)
  | _, _, _, _, .blocked _ _ _ => []
  | _, _, _, _, .terminal _ _ S _ => [S.allocated]
  | _, _, _, _, .next _ _ S _ tail => S.allocated :: tail.sectors

def remaining : {P : Set ℂ} → {ν α : ℂ →₀ ℝ} → {K : PointGeometricCutState a y P ν α} →
    PointFiniteActualCutPrefix a y K → (ℂ →₀ ℝ)
  | _, _, α, _, .blocked _ _ _ => α
  | _, _, _, _, .terminal _ _ _ _ => 0
  | _, _, _, _, .next _ _ _ _ tail => tail.remaining

def completed : {P : Set ℂ} → {ν α : ℂ →₀ ℝ} → {K : PointGeometricCutState a y P ν α} →
    PointFiniteActualCutPrefix a y K → Prop
  | _, _, _, _, .blocked _ _ _ => False
  | _, _, _, _, .terminal _ _ _ _ => True
  | _, _, _, _, .next _ _ _ _ tail => tail.completed

end PointFiniteActualCutPrefix

/-- Sum in the ambient Finsupp, so coincident apices are coalesced exactly. -/
def pointActualAllocatedBudget {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (L : List (PointActualAllocatedSector a y)) : ℂ →₀ ℝ :=
  L.foldr (fun S b ↦ Finsupp.single S.apex S.beta + b) 0

namespace PointFiniteActualCutPrefix
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
  {P : Set ℂ} {ν α : ℂ →₀ ℝ} {K : PointGeometricCutState a y P ν α}

/-- Exact pointwise budget conservation for every constructed finite prefix,
including a prefix blocked before all allocation has been spent. -/
theorem budget_balance (T : PointFiniteActualCutPrefix a y K) :
    α = pointActualAllocatedBudget T.sectors + T.remaining := by
  induction T with
  | blocked K hm hc => simp [sectors, remaining, pointActualAllocatedBudget]
  | terminal K B S hspent =>
      simpa [sectors, remaining, pointActualAllocatedBudget,
        PointConstructedCutSector.allocated, PointActualAllocatedSector.apex,
        PointConstructedCutSector.apex] using hspent
  | next K B S O tail ih =>
      change _ = (Finsupp.single S.apex S.beta + pointActualAllocatedBudget tail.sectors) + tail.remaining
      rw [add_assoc, ← ih]
      change _ = _ + (_ - _)
      abel

theorem remaining_zero_of_completed (T : PointFiniteActualCutPrefix a y K)
    (h : T.completed) : T.remaining = 0 := by
  induction T with
  | blocked K hm hc => exact False.elim h
  | terminal K B S hspent => rfl
  | next K B S O tail ih => exact ih h

theorem exact_allocation_of_completed (T : PointFiniteActualCutPrefix a y K)
    (h : T.completed) : pointActualAllocatedBudget T.sectors = α := by
  have hb := T.budget_balance
  rw [T.remaining_zero_of_completed h, add_zero] at hb
  exact hb.symm

/-- If the actual prefix is not complete, it carries a concrete positive-budget
current region with the exact marked-boundary/no-clean-ray obstruction. -/
theorem obstruction_of_not_completed (T : PointFiniteActualCutPrefix a y K)
    (h : ¬T.completed) :
    ∃ (Q : Set ℂ) (μ : ℂ →₀ ℝ) (L : PointGeometricCutState a y Q μ T.remaining),
      (∃ x, x ∈ pointSignedMarked μ T.remaining ∧ x ∈ frontier Q) ∧ ¬Nonempty L.CleanRay := by
  induction T with
  | blocked K hm hc => exact ⟨_, _, K, hm, hc⟩
  | terminal K B S hspent => exact False.elim (h trivial)
  | next K B S O tail ih => exact ih h

end PointFiniteActualCutPrefix
end RepulsiveCoulomb
