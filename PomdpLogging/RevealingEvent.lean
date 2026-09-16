import PomdpLogging.OutcomeProbability

noncomputable section
open scoped BigOperators

namespace PomdpLogging

def firstAction : {L : ℕ} → History (L+1) → Action
  | 0, (_,a) => a
  | _+1, (f,_) => firstAction f

theorem continuation_first_expect (m : Memory) (L : ℕ) (g : Action → ℝ) :
    (∑ f : History (L+1), continuationMass m f * g (firstAction f)) =
      ∑ a, logger m a * g a := by
  induction L with
  | zero =>
    change (∑ fa : Unit × Action, (1 * logger m fa.2) * g fa.2) = _
    simp [Fintype.sum_prod_type]
  | succ L ih =>
    change (∑ fa : History (L+1) × Action,
      (continuationMass m fa.1 * logger (runMemory m fa.1) fa.2) * g (firstAction fa.1)) = _
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum, logger_total, mul_one]
    exact ih

theorem future_first_expect (s : Bool) (m : Memory) (L : ℕ) (g : Action → ℝ) :
    (futureLaw s m (L+1)).expect (fun f => g (firstAction f.1)) =
      ∑ a, logger m a * g a := by
  change (∑ fy : History (L+1) × Bool,
    (continuationMass m fy.1 * emission (runState s fy.1) fy.2) * g (firstAction fy.1)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, emission_total, mul_one]
  exact continuation_first_expect m L g

theorem future_first_action_prob (s : Bool) (m : Memory) (L : ℕ) (a : Action) :
    (futureLaw s m (L+1)).expect (fun f => if firstAction f.1 = a then 1 else 0) =
      logger m a := by
  rw [future_first_expect s m L (fun a' => if a' = a then 1 else 0)]
  simp [mul_ite]

def resetTo (s : Bool) : Action := if s then .resetOne else .resetZero

def revealWeight (θ : Bool) {L : ℕ} (f : Future (L+1)) : ℝ :=
  if firstAction f.1 = resetTo (!θ) then 1 else 0

theorem future_reveal_expect (s : Bool) (m : Memory) (L : ℕ) (θ : Bool) :
    (futureLaw s m (L+1)).expect (revealWeight θ) = logger m (resetTo (!θ)) :=
  future_first_action_prob s m L (resetTo (!θ))

/-- The binary coarsening has probability 1/6 in physical state theta. -/
theorem reveal_probability_same (θ : Bool) (k L : ℕ) :
    (∑ f, outcome θ k (L+1) f θ * revealWeight θ f) = 1/6 := by
  rw [outcome_expect]
  simp_rw [future_reveal_expect]
  have hp : 1+survival k ≠ 0 := by linarith [survival_pos k]
  cases θ <;> norm_num [stateMass, logger, preferred, resetTo] <;> field_simp <;> ring

/-- The same coarsening has probability 2/3 in the other physical state. -/
theorem reveal_probability_other (θ : Bool) (k L : ℕ) :
    (∑ f, outcome θ k (L+1) f (!θ) * revealWeight θ f) = 2/3 := by
  rw [outcome_expect]
  simp_rw [future_reveal_expect]
  have hp : 1-survival k ≠ 0 := by linarith [survival_le_third k]
  cases θ <;> norm_num [stateMass, logger, preferred, resetTo] <;> field_simp <;> ring

end PomdpLogging
