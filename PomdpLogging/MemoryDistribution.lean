import PomdpLogging.Construction

noncomputable section
open scoped BigOperators

namespace PomdpLogging

/-- The law of memory is derived from the full weighted action-history space.
The statement for arbitrary `f` also gives each individual memory mass. -/
theorem memory_expect (k : ℕ) (f : Memory → ℝ) :
    (historyLaw (k+1)).expect (fun h => f (memory h)) =
      survival k * f .fresh + (1-survival k)/2 * f .zero +
        (1-survival k)/2 * f .one := by
  induction k generalizing f with
  | zero =>
    change (∑ ha : Unit × Action,
      (1 * (1/3 : ℝ)) * f (updateMemory .fresh ha.2)) = _
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_unique]
    rw [sum_action]
    norm_num [updateMemory, survival]
  | succ k ih =>
    change (∑ ha : History (k+1) × Action,
      (historyMass ha.1 * logger (memory ha.1) ha.2) *
        f (updateMemory (memory ha.1) ha.2)) = _
    rw [Fintype.sum_prod_type]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    change (historyLaw (k+1)).expect
      (fun h => ∑ a, logger (memory h) a * f (updateMemory (memory h) a)) = _
    rw [ih (fun m => ∑ a, logger m a * f (updateMemory m a))]
    simp only [sum_action]
    norm_num [logger, preferred, updateMemory, survival, pow_succ]
    ring

def memoryMass (k : ℕ) : Memory → ℝ
  | .fresh => survival k
  | .zero => (1-survival k)/2
  | .one => (1-survival k)/2

theorem memoryMass_nonneg (k : ℕ) (m : Memory) : 0 ≤ memoryMass k m := by
  have hp := survival_pos k
  have hb := survival_le_third k
  cases m <;> simp only [memoryMass] <;> linarith

def memoryLaw (k : ℕ) : Law Memory where
  mass := memoryMass k
  nonneg := memoryMass_nonneg k
  total := by rw [sum_memory]; simp only [memoryMass]; ring

theorem actual_memory_law (k : ℕ) : (historyLaw (k+1)).map memory = memoryLaw k := by
  classical
  ext m
  rw [Law.map_mass]
  rw [memory_expect k (fun m' => if m = m' then 1 else 0)]
  cases m <;> simp [memoryLaw, memoryMass]

def stateMass (θ : Bool) (k : ℕ) (s : Bool) : ℝ :=
  if s = θ then (1 + survival k)/2 else (1 - survival k)/2

theorem stateMass_ge_third (θ : Bool) (k : ℕ) (s : Bool) :
    1/3 ≤ stateMass θ k s := by
  have hp := survival_pos k
  have hb := survival_le_third k
  unfold stateMass
  split_ifs <;> linarith

theorem actual_state_mass (θ : Bool) (k : ℕ) (s : Bool) :
    ((historyLaw (k+1)).map (fun h => stateOf θ (memory h))).mass s = stateMass θ k s := by
  classical
  rw [Law.map_mass]
  rw [memory_expect k (fun m => if s = stateOf θ m then 1 else 0)]
  cases θ <;> cases s <;> simp [stateOf, stateMass] <;> ring

end PomdpLogging
