import PomdpLogging.MemoryObstructions

noncomputable section
open scoped BigOperators
namespace PomdpLogging

/-- Zero-based time and value of the first reset in an action suffix. -/
def earliestReset : {L : ℕ} → History L → Option (ℕ × Bool)
  | 0, _ => none
  | L+1, (h,a) => match earliestReset h with
    | some tr => some tr
    | none => match a with
      | .hold => none
      | .resetZero => some (L,false)
      | .resetOne => some (L,true)

theorem earliestReset_allHold (L : ℕ) : earliestReset (allHold L) = none := by
  induction L with
  | zero => rfl
  | succ L ih => simpa [allHold, earliestReset, ih]

theorem earliestReset_none_iff {L : ℕ} (h : History L) :
    earliestReset h = none ↔ h = allHold L := by
  constructor
  · intro he
    induction L with
    | zero => cases h; rfl
    | succ L ih =>
      rcases h with ⟨h,a⟩
      cases hp : earliestReset h with
      | none =>
        have hh := ih h hp
        subst h
        cases a <;> simp_all [earliestReset, allHold] <;> rfl
      | some tr => simp [earliestReset, hp] at he
  · rintro rfl
    exact earliestReset_allHold L

theorem earliestReset_lt {L : ℕ} (h : History L) (t : ℕ) (r : Bool)
    (he : earliestReset h = some (t,r)) : t < L := by
  induction L with
  | zero => simp [earliestReset] at he
  | succ L ih =>
    rcases h with ⟨h,a⟩
    cases hp : earliestReset h with
    | none =>
      cases a <;> simp [earliestReset, hp] at he
      all_goals rcases he with ⟨rfl, rfl⟩; omega
    | some tr =>
      have ht : tr = (t,r) := by simpa [earliestReset, hp] using he
      subst tr
      exact (ih h hp).trans (Nat.lt_succ_self L)

theorem runMemory_from_fresh {L : ℕ} (h : History L) : runMemory .fresh h = memory h := by
  induction L with
  | zero => rfl
  | succ L ih => rcases h with ⟨h,a⟩; simp [runMemory, memory, ih]

theorem runMemory_formula (m : Memory) {L : ℕ} (h : History L) :
    runMemory m h = if memory h = .fresh then m else memory h := by
  induction L with
  | zero => simp [runMemory, memory]
  | succ L ih =>
    rcases h with ⟨h,a⟩
    cases a <;> simp [runMemory, memory, updateMemory, ih] <;> rfl

theorem runMemory_after_reset (m : Memory) {L : ℕ} (h : History L)
    (he : earliestReset h ≠ none) : runMemory m h = memory h := by
  rw [runMemory_formula]
  apply if_neg
  intro hm
  apply he
  exact (earliestReset_none_iff h).mpr ((memory_fresh_iff h).mp hm)

theorem runState_memory (s : Bool) {L : ℕ} (h : History L) :
    runState s h = stateOf s (memory h) := by
  have he := stateOf_runMemory s Memory.fresh h
  rw [runMemory_from_fresh] at he
  exact he.symm

theorem runState_after_reset (s t : Bool) {L : ℕ} (h : History L)
    (he : earliestReset h ≠ none) : runState s h = runState t h := by
  rw [runState_memory, runState_memory]
  have hm : memory h ≠ .fresh := by
    intro hh
    exact he ((earliestReset_none_iff h).mpr ((memory_fresh_iff h).mp hh))
  cases hh : memory h with
  | fresh => exact False.elim (hm hh)
  | zero => rfl
  | one => rfl

theorem continuationMass_allHold (m : Memory) (L : ℕ) :
    continuationMass m (allHold L) = (logger m .hold)^L := by
  induction L with
  | zero => simp [allHold, continuationMass]
  | succ L ih => simp [allHold, continuationMass, runMemory_allHold, ih, pow_succ]

def resetPrefixProbability (m : Memory) (t : ℕ) (r : Bool) : ℝ :=
  (logger m .hold)^t * logger m (resetTo r)

theorem resetPrefixProbability_pos (m : Memory) (t : ℕ) (r : Bool) :
    0 < resetPrefixProbability m t r := by
  have h0 : 0 < logger m .hold := lt_of_lt_of_le (by norm_num) (logger_coverage _ _)
  have h1 : 0 < logger m (resetTo r) := lt_of_lt_of_le (by norm_num) (logger_coverage _ _)
  exact mul_pos (pow_pos h0 t) h1

/-- After the first reset, all dependence on incoming memory has been paid
in the probability of reaching that reset. Subsequent action factors cancel. -/
theorem continuation_firstReset_factor (m : Memory) {L : ℕ} (h : History L)
    (t : ℕ) (r : Bool) (he : earliestReset h = some (t,r)) :
    continuationMass m h * resetPrefixProbability .fresh t r =
      continuationMass .fresh h * resetPrefixProbability m t r := by
  induction L with
  | zero => simp [earliestReset] at he
  | succ L ih =>
    rcases h with ⟨h,a⟩
    cases hp : earliestReset h with
    | none =>
      have hh := (earliestReset_none_iff h).mp hp
      subst h
      cases a <;> simp [earliestReset, hp] at he
      all_goals
        rcases he with ⟨rfl, rfl⟩
        simp [continuationMass, continuationMass_allHold, runMemory_allHold,
          resetPrefixProbability, resetTo, mul_comm]
    | some tr =>
      have ht : tr = (t,r) := by simpa [earliestReset, hp] using he
      subst tr
      have hn : earliestReset h ≠ none := by rw [hp]; simp
      have hih := ih h hp
      change (continuationMass m h * logger (runMemory m h) a) * _ =
        (continuationMass .fresh h * logger (runMemory .fresh h) a) * _
      rw [runMemory_after_reset m h hn, runMemory_from_fresh]
      nlinarith [congrArg (fun x : ℝ => x * logger (memory h) a) hih]

end PomdpLogging
