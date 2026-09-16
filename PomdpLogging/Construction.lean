import PomdpLogging.FiniteProbability

noncomputable section
open scoped BigOperators

namespace PomdpLogging

inductive Action where
  | hold | resetZero | resetOne
  deriving DecidableEq, Repr

instance : Fintype Action := ⟨{.hold, .resetZero, .resetOne}, by
  intro a
  cases a <;> simp⟩

inductive Memory where
  | fresh | zero | one
  deriving DecidableEq, Repr

instance : Fintype Memory := ⟨{.fresh, .zero, .one}, by
  intro m
  cases m <;> simp⟩

def updateMemory (m : Memory) : Action → Memory
  | .hold => m
  | .resetZero => .zero
  | .resetOne => .one

def preferred : Memory → Action
  | .fresh => .hold
  | .zero => .resetZero
  | .one => .resetOne

def logger (m : Memory) (a : Action) : ℝ := if a = preferred m then 2/3 else 1/6

theorem sum_action (f : Action → ℝ) :
    ∑ a, f a = f .hold + f .resetZero + f .resetOne := by
  change (∑ a ∈ ({.hold, .resetZero, .resetOne} : Finset Action), f a) = _
  simp [add_assoc]

theorem sum_memory (f : Memory → ℝ) :
    ∑ m, f m = f .fresh + f .zero + f .one := by
  change (∑ m ∈ ({.fresh, .zero, .one} : Finset Memory), f m) = _
  simp [add_assoc]

theorem logger_coverage (m : Memory) (a : Action) : 1/6 ≤ logger m a := by
  unfold logger
  split_ifs <;> norm_num

theorem logger_total (m : Memory) : ∑ a, logger m a = 1 := by
  rw [sum_action]
  cases m <;> norm_num [logger, preferred]

def loggerLaw (m : Memory) : Law Action where
  mass := logger m
  nonneg a := le_trans (by norm_num) (logger_coverage m a)
  total := logger_total m

def stateOf (θ : Bool) : Memory → Bool
  | .fresh => θ
  | .zero => false
  | .one => true

def transition (s : Bool) : Action → Bool
  | .hold => s
  | .resetZero => false
  | .resetOne => true

theorem stateOf_update (θ : Bool) (m : Memory) (a : Action) :
    stateOf θ (updateMemory m a) = transition (stateOf θ m) a := by
  cases a <;> rfl

def emission (s y : Bool) : ℝ := if y = s then 3/4 else 1/4

theorem emission_pos (s y : Bool) : 0 < emission s y := by
  unfold emission
  split_ifs <;> norm_num

theorem emission_total (s : Bool) : ∑ y, emission s y = 1 := by
  cases s <;> norm_num [emission, Bool.forall_bool]

def emissionLaw (s : Bool) : Law Bool where
  mass := emission s
  nonneg y := le_of_lt (emission_pos s y)
  total := emission_total s

/-- Histories contain only the nonterminal actions; intermediate observations
are deterministic time-tagged blanks. The terminal bit is added separately. -/
def History : ℕ → Type
  | 0 => Unit
  | n+1 => History n × Action

instance historyFintype (n : ℕ) : Fintype (History n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (History n × Action))

instance historyDecidableEq (n : ℕ) : DecidableEq (History n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (History n × Action))

def memory : {n : ℕ} → History n → Memory
  | 0, _ => .fresh
  | _+1, (h,a) => updateMemory (memory h) a

def actionWeight : {n : ℕ} → History n → Action → ℝ
  | 0, _, _ => 1/3
  | _+1, h, a => logger (memory h) a

theorem actionWeight_coverage {n : ℕ} (h : History n) (a : Action) :
    1/6 ≤ actionWeight h a := by
  cases n with
  | zero => norm_num [actionWeight]
  | succ n => exact logger_coverage _ _

theorem actionWeight_total {n : ℕ} (h : History n) : ∑ a, actionWeight h a = 1 := by
  cases n with
  | zero => rw [sum_action]; norm_num [actionWeight]
  | succ n => exact logger_total _

def historyMass : {n : ℕ} → History n → ℝ
  | 0, _ => 1
  | _+1, (h,a) => historyMass h * actionWeight h a

theorem historyMass_pos {n : ℕ} (h : History n) : 0 < historyMass h := by
  induction n with
  | zero => simp [historyMass]
  | succ n ih =>
    exact mul_pos (ih h.1) (lt_of_lt_of_le (by norm_num) (actionWeight_coverage h.1 h.2))

theorem historyMass_total (n : ℕ) : ∑ h : History n, historyMass h = 1 := by
  induction n with
  | zero =>
    change (∑ _ : Unit, (1 : ℝ)) = 1
    norm_num
  | succ n ih =>
    change (∑ h : History n × Action, historyMass h.1 * actionWeight h.1 h.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, actionWeight_total, mul_one]
    exact ih

def historyLaw (n : ℕ) : Law (History n) where
  mass := historyMass
  nonneg h := le_of_lt (historyMass_pos h)
  total := historyMass_total n

def allHold : (n : ℕ) → History n
  | 0 => ()
  | n+1 => (allHold n, .hold)

@[simp] theorem memory_allHold (n : ℕ) : memory (allHold n) = .fresh := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [allHold, memory, updateMemory] using ih

theorem memory_fresh_iff {n : ℕ} (h : History n) : memory h = .fresh ↔ h = allHold n := by
  induction n with
  | zero => exact iff_of_true rfl (@Subsingleton.elim Unit inferInstance h ())
  | succ n ih =>
    rcases h with ⟨h,a⟩
    change updateMemory (memory h) a = .fresh ↔ (h,a) = (allHold n, Action.hold)
    cases a <;> simp [updateMemory, ih, Prod.mk.injEq]

/-- `k` is the number of actions after the initial uniform action; H = k+2. -/
def survival (k : ℕ) : ℝ := (1/3) * (2/3)^k

theorem allHold_mass (k : ℕ) : historyMass (allHold (k+1)) = survival k := by
  induction k with
  | zero => norm_num [allHold, historyMass, actionWeight, survival]
  | succ k ih =>
    change historyMass (allHold (k+1)) * logger (memory (allHold (k+1))) .hold = _
    rw [memory_allHold, ih]
    norm_num [logger, preferred, survival, pow_succ]
    ring

theorem survival_pos (k : ℕ) : 0 < survival k := by
  unfold survival
  positivity

theorem survival_le_third (k : ℕ) : survival k ≤ 1/3 := by
  have h : (2/3 : ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold survival
  linarith

end PomdpLogging
