import PomdpLogging.BeliefCoverage

noncomputable section
open scoped BigOperators

namespace PomdpLogging

def runMemory (m : Memory) : {L : ℕ} → History L → Memory
  | 0, _ => m
  | _+1, (f,a) => updateMemory (runMemory m f) a

def runState (s : Bool) : {L : ℕ} → History L → Bool
  | 0, _ => s
  | _+1, (f,a) => transition (runState s f) a

theorem stateOf_runMemory (θ : Bool) (m : Memory) {L : ℕ} (f : History L) :
    stateOf θ (runMemory m f) = runState (stateOf θ m) f := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rcases f with ⟨f,a⟩
    simp only [runMemory, runState, stateOf_update, ih]

def continuationMass (m : Memory) : {L : ℕ} → History L → ℝ
  | 0, _ => 1
  | _+1, (f,a) => continuationMass m f * logger (runMemory m f) a

theorem continuationMass_pos (m : Memory) {L : ℕ} (f : History L) :
    0 < continuationMass m f := by
  induction L with
  | zero => norm_num [continuationMass]
  | succ L ih =>
    exact mul_pos (ih f.1) (lt_of_lt_of_le (by norm_num) (logger_coverage _ _))

theorem continuationMass_total (m : Memory) (L : ℕ) :
    ∑ f : History L, continuationMass m f = 1 := by
  induction L with
  | zero =>
    change (∑ _ : Unit, (1 : ℝ)) = 1
    norm_num
  | succ L ih =>
    change (∑ fa : History L × Action, continuationMass m fa.1 * logger (runMemory m fa.1) fa.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, logger_total, mul_one]
    exact ih

abbrev Future (L : ℕ) := History L × Bool

/-- A continuation with fixed initial physical bit and logger memory. This
law is later averaged over the *actual* conditional distribution of memory. -/
def futureLaw (s : Bool) (m : Memory) (L : ℕ) : Law (Future L) where
  mass fy := continuationMass m fy.1 * emission (runState s fy.1) fy.2
  nonneg fy := le_of_lt (mul_pos (continuationMass_pos m fy.1) (emission_pos _ _))
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, emission_total, mul_one]
    exact continuationMass_total m L

theorem future_mass_pos (s : Bool) (m : Memory) (L : ℕ) (f : Future L) :
    0 < (futureLaw s m L).mass f :=
  mul_pos (continuationMass_pos m f.1) (emission_pos _ _)

def appendHistory {n : ℕ} (h : History n) : {L : ℕ} → History L → History (n+L)
  | 0, _ => h
  | _+1, (f,a) => (appendHistory h f, a)

theorem memory_append {n L : ℕ} (h : History n) (f : History L) :
    memory (appendHistory h f) = runMemory (memory h) f := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rcases f with ⟨f,a⟩
    simp only [appendHistory, memory, runMemory, ih]

theorem actionWeight_eq_logger {n : ℕ} (hn : 0 < n) (h : History n) (a : Action) :
    actionWeight h a = logger (memory h) a := by
  cases n with
  | zero => omega
  | succ n => rfl

/-- Factorization of the actual logging probability at any nonempty prefix. -/
theorem historyMass_append {n L : ℕ} (hn : 0 < n) (h : History n) (f : History L) :
    historyMass (appendHistory h f) = historyMass h * continuationMass (memory h) f := by
  induction L with
  | zero => simp [appendHistory, continuationMass]
  | succ L ih =>
    rcases f with ⟨f,a⟩
    change historyMass (appendHistory h f) * actionWeight (appendHistory h f) a =
      historyMass h * (continuationMass (memory h) f * logger (runMemory (memory h) f) a)
    rw [actionWeight_eq_logger (by omega), memory_append, ih]
    ring

/-- Joint prefix/future law obtained by continuing the actual logger from the
memory computed from that prefix. Intermediate observations are fixed blanks. -/
def prefixFutureLaw (θ : Bool) (k L : ℕ) : Law (History (k+1) × Future L) where
  mass hf := historyMass hf.1 * (futureLaw (bitAfter θ hf.1) (memory hf.1) L).mass hf.2
  nonneg hf := mul_nonneg (historyMass_pos hf.1).le (Law.nonneg _ _)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, Law.total, mul_one]
    exact historyMass_total (k+1)

def stateFutureLaw (θ : Bool) (k L : ℕ) : Law (Bool × Future L) :=
  (prefixFutureLaw θ k L).map (fun hf => (bitAfter θ hf.1, hf.2))

/-- The paper's behavior-marginal outcome matrix, defined from an actual joint
law and the physical-state prior, not by stipulating a convenient channel. -/
def outcome (θ : Bool) (k L : ℕ) (f : Future L) (s : Bool) : ℝ :=
  (stateFutureLaw θ k L).mass (s,f) / stateMass θ k s

theorem prefixFuture_history_marginal (θ : Bool) (k L : ℕ) (h : History (k+1)) :
    ∑ f, (prefixFutureLaw θ k L).mass (h,f) = historyMass h := by
  simp only [prefixFutureLaw, ← Finset.mul_sum, Law.total, mul_one]

theorem prefixFuture_expect (θ : Bool) (k L : ℕ) (g : Bool → Future L → ℝ) :
    (prefixFutureLaw θ k L).expect (fun hf => g (bitAfter θ hf.1) hf.2) =
      (historyLaw (k+1)).expect (fun h =>
        (futureLaw (bitAfter θ h) (memory h) L).expect (g (bitAfter θ h))) := by
  simp only [Law.expect, prefixFutureLaw, historyLaw, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc]

/-- Exact reduction of the prefix average to the three memory labels. -/
theorem stateFuture_expect (θ : Bool) (k L : ℕ) (g : Bool → Future L → ℝ) :
    (stateFutureLaw θ k L).expect (fun sf => g sf.1 sf.2) =
      survival k * (futureLaw θ .fresh L).expect (g θ) +
      (1-survival k)/2 * (futureLaw false .zero L).expect (g false) +
      (1-survival k)/2 * (futureLaw true .one L).expect (g true) := by
  rw [stateFutureLaw, Law.expect_map, prefixFuture_expect]
  simp_rw [bitAfter_eq_stateOf]
  rw [memory_expect k (fun m => (futureLaw (stateOf θ m) m L).expect (g (stateOf θ m)))]
  rfl

end PomdpLogging
