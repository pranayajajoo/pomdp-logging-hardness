import PomdpLogging.StageConsistency
import PomdpLogging.RevealingEvent

noncomputable section
open scoped BigOperators
namespace PomdpLogging

def firstHold : History 1 := ((), .hold)
def firstReset (θ : Bool) : History 1 := ((), resetTo θ)

theorem same_physical_belief (θ : Bool) :
    belief θ 0 firstHold = belief θ 0 (firstReset θ) := by
  funext s
  rw [belief_oneHot, belief_oneHot]
  cases θ <;> rfl

theorem same_belief_logger_tv (θ : Bool) :
    (∑ a, |logger (memory firstHold) a - logger (memory (firstReset θ)) a|)/2 = 1/2 := by
  rw [sum_action]
  cases θ <;> norm_num [firstHold, firstReset, resetTo, memory, updateMemory, logger, preferred]

theorem different_conditional_futures (θ : Bool) (L : ℕ) :
    futureLaw (bitAfter θ firstHold) (memory firstHold) (L+1) ≠
      futureLaw (bitAfter θ (firstReset θ)) (memory (firstReset θ)) (L+1) := by
  intro he
  have h := congrArg (fun P : Law (Future (L+1)) =>
    P.expect (fun f => if firstAction f.1 = Action.hold then (1 : ℝ) else 0)) he
  rw [future_first_action_prob, future_first_action_prob] at h
  cases θ <;> norm_num [firstHold, firstReset, resetTo, memory, updateMemory, logger, preferred] at h

/-- Proposition C.1: there is no history-independent physical-state outcome
matrix that factors every conditional future distribution through the belief. -/
theorem no_physical_state_factorization (θ : Bool) (L : ℕ) :
    ¬ ∃ U : Future (L+1) → Bool → ℝ, ∀ (h : History 1) (f : Future (L+1)),
      (futureLaw (bitAfter θ h) (memory h) (L+1)).mass f =
        ∑ s, U f s * belief θ 0 h s := by
  rintro ⟨U, hU⟩
  apply different_conditional_futures θ L
  ext f
  rw [hU, hU, same_physical_belief]

def memoryHistoryLaw (k : ℕ) : Law (History (k+1) × Memory) :=
  (historyLaw (k+1)).map (fun h => (h,memory h))

def augmentedBelief (k : ℕ) (h : History (k+1)) (m : Memory) : ℝ :=
  (memoryHistoryLaw k).mass (h,m) / historyMass h

theorem augmentedBelief_oneHot (k : ℕ) (h : History (k+1)) (m : Memory) :
    augmentedBelief k h m = if m = memory h then 1 else 0 := by
  classical
  have he : (memoryHistoryLaw k).mass (h,m) = historyMass h*(if m = memory h then 1 else 0) := by
    rw [memoryHistoryLaw, Law.map_mass]
    unfold Law.expect
    rw [Finset.sum_eq_single h]
    · simp [Prod.mk.injEq, historyLaw]
    · intro b _ hb
      simp [Prod.mk.injEq, Ne.symm hb]
    · simp
  rw [augmentedBelief, he]
  by_cases hm : m = memory h <;> simp [hm, (historyMass_pos h).ne']

def augmentedBeliefGram (k : ℕ) : Matrix Memory Memory ℝ :=
  fun m r => (historyLaw (k+1)).expect (fun h => augmentedBelief k h m * augmentedBelief k h r)

theorem augmentedBeliefGram_diagonal (k : ℕ) :
    augmentedBeliefGram k = Matrix.diagonal (memoryMass k) := by
  ext m r
  simp only [augmentedBeliefGram, augmentedBelief_oneHot]
  rw [memory_expect k (fun b => (if m = b then 1 else 0)*(if r = b then 1 else 0))]
  cases m <;> cases r <;> simp [memoryMass, Matrix.diagonal_apply]

def freshVector : Memory → ℝ := fun m => if m = .fresh then 1 else 0

theorem augmented_rare_eigenvalue (k : ℕ) :
    freshVector ≠ 0 ∧ (augmentedBeliefGram k).mulVec freshVector = survival k • freshVector := by
  constructor
  · intro h
    have hh := congrFun h Memory.fresh
    norm_num [freshVector] at hh
  · rw [augmentedBeliefGram_diagonal]
    funext m
    rw [Matrix.mulVec_diagonal]
    cases m <;> simp [memoryMass, freshVector]

theorem augmented_inverse_rate (k : ℕ) : 1/survival k = 3*(3/2 : ℝ)^k := by
  have hp : (2/3 : ℝ)^k*(3/2 : ℝ)^k = 1 := by rw [← mul_pow]; norm_num
  apply (div_eq_iff (survival_pos k).ne').mpr
  unfold survival
  nlinarith

theorem augmented_coverage_cost (k : ℕ) {C : ℝ} (hC : 0 < C)
    (hcover : ∀ (lam : ℝ) (v : Memory → ℝ), v ≠ 0 →
      (augmentedBeliefGram k).mulVec v = lam • v → 1/C ≤ lam) :
    3*(3/2 : ℝ)^k ≤ C := by
  obtain ⟨hv, he⟩ := augmented_rare_eigenvalue k
  have hc := hcover (survival k) freshVector hv he
  rw [← augmented_inverse_rate]
  apply (div_le_iff₀ (survival_pos k)).mpr
  have hh := (div_le_iff₀ hC).mp hc
  linarith

theorem reachable_augmented_state_injective (θ : Bool) :
    Function.Injective (fun m : Memory => (stateOf θ m,m)) := by
  intro m r he
  exact congrArg Prod.snd he

theorem runMemory_allHold (m : Memory) (L : ℕ) : runMemory m (allHold L) = m := by
  induction L with
  | zero => rfl
  | succ L ih => simpa [allHold, runMemory, updateMemory] using ih

def suffixActions (n L : ℕ) (h : History (n+L)) : History L :=
  ((historyJoinEquiv n L).symm h).2

theorem suffix_append (n L : ℕ) (h : History n) (f : History L) :
    suffixActions n L (appendHistory h f) = f := by
  rw [← historyJoinEquiv_apply]
  simp [suffixActions]

/-- For every proposed fixed window, positive-probability histories have the
same observed suffix but opposite physical states. No bounded window suffices. -/
theorem no_fixed_suffix (L : ℕ) :
    ∃ h0 h1 : History (1+L),
      suffixActions 1 L h0 = suffixActions 1 L h1 ∧
      memory h0 = .zero ∧ memory h1 = .one ∧
      stateOf false (memory h0) ≠ stateOf false (memory h1) ∧
      0 < historyMass h0 ∧ 0 < historyMass h1 := by
  let h0 := appendHistory (firstReset false) (allHold L)
  let h1 := appendHistory (firstReset true) (allHold L)
  have hm0 : memory h0 = .zero := by rw [memory_append, runMemory_allHold]; rfl
  have hm1 : memory h1 = .one := by rw [memory_append, runMemory_allHold]; rfl
  refine ⟨h0, h1, ?_, hm0, hm1, ?_, historyMass_pos h0, historyMass_pos h1⟩
  · rw [suffix_append, suffix_append]
  · rw [hm0, hm1]
    decide

end PomdpLogging
