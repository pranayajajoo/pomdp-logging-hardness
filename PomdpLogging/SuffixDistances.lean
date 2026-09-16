import PomdpLogging.MemoryObstructions

noncomputable section
open scoped BigOperators
namespace PomdpLogging

/-- The physical beliefs stay at l1 distance two after every common hold suffix. -/
theorem fixed_suffix_belief_distance (θ : Bool) (L : ℕ)
    (h0 h1 : History (L+1)) (hm0 : memory h0 = .zero) (hm1 : memory h1 = .one) :
    (∑ s, |belief θ L h0 s-belief θ L h1 s|) = 2 := by
  simp_rw [belief_oneHot, bitAfter_eq_stateOf, hm0, hm1]
  norm_num [stateOf]

/-- Same physical belief and a persistent l1 distance one between action laws,
for arbitrarily long identical suffixes; all exhibited histories have positive mass. -/
theorem fixed_suffix_logger_distance (θ : Bool) (L : ℕ) :
    ∃ h0 h1 : History (1+L),
      suffixActions 1 L h0 = suffixActions 1 L h1 ∧
      stateOf θ (memory h0) = stateOf θ (memory h1) ∧
      (∑ a, |logger (memory h0) a-logger (memory h1) a|) = 1 ∧
      0 < historyMass h0 ∧ 0 < historyMass h1 := by
  let h0 := appendHistory firstHold (allHold L)
  let h1 := appendHistory (firstReset θ) (allHold L)
  have hm0 : memory h0 = memory firstHold := by rw [memory_append, runMemory_allHold]
  have hm1 : memory h1 = memory (firstReset θ) := by rw [memory_append, runMemory_allHold]
  refine ⟨h0, h1, ?_, ?_, ?_, historyMass_pos h0, historyMass_pos h1⟩
  · rw [suffix_append, suffix_append]
  · rw [hm0, hm1]
    cases θ <;> rfl
  · rw [hm0, hm1]
    linarith [same_belief_logger_tv θ]

end PomdpLogging
