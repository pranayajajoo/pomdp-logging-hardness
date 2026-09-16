import PomdpLogging.Episodes

noncomputable section
open scoped BigOperators Matrix

namespace PomdpLogging

/-- The actual joint distribution of the observable prefix and physical state. -/
def stateHistoryLaw (θ : Bool) (k : ℕ) : Law (History (k+1) × Bool) :=
  (historyLaw (k+1)).map (fun h => (h, bitAfter θ h))

theorem stateHistory_mass (θ : Bool) (k : ℕ) (h : History (k+1)) (s : Bool) :
    (stateHistoryLaw θ k).mass (h,s) =
      historyMass h * (if s = bitAfter θ h then 1 else 0) := by
  classical
  rw [stateHistoryLaw, Law.map_mass]
  unfold Law.expect
  rw [Finset.sum_eq_single h]
  · simp [Prod.mk.injEq, historyLaw]
  · intro b _ hb
    simp [Prod.mk.injEq, Ne.symm hb]
  · simp

/-- Conditional state probability, defined by joint mass divided by the actual
positive history marginal. No state oracle is supplied to an estimator. -/
def belief (θ : Bool) (k : ℕ) (h : History (k+1)) (s : Bool) : ℝ :=
  (stateHistoryLaw θ k).mass (h,s) / (historyLaw (k+1)).mass h

theorem belief_oneHot (θ : Bool) (k : ℕ) (h : History (k+1)) (s : Bool) :
    belief θ k h s = if s = bitAfter θ h then 1 else 0 := by
  rw [belief, stateHistory_mass]
  change (historyMass h * _) / historyMass h = _
  by_cases hs : s = bitAfter θ h <;> simp [hs, ne_of_gt (historyMass_pos h)]

def beliefGram (θ : Bool) (k : ℕ) : Matrix Bool Bool ℝ :=
  fun s t => (historyLaw (k+1)).expect (fun h => belief θ k h s * belief θ k h t)

theorem bool_oneHot_mul (s t b : Bool) :
    (if s = b then (1 : ℝ) else 0) * (if t = b then 1 else 0) =
      if s = t then (if s = b then 1 else 0) else 0 := by
  cases s <;> cases t <;> cases b <;> norm_num

theorem beliefGram_diagonal (θ : Bool) (k : ℕ) :
    beliefGram θ k = Matrix.diagonal (stateMass θ k) := by
  classical
  ext s t
  simp only [beliefGram, Law.expect, belief_oneHot, bool_oneHot_mul, Matrix.diagonal_apply]
  by_cases hst : s = t
  · subst t
    simp only [ite_true]
    rw [← actual_state_mass θ k s, Law.map_mass]
    simp only [Law.expect, bitAfter_eq_stateOf]
  · simp [hst]

/-- Every real eigenvalue of the actual belief Gram matrix is at least 1/3.
The matrix is explicitly diagonal, so this is the paper's minimum-eigenvalue
coverage bound, expressed without an arbitrary ordering of eigenvectors. -/
theorem belief_eigenvalue_lower (θ : Bool) (k : ℕ) (lam : ℝ) (v : Bool → ℝ)
    (hv : v ≠ 0) (he : (beliefGram θ k).mulVec v = lam • v) : 1/3 ≤ lam := by
  have hex : ∃ s, v s ≠ 0 := by
    by_contra! h
    apply hv
    funext s
    exact h s
  obtain ⟨s, hs⟩ := hex
  have he' := congrFun he s
  rw [beliefGram_diagonal, Matrix.mulVec_diagonal] at he'
  change stateMass θ k s * v s = lam * v s at he'
  have hm : (stateMass θ k s - lam) * v s = 0 := by nlinarith [he']
  rcases mul_eq_zero.mp hm with h | h
  · linarith [stateMass_ge_third θ k s]
  · exact False.elim (hs h)

end PomdpLogging
