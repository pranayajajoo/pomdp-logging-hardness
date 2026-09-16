import PomdpLogging.ModelSemantics
import PomdpLogging.UniformRevealing

noncomputable section
open scoped BigOperators
namespace PomdpLogging

def initialBelief : Unit → ℝ := fun s => (Law.pure ()).mass s

def initialBeliefGram : Matrix Unit Unit ℝ :=
  fun s t => initialBelief s * initialBelief t

def initialOutcome (θ : Bool) (k : ℕ) : Episode k → Unit → ℝ :=
  fun e _ => (episodeLaw θ k).mass e

def initialOutcomeGram (θ : Bool) (k : ℕ) : Matrix Unit Unit ℝ :=
  fun s t => ∑ e, initialOutcome θ k e s * initialOutcome θ k e t /
    (∑ u, initialOutcome θ k e u)

theorem initial_belief_gram : initialBeliefGram = 1 := by
  ext s t
  cases s
  cases t
  simp [initialBeliefGram, initialBelief, Law.pure]

theorem initial_outcome_gram (θ : Bool) (k : ℕ) : initialOutcomeGram θ k = 1 := by
  ext s t
  cases s
  cases t
  simp only [initialOutcomeGram, initialOutcome, Fintype.sum_unique]
  have he (e : Episode k) : (episodeLaw θ k).mass e * (episodeLaw θ k).mass e /
      (episodeLaw θ k).mass e = (episodeLaw θ k).mass e :=
    mul_div_cancel_right₀ _ (episode_mass_pos θ k e).ne'
  simp_rw [he]
  simp [Law.total]

theorem initial_belief_eigenvalue_lower {lam : ℝ} {v : Unit → ℝ} (hv : v ≠ 0)
    (he : initialBeliefGram.mulVec v = lam • v) : 1/3 ≤ lam := by
  rw [initial_belief_gram, Matrix.one_mulVec] at he
  have h := congrFun he ()
  have hn : v () ≠ 0 := by
    intro hz
    apply hv
    funext u
    cases u
    exact hz
  have hl : lam = 1 := by
    apply (mul_right_cancel₀ hn)
    simpa using h.symm
  rw [hl]
  norm_num

theorem initial_inverse_norm (θ : Bool) (k : ℕ) :
    |((initialOutcomeGram θ k)⁻¹) () ()| = 1 := by
  rw [initial_outcome_gram]
  simp

theorem terminal_outcome (θ : Bool) (k : ℕ) (f : Future 0) (s : Bool) :
    outcome θ k 0 f s = emission s f.2 := by
  rw [outcome_memory_formula]
  have hp := survival_pos k
  have hu := survival_le_third k
  have hs0 : 1-survival k ≠ 0 := by linarith
  have hs1 : 1+survival k ≠ 0 := by linarith
  cases θ <;> cases s <;>
    simp [futureLaw, continuationMass, runState, stateMass] <;> field_simp <;> ring

theorem terminal_gram (θ : Bool) (k : ℕ) :
    (actualChannel θ k 0).gram = symmetricStochastic (1/4) := by
  ext s t
  simp only [PositiveChannel.gram, actualChannel, PositiveChannel.denominator]
  simp_rw [terminal_outcome]
  cases s <;> cases t <;>
    norm_num [Fintype.sum_prod_type, emission, symmetricStochastic, History]
  all_goals decide

theorem actual_terminal_revealing (θ : Bool) (k : ℕ) :
    matrixOneNorm ((actualChannel θ k 0).gram)⁻¹ = 4 := by
  rw [terminal_gram]
  exact terminal_revealing_norm

end PomdpLogging
