import PomdpLogging.UniformChannel
import PomdpLogging.RevealingEvent

noncomputable section
open scoped BigOperators

namespace PomdpLogging

def actualChannel (θ : Bool) (k L : ℕ) : PositiveChannel (Future L) where
  entry := outcome θ k L
  positive := outcome_pos θ k L
  total := outcome_total θ k L

def stateLabel (θ i : Bool) : Bool := if i then !θ else θ

/-- Relabel the two columns in the order theta, 1-theta used in the paper's proof. -/
def orderedChannel (θ : Bool) (k L : ℕ) : PositiveChannel (Future L) where
  entry f i := outcome θ k L f (stateLabel θ i)
  positive f i := outcome_pos θ k L f (stateLabel θ i)
  total i := outcome_total θ k L (stateLabel θ i)

theorem ordered_channel_event_zero (θ : Bool) (k L : ℕ) :
    (∑ f ∈ Finset.univ.filter (fun f : Future (L+1) => firstAction f.1 = resetTo (!θ)),
      (orderedChannel θ k (L+1)).entry f false) = 1/6 := by
  simpa [orderedChannel, stateLabel, revealWeight, mul_ite, Finset.sum_filter] using
    reveal_probability_same θ k L

theorem ordered_channel_event_one (θ : Bool) (k L : ℕ) :
    (∑ f ∈ Finset.univ.filter (fun f : Future (L+1) => firstAction f.1 = resetTo (!θ)),
      (orderedChannel θ k (L+1)).entry f true) = 2/3 := by
  simpa [orderedChannel, stateLabel, revealWeight, mul_ite, Finset.sum_filter] using
    reveal_probability_other θ k L

theorem ordered_gram_eq_actual (θ : Bool) (k L : ℕ) :
    (orderedChannel θ k L).gram = (actualChannel θ k L).gram := by
  cases θ with
  | false =>
    ext s t
    cases s <;> cases t <;> rfl
  | true =>
    have he (s t : Bool) : (orderedChannel true k L).gram s t =
        (actualChannel true k L).gram (!s) (!t) := by
      unfold PositiveChannel.gram
      apply Finset.sum_congr rfl
      intro f _
      cases s <;> cases t <;>
        simp [orderedChannel, actualChannel, stateLabel, PositiveChannel.denominator, add_comm]
    ext s t
    rw [he, PositiveChannel.gram_swap_entry]

/-- Lemma A.3 for the actual physical-state outcome matrix at every
noninitial, nonterminal stage. Here h = k+2 and H-h = L+1. -/
theorem actual_uniform_revealing (θ : Bool) (k L : ℕ) :
    matrixOneNorm ((actualChannel θ k (L+1)).gram)⁻¹ ≤ 35/9 := by
  rw [← ordered_gram_eq_actual]
  exact (orderedChannel θ k (L+1)).uniform_bound
    (fun f => firstAction f.1 = resetTo (!θ))
    (ordered_channel_event_zero θ k L) (ordered_channel_event_one θ k L)

end PomdpLogging
