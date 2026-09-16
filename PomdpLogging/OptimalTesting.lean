import PomdpLogging.FiniteProbability

noncomputable section
open scoped BigOperators
namespace PomdpLogging

def likelihoodDecision (p q : ℝ) : ℝ :=
  if p < q then 1 else if q < p then 0 else 1/2

theorem likelihoodDecision_bounds (p q : ℝ) :
    0 ≤ likelihoodDecision p q ∧ likelihoodDecision p q ≤ 1 := by
  unfold likelihoodDecision
  split_ifs <;> norm_num

theorem likelihoodDecision_complement (p q : ℝ) :
    likelihoodDecision q p = 1-likelihoodDecision p q := by
  unfold likelihoodDecision
  split_ifs <;> norm_num <;> linarith

theorem likelihoodDecision_optimal (p q : ℝ) :
    p*likelihoodDecision p q + q*(1-likelihoodDecision p q) = min p q := by
  rcases lt_trichotomy p q with h | h | h
  · simp [likelihoodDecision, h, min_eq_left h.le]
  · subst q
    simp [likelihoodDecision]
    ring
  · simp [likelihoodDecision, h, not_lt.mpr h.le, min_eq_right h.le]

def likelihoodTest {α : Type*} [Fintype α] (P Q : Law α) : Test α where
  one x := likelihoodDecision (P.mass x) (Q.mass x)
  nonneg x := (likelihoodDecision_bounds _ _).1
  le_one x := (likelihoodDecision_bounds _ _).2

def overlapRisk {α : Type*} [Fintype α] (P Q : Law α) : ℝ :=
  (∑ x, min (P.mass x) (Q.mass x))/2

theorem likelihood_errors_sum {α : Type*} [Fintype α] (P Q : Law α) :
    (likelihoodTest P Q).errorZero P + (likelihoodTest P Q).errorOne Q =
      2*overlapRisk P Q := by
  unfold Test.errorZero Test.errorOne Law.expect likelihoodTest overlapRisk
  rw [← Finset.sum_add_distrib]
  simp_rw [likelihoodDecision_optimal]
  ring

theorem likelihood_balanced {α : Type*} [Fintype α] (P Q : Law α) (e : α ≃ α)
    (hP : ∀ x, P.mass (e x) = Q.mass x) (hQ : ∀ x, Q.mass (e x) = P.mass x) :
    (likelihoodTest P Q).errorZero P = (likelihoodTest P Q).errorOne Q := by
  unfold Test.errorZero Test.errorOne Law.expect likelihoodTest
  apply Fintype.sum_equiv e
  intro x
  change P.mass x * likelihoodDecision (P.mass x) (Q.mass x) =
    Q.mass (e x) * (1-likelihoodDecision (P.mass (e x)) (Q.mass (e x)))
  rw [hP, hQ, likelihoodDecision_complement]

theorem balanced_likelihood_risk {α : Type*} [Fintype α] (P Q : Law α)
    (hb : (likelihoodTest P Q).errorZero P = (likelihoodTest P Q).errorOne Q) :
    (likelihoodTest P Q).errorZero P = overlapRisk P Q ∧
    (likelihoodTest P Q).errorOne Q = overlapRisk P Q ∧
    (likelihoodTest P Q).worstError P Q = overlapRisk P Q := by
  have hs := likelihood_errors_sum P Q
  have h0 : (likelihoodTest P Q).errorZero P = overlapRisk P Q := by linarith
  have h1 : (likelihoodTest P Q).errorOne Q = overlapRisk P Q := by linarith
  exact ⟨h0, h1, by simp [Test.worstError, h0, h1]⟩

theorem balanced_likelihood_minimax {α : Type*} [Fintype α] (P Q : Law α)
    (hb : (likelihoodTest P Q).errorZero P = (likelihoodTest P Q).errorOne Q)
    (T : Test α) :
    (likelihoodTest P Q).worstError P Q ≤ T.worstError P Q := by
  rw [(balanced_likelihood_risk P Q hb).2.2]
  exact T.overlap_lower P Q

end PomdpLogging
