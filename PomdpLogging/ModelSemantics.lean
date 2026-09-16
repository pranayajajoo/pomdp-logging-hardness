import PomdpLogging.StageConsistency

noncomputable section
open scoped BigOperators
namespace PomdpLogging

theorem Law.pure_bind {α β : Type*} [Fintype α] [Fintype β]
    (a : α) (K : α → Law β) : (Law.pure a).bind K = K a := by
  classical
  ext b
  simp [Law.bind, Law.pure]

/-- A layered POMDP with singleton initial state, two physical states thereafter,
singleton nonterminal observations, and a binary terminal observation.
Intermediate observations carry no information. Terminal reward is the observed bit.
The kernels here, rather than logger memory, specify the physical model. -/
structure BinaryLayeredModel where
  firstTransition : Unit → Action → Law Bool
  transition : Bool → Action → Law Bool
  terminalEmission : Bool → Law Bool

def candidateModel (θ : Bool) : BinaryLayeredModel where
  firstTransition _ a := Law.pure (transition θ a)
  transition s a := Law.pure (transition s a)
  terminalEmission := emissionLaw

def BinaryLayeredModel.stateGivenActions (M : BinaryLayeredModel) :
    {k : ℕ} → History (k+1) → Law Bool
  | 0, ha => M.firstTransition () ha.2
  | _+1, ha => (M.stateGivenActions ha.1).bind (fun s => M.transition s ha.2)

theorem candidate_state_given_actions (θ : Bool) {k : ℕ} (h : History (k+1)) :
    (candidateModel θ).stateGivenActions h = Law.pure (bitAfter θ h) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases h with ⟨h,a⟩
    change ((candidateModel θ).stateGivenActions h).bind _ = _
    rw [ih, Law.pure_bind]
    rfl

def BinaryLayeredModel.observationGivenActions (M : BinaryLayeredModel)
    {k : ℕ} (h : History (k+1)) : Law Bool :=
  (M.stateGivenActions h).bind M.terminalEmission

def BinaryLayeredModel.observableLaw (M : BinaryLayeredModel) (k : ℕ) : Law (Episode k) where
  mass hy := historyMass hy.1 * (M.observationGivenActions hy.1).mass hy.2
  nonneg hy := mul_nonneg (historyMass_pos hy.1).le (Law.nonneg _ _)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, Law.total, mul_one]
    exact historyMass_total (k+1)

def BinaryLayeredModel.loggedDataLaw (M : BinaryLayeredModel) (k : ℕ) : Law (Episode k × Action) :=
  (M.observableLaw k).prod finalActionLaw

theorem candidate_observable_law (θ : Bool) (k : ℕ) :
    (candidateModel θ).observableLaw k = episodeLaw θ k := by
  ext hy
  simp only [BinaryLayeredModel.observableLaw, BinaryLayeredModel.observationGivenActions,
    candidate_state_given_actions, Law.pure_bind]
  rfl

theorem candidate_logged_data_law (θ : Bool) (k : ℕ) :
    (candidateModel θ).loggedDataLaw k = fullEpisodeLaw θ k := by
  unfold BinaryLayeredModel.loggedDataLaw fullEpisodeLaw
  rw [candidate_observable_law]

def terminalReturn (y : Bool) : ℝ := if y then 1 else 0

theorem return_bounds (y : Bool) : 0 ≤ terminalReturn y ∧ terminalReturn y ≤ 1 := by
  cases y <;> norm_num [terminalReturn]

def BinaryLayeredModel.targetReturn (M : BinaryLayeredModel) (k : ℕ) : ℝ :=
  (M.observationGivenActions (allHold (k+1))).expect terminalReturn

theorem candidate_target_return (θ : Bool) (k : ℕ) :
    (candidateModel θ).targetReturn k = targetValue θ := by
  unfold BinaryLayeredModel.targetReturn BinaryLayeredModel.observationGivenActions
  rw [candidate_state_given_actions, Law.pure_bind, target_bit]
  rfl

/-- Stage is zero-based here. The policy is a common function of actions only;
it ignores current observations and has no model or hidden-state argument. -/
def behaviorPolicy (H h : ℕ) (past : History h) (a : Action) : ℝ :=
  if h+1 = H then 1/3 else actionWeight past a

theorem behaviorPolicy_coverage (H h : ℕ) (past : History h) (a : Action) :
    1/6 ≤ behaviorPolicy H h past a := by
  unfold behaviorPolicy
  split_ifs
  · norm_num
  · exact actionWeight_coverage past a

def targetPolicy : Law Action := Law.pure Action.hold

theorem targetPolicy_deterministic : targetPolicy.mass Action.hold = 1 := by
  simp [targetPolicy, Law.pure]

theorem model_cardinalities : Fintype.card Unit = 1 ∧ Fintype.card Bool = 2 ∧
    Fintype.card Action = 3 ∧ Fintype.card Memory = 3 := by
  constructor
  · decide
  constructor
  · decide
  constructor <;> decide

end PomdpLogging
