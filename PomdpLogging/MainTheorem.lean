import PomdpLogging.BoundaryLayers
import PomdpLogging.MatrixForms
import PomdpLogging.UniformRate
import PomdpLogging.ProductReconstruction

noncomputable section
open scoped BigOperators
namespace PomdpLogging

abbrev InitialState := Unit
abbrev PhysicalState := Bool
abbrev IntermediateObservation := Unit
abbrev TerminalObservation := Bool

/-- A checklist of Theorem 4.1's claims for the explicitly constructed pair
`candidateModel false`, `candidateModel true`. Stage indices h are one-based,
as in the paper. The initial scalar layer is stated separately from the two-state
layers, so no padding by unreachable states changes the coverage condition. -/
structure PaperMainClaims (H : ℕ) : Prop where
  sizes : Fintype.card InitialState = 1 ∧ Fintype.card PhysicalState = 2 ∧
    Fintype.card Action = 3 ∧ Fintype.card Memory = 3 ∧
    Fintype.card IntermediateObservation = 1 ∧ Fintype.card TerminalObservation = 2
  bounded_return : ∀ y, 0 ≤ terminalReturn y ∧ terminalReturn y ≤ 1
  action_coverage : ∀ h (past : History h) a, 1/6 ≤ behaviorPolicy H h past a
  deterministic_target : targetPolicy.mass Action.hold = 1
  sampling_semantics : ∀ θ, (candidateModel θ).loggedDataLaw (H-2) = fullEpisodeLaw θ (H-2)
  initial_belief : initialBeliefGram = 1
  initial_revealing : ∀ θ, |((initialOutcomeGram θ (H-2))⁻¹) () ()| ≤ 35/9 ∧
    |((initialOutcomeGram θ (H-2))⁻¹) () ()| ≤ 9
  belief_coverage : ∀ θ h, 2 ≤ h → h < H → ∀ (lam : ℝ) (v : Bool → ℝ),
    v ≠ 0 → (beliefGram θ (h-2)).mulVec v = lam • v → 1/3 ≤ lam
  uniform_revealing : ∀ θ h, 2 ≤ h → h < H →
    matrixOneNorm ((actualChannel θ (h-2) (H-h)).gram)⁻¹ ≤ 35/9
  weighted_revealing : ∀ θ h, 2 ≤ h → h < H →
    matrixOneNorm ((actualChannel θ (h-2) (H-h)).weightedGram (stateMass θ (h-2) true))⁻¹ ≤ 9
  values : (candidateModel false).targetReturn (H-2) = 1/4 ∧
    (candidateModel true).targetReturn (H-2) = 3/4
  estimation_lower : ∀ n (A : ValueEstimator (Fin n → Episode (H-2) × Action))
    (δ : ℝ), 0 < δ → δ < 1/2 →
    A.failure (((candidateModel false).loggedDataLaw (H-2)).iid n) (1/4) ≤ δ →
    A.failure (((candidateModel true).loggedDataLaw (H-2)).iid n) (3/4) ≤ δ →
    2*binaryKL (1-δ) δ / (survival (H-2)*Real.log 3) ≤ n

/-- Theorem 4.1 for every requested horizon, with the precise constants.
All coverage and information inequalities are conclusions of earlier proofs;
none is assumed as a hypothesis of this theorem. -/
theorem main_theorem (H : ℕ) (_hH : 3 ≤ H) : PaperMainClaims H where
  sizes := by
    obtain ⟨h0, h1, ha, hm⟩ := model_cardinalities
    exact ⟨h0, h1, ha, hm, h0, h1⟩
  bounded_return := return_bounds
  action_coverage := behaviorPolicy_coverage H
  deterministic_target := targetPolicy_deterministic
  sampling_semantics θ := candidate_logged_data_law θ (H-2)
  initial_belief := initial_belief_gram
  initial_revealing θ := by rw [initial_inverse_norm]; norm_num
  belief_coverage θ h _ _ lam v hv he := belief_eigenvalue_lower θ (h-2) lam v hv he
  uniform_revealing θ h _ hh := by
    have hn : H-h-1+1 = H-h := by omega
    rw [← hn]
    exact actual_uniform_revealing θ (h-2) (H-h-1)
  weighted_revealing θ h _ hh := by
    have hn : H-h-1+1 = H-h := by omega
    rw [← hn]
    exact actual_weighted_revealing θ (h-2) (H-h-1)
  values := by rw [candidate_target_return, candidate_target_return,
    targetValue_zero, targetValue_one]; exact ⟨rfl, rfl⟩
  estimation_lower n A δ hd hu h0 h1 := by
    rw [candidate_logged_data_law] at h0 h1
    exact exact_estimation_sample_lower (H-2) n A hd hu h0 h1

end PomdpLogging
