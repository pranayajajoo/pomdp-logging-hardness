import PomdpLogging
import Lean.Util.CollectAxioms

/-! Reject every axiom dependency other than mathlib's three standard foundations.
This checks all public project declarations, plus private project declarations
whose generated names start with `_private.PomdpLogging`. -/
run_cmd do
  let env ← Lean.getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "PomdpLogging." ||
        name.toString.startsWith "_private.PomdpLogging" then
      declarations := declarations + 1
      if let .thmInfo _ := info then theorems := theorems + 1
      for ax in ← Lean.collectAxioms name do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
  unless theorems > 100 do
    throwError "Audit imported too few project theorems: {theorems}"
  Lean.logInfo m!"Axiom audit passed: {declarations} project declarations, {theorems} theorems. Allowed dependencies: propext, Classical.choice, Quot.sound."

#print axioms PomdpLogging.main_theorem
#print axioms PomdpLogging.exact_estimation_sample_lower
#print axioms PomdpLogging.exact_full_data_minimax
#print axioms PomdpLogging.exact_sample_sandwich
#print axioms PomdpLogging.uniform_sample_rate
#print axioms PomdpLogging.compact_preserves_grams
#print axioms PomdpLogging.deterministic_exact_minimax
#print axioms PomdpLogging.deterministic_totalVariation
