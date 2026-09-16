# Formalization status

The exact main theorem and full-data minimax and sample-complexity results are
proved. Formal objects are connected to the specified POMDP kernels, logger,
conditional beliefs, and behavior-marginal futures. All results are symbolic in
the horizon and sample size.

| Manuscript claim | Formal evidence | Status |
|---|---|---|
| Actual POMDP, common logger, target, data law | `candidate_logged_data_law`, `stage_joint_consistency`, `main_theorem` | Proved |
| Memory masses and all-hold probability | `memory_expect`, `actual_memory_law`, `allHold_mass` | Proved |
| Conditional physical beliefs and coverage 3 | `belief_oneHot`, `belief_eigenvalue_lower`, `initial_belief_eigenvalue_lower` | Proved |
| Action coverage 6 | `behaviorPolicy_coverage` | Proved |
| Actual conditional outcome matrix | `outcome_memory_formula`, `stage_joint_consistency` | Proved |
| Literal matrix-product definitions of G and K | `PositiveChannel.gram_matrix_formula`, `PositiveChannel.weightedGram_matrix_formula` | Proved |
| Uniform-prior inverse 1-norm bound 35/9 | `actual_uniform_revealing`, `initial_inverse_norm` | Proved |
| Prior-weighted inverse 1-norm bound 9 | `actual_weighted_revealing`, `initial_inverse_norm` | Proved |
| Terminal uniform-prior constant 4 | `actual_terminal_revealing` | Proved |
| Target values 1/4 and 3/4 | `candidate_target_return`, `targetValue_zero`, `targetValue_one` | Proved |
| Full support; exact trajectory and product KL | `full_episode_mass_pos`, `full_trajectory_kl`, `full_dataset_kl` | Proved |
| Theorem 4.1, every H >= 3 | `main_theorem`, `exact_estimation_sample_lower` | Proved |
| Proposition 5.1, both directions of experiment equivalence | `full_dataset_compression`, `reconstructs_full_dataset` | Proved |
| Theorem 5.2, full-data minimax and fair-tie majority | `likelihood_is_majority`, `majority_risk_formula`, `exact_full_data_minimax` | Proved |
| Exact minimax lower and upper bounds | `minimax_risk_lower`, `minimax_risk_upper` | Proved |
| Corollary 4.2, exact sample sandwich and uniform rate | `accuracy_iff_risk`, `exact_sample_sandwich`, `uniform_sample_rate` | Proved |
| Appendix C, failed belief factorization | `same_physical_belief`, `same_belief_logger_tv`, `no_physical_state_factorization` | Proved |
| Appendix C, rare augmented-state eigenvalue | `augmentedBeliefGram_diagonal`, `augmented_rare_eigenvalue`, `augmented_coverage_cost` | Proved |
| Appendix C, persistent suffix ambiguity and distances | `no_fixed_suffix`, `fixed_suffix_belief_distance`, `fixed_suffix_logger_distance` | Proved |
| Appendix D, actual compact statistic, 2L+2 symbols | `compact_cardinality` | Proved |
| Appendix D, state-independent reconstruction and exact G/K preservation | `compact_reconstruction_factor`, `compact_preserves_grams` | Proved |
| Appendix E, actual deterministic model and target values | `deterministic_model_law`, `deterministic_target_return` | Proved |
| Appendix E, three-symbol law, full-data TV and estimation minimax | `deterministic_actual_symbol_law`, `deterministic_totalVariation`, `deterministic_exact_minimax` | Proved |
| Automatic axiom audit of every project declaration | `Audit.lean`, run by `check.sh` | Passed |
| Fresh project rebuild with pinned dependencies | `clean-build.log`, exit status 0 | Passed |

The appendix coverage is as listed above. The deterministic variant's additional
revealing assertion and the compact matrix's standalone tabulation formulas are
not separately exported theorems. These are not hypotheses or gaps in the verified
main theorem. See [VERIFICATION.md](VERIFICATION.md) for the precise scope.
