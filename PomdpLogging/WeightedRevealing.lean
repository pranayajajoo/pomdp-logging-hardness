import PomdpLogging.WeightedChannel
import PomdpLogging.StochasticInverse
import PomdpLogging.UniformRevealing

noncomputable section
open scoped BigOperators
namespace PomdpLogging
namespace PositiveChannel

variable {F : Type*} [Fintype F]

theorem weightedGram_form (U : PositiveChannel F) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ' : ρ < 1) :
    U.weightedGram ρ = columnStochastic (ρ*U.overlap ρ) ((1-ρ)*U.overlap ρ) := by
  have h0 := U.weightedGram_column_sum hρ hρ' false
  have h1 := U.weightedGram_column_sum hρ hρ' true
  have hc := U.weightedGram_cross ρ
  ext s t
  cases s <;> cases t <;> simp only [columnStochastic, Bool.false_eq_true,
    ite_true, ite_false] <;> linarith [hc.1, hc.2]

theorem weighted_bound (U : PositiveChannel F) {ρ q r : ℝ}
    (hρ : 1/3 ≤ ρ) (hρ' : ρ ≤ 2/3)
    (E : F → Prop) [DecidablePred E]
    (hq : (∑ f ∈ Finset.univ.filter E, U.entry f false) = q)
    (hr : (∑ f ∈ Finset.univ.filter E, U.entry f true) = r)
    (hq0 : 0 < q) (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hdiff : (r-q)^2 = 1/4) : matrixOneNorm (U.weightedGram ρ)⁻¹ ≤ 9 := by
  have hp : 0 < ρ := by linarith
  have hu : ρ < 1 := by linarith
  have hc := U.contrast_lower hp hu E hq hr hq0 hq1 hr0 hr1 hdiff
  have hi := U.contrast_identity hp hu
  have hs := U.overlap_nonneg hp hu
  have hrange : 2/9 ≤ ρ*(1-ρ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (sub_nonneg.mpr hρ')]
  have hl : 2/9 ≤ 1-ρ*U.overlap ρ-(1-ρ)*U.overlap ρ := by
    nlinarith [mul_nonneg (show 0 ≤ ρ*(1-ρ) by positivity) (sub_nonneg.mpr hc)]
  rw [U.weightedGram_form hp hu]
  exact columnStochastic_inv_bound (mul_nonneg hp.le hs)
    (mul_nonneg (by linarith) hs) hl

end PositiveChannel

theorem stateMass_le_two_thirds (θ : Bool) (k : ℕ) (s : Bool) :
    stateMass θ k s ≤ 2/3 := by
  have hp := survival_pos k
  have hb := survival_le_third k
  unfold stateMass
  split_ifs <;> linarith

/-- Lemma A.5, including the actual behavior prior and the actual outcome law. -/
theorem actual_weighted_revealing (θ : Bool) (k L : ℕ) :
    matrixOneNorm ((actualChannel θ k (L+1)).weightedGram (stateMass θ k true))⁻¹ ≤ 9 := by
  have hq := ordered_channel_event_zero θ k L
  have hr := ordered_channel_event_one θ k L
  cases θ with
  | false =>
    apply PositiveChannel.weighted_bound _ (stateMass_ge_third false k true)
      (stateMass_le_two_thirds false k true)
      (fun f : Future (L+1) => firstAction f.1 = resetTo true)
      (q := 1/6) (r := 2/3)
    · exact hq
    · exact hr
    all_goals norm_num
  | true =>
    apply PositiveChannel.weighted_bound _ (stateMass_ge_third true k true)
      (stateMass_le_two_thirds true k true)
      (fun f : Future (L+1) => firstAction f.1 = resetTo false)
      (q := 2/3) (r := 1/6)
    · exact hr
    · exact hq
    all_goals norm_num

end PomdpLogging
