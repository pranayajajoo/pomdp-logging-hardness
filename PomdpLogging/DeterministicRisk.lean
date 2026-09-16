import PomdpLogging.DeterministicVariant

noncomputable section
open scoped BigOperators
namespace PomdpLogging

theorem deterministic_allHold_disjoint {k : ℕ} (e : Episode k × Action)
    (hh : e.1.1 = allHold (k+1)) :
    (deterministicFullLaw false k).mass e = 0 ∨ (deterministicFullLaw true k).mass e = 0 := by
  cases hy : e.1.2 <;>
    simp [deterministicFullLaw, Law.prod, deterministicEpisodeLaw, hh, hy, target_bit]

theorem deterministic_dataset_min_mass (k n : ℕ) (xs : Fin n → Episode k × Action) :
    min (((deterministicFullLaw false k).iid n).mass xs)
        (((deterministicFullLaw true k).iid n).mass xs) =
      ((deterministicFullLaw false k).iid n).mass xs * ∏ i, erasedWeight (xs i) := by
  classical
  by_cases hh : ∀ i, (xs i).1.1 ≠ allHold (k+1)
  · have hw : (∏ i, erasedWeight (xs i)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp [erasedWeight_history, hh i]
    have he : ((deterministicFullLaw false k).iid n).mass xs =
        ((deterministicFullLaw true k).iid n).mass xs := by
      change (∏ i, (deterministicFullLaw false k).mass (xs i)) = _
      apply Finset.prod_congr rfl
      intro i _
      exact deterministic_erased_equal (xs i) (hh i)
    rw [← he, min_self, hw, mul_one]
  · push_neg at hh
    obtain ⟨i, hi⟩ := hh
    have hw : (∏ j, erasedWeight (xs j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [erasedWeight_history, hi]
    rw [hw, mul_zero]
    rcases deterministic_allHold_disjoint (xs i) hi with h0 | h1
    · have hz : ((deterministicFullLaw false k).iid n).mass xs = 0 := by
        change (∏ j, (deterministicFullLaw false k).mass (xs j)) = 0
        exact Finset.prod_eq_zero (Finset.mem_univ i) h0
      rw [hz, min_eq_left (Law.nonneg _ _)]
    · have hz : ((deterministicFullLaw true k).iid n).mass xs = 0 := by
        change (∏ j, (deterministicFullLaw true k).mass (xs j)) = 0
        exact Finset.prod_eq_zero (Finset.mem_univ i) h1
      rw [hz, min_eq_right (Law.nonneg _ _)]

theorem deterministic_overlap_risk (k n : ℕ) :
    overlapRisk ((deterministicFullLaw false k).iid n) ((deterministicFullLaw true k).iid n) =
      (1-survival k)^n/2 := by
  unfold overlapRisk
  simp_rw [deterministic_dataset_min_mass]
  change ((deterministicFullLaw false k).iid n).expect (fun xs => ∏ i, erasedWeight (xs i))/2 = _
  rw [Law.iid_expect_product, deterministic_erased_expect]

theorem deterministic_likelihood_balanced (k n : ℕ) :
    (likelihoodTest ((deterministicFullLaw false k).iid n)
      ((deterministicFullLaw true k).iid n)).errorZero ((deterministicFullLaw false k).iid n) =
    (likelihoodTest ((deterministicFullLaw false k).iid n)
      ((deterministicFullLaw true k).iid n)).errorOne ((deterministicFullLaw true k).iid n) :=
  likelihood_balanced _ _ (deterministicDatasetFlip k n)
    (deterministic_dataset_flip_mass false k n) (deterministic_dataset_flip_mass true k n)

theorem deterministic_minimax_test (k n : ℕ) :
    (∀ T : Test (Fin n → Episode k × Action), (1-survival k)^n/2 ≤
      T.worstError ((deterministicFullLaw false k).iid n) ((deterministicFullLaw true k).iid n)) ∧
    (likelihoodTest ((deterministicFullLaw false k).iid n)
      ((deterministicFullLaw true k).iid n)).worstError
      ((deterministicFullLaw false k).iid n) ((deterministicFullLaw true k).iid n) =
        (1-survival k)^n/2 := by
  constructor
  · intro T
    rw [← deterministic_overlap_risk]
    exact T.overlap_lower _ _
  · rw [(balanced_likelihood_risk _ _ (deterministic_likelihood_balanced k n)).2.2,
      deterministic_overlap_risk]

def Law.totalVariation {α : Type*} [Fintype α] (P Q : Law α) : ℝ :=
  (∑ x, |P.mass x-Q.mass x|)/2

theorem Law.totalVariation_overlap {α : Type*} [Fintype α] (P Q : Law α) :
    P.totalVariation Q = 1-2*overlapRisk P Q := by
  have he (x : α) : |P.mass x-Q.mass x| = P.mass x+Q.mass x-2*min (P.mass x) (Q.mass x) := by
    rcases le_total (P.mass x) (Q.mass x) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]; ring
    · rw [abs_of_nonneg (sub_nonneg.mpr h), min_eq_right h]; ring
  unfold totalVariation overlapRisk
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, P.total, Q.total]
  ring

/-- Appendix E's exact total variation formula for the full recorded data. -/
theorem deterministic_totalVariation (k n : ℕ) :
    ((deterministicFullLaw false k).iid n).totalVariation ((deterministicFullLaw true k).iid n) =
      1-(1-survival k)^n := by
  rw [Law.totalVariation_overlap, deterministic_overlap_risk]
  ring

end PomdpLogging
