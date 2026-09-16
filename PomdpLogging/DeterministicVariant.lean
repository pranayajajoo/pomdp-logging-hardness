import PomdpLogging.ModelSemantics
import PomdpLogging.OptimalTesting
import PomdpLogging.FullDataLowerBound
import PomdpLogging.ProductInformation

noncomputable section
open scoped BigOperators
namespace PomdpLogging

def deterministicEpisodeLaw (θ : Bool) (k : ℕ) : Law (Episode k) where
  mass hy := historyMass hy.1 * (if hy.2 = bitAfter θ hy.1 then 1 else 0)
  nonneg hy := mul_nonneg (historyMass_pos hy.1).le (by split_ifs <;> norm_num)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum]
    simp
    exact historyMass_total (k+1)

def deterministicFullLaw (θ : Bool) (k : ℕ) : Law (Episode k × Action) :=
  (deterministicEpisodeLaw θ k).prod finalActionLaw

def deterministicModel (θ : Bool) : BinaryLayeredModel :=
  { candidateModel θ with terminalEmission := fun s => Law.pure s }

theorem deterministic_state_given_actions (θ : Bool) {k : ℕ} (h : History (k+1)) :
    (deterministicModel θ).stateGivenActions h = Law.pure (bitAfter θ h) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases h with ⟨h,a⟩
    change ((deterministicModel θ).stateGivenActions h).bind _ = _
    rw [ih, Law.pure_bind]
    rfl

theorem deterministic_model_law (θ : Bool) (k : ℕ) :
    (deterministicModel θ).loggedDataLaw k = deterministicFullLaw θ k := by
  unfold BinaryLayeredModel.loggedDataLaw deterministicFullLaw
  congr 1
  ext hy
  simp only [BinaryLayeredModel.observableLaw, BinaryLayeredModel.observationGivenActions,
    deterministic_state_given_actions, Law.pure_bind]
  simp [deterministicModel, Law.pure, deterministicEpisodeLaw, eq_comm]

theorem deterministic_target_return (θ : Bool) (k : ℕ) :
    (deterministicModel θ).targetReturn k = if θ then 1 else 0 := by
  unfold BinaryLayeredModel.targetReturn BinaryLayeredModel.observationGivenActions
  rw [deterministic_state_given_actions, Law.pure_bind, target_bit]
  change (Law.pure θ).expect terminalReturn = _
  rw [Law.expect_pure]
  rfl

theorem erasedWeight_history {k : ℕ} (e : Episode k × Action) :
    erasedWeight e = if e.1.1 = allHold (k+1) then 0 else 1 := by
  by_cases hh : e.1.1 = allHold (k+1)
  · cases hy : e.1.2 <;> simp [erasedWeight, compressFull, compress, hh, hy]
  · simp [erasedWeight, compressFull, compress, hh]

theorem deterministic_erased_equal {k : ℕ} (e : Episode k × Action)
    (hh : e.1.1 ≠ allHold (k+1)) :
    (deterministicFullLaw false k).mass e = (deterministicFullLaw true k).mass e := by
  simp only [deterministicFullLaw, Law.prod, deterministicEpisodeLaw,
    reset_erases_bit e.1.1 hh]

theorem deterministic_erased_expect (θ : Bool) (k : ℕ) :
    (deterministicFullLaw θ k).expect erasedWeight = 1-survival k := by
  unfold deterministicFullLaw
  rw [Law.expect_prod]
  simp_rw [erasedWeight_history]
  have he (a : Episode k) :
      finalActionLaw.expect (fun _ : Action => if a.1 = allHold (k+1) then (0 : ℝ) else 1) =
        if a.1 = allHold (k+1) then 0 else 1 := Law.expect_const _ _
  simp_rw [he]
  change (∑ hy : History (k+1) × Bool,
    (historyMass hy.1*(if hy.2 = bitAfter θ hy.1 then 1 else 0)) *
      (if hy.1 = allHold (k+1) then 0 else 1)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp
  have hh := Law.expect_ite_eq (historyLaw (k+1)) (allHold (k+1)) (0 : ℝ) 1
  simpa [Law.expect, historyLaw, allHold_mass, mul_ite] using hh

def deterministicFlip {k : ℕ} (e : Episode k × Action) : Episode k × Action :=
  ((e.1.1, if e.1.1 = allHold (k+1) then !e.1.2 else e.1.2),e.2)

theorem deterministicFlip_involutive {k : ℕ} (e : Episode k × Action) :
    deterministicFlip (deterministicFlip e) = e := by
  rcases e with ⟨⟨h,y⟩,a⟩
  by_cases hh : h = allHold (k+1) <;> simp [deterministicFlip, hh]

def deterministicDatasetFlip (k n : ℕ) :
    (Fin n → Episode k × Action) ≃ (Fin n → Episode k × Action) where
  toFun xs i := deterministicFlip (xs i)
  invFun xs i := deterministicFlip (xs i)
  left_inv xs := funext (fun i => deterministicFlip_involutive (xs i))
  right_inv xs := funext (fun i => deterministicFlip_involutive (xs i))

theorem deterministic_flip_mass (θ : Bool) (k : ℕ) (e : Episode k × Action) :
    (deterministicFullLaw θ k).mass (deterministicFlip e) =
      (deterministicFullLaw (!θ) k).mass e := by
  rcases e with ⟨⟨h,y⟩,a⟩
  by_cases hh : h = allHold (k+1)
  · subst h
    cases θ <;> cases y <;>
      simp [deterministicFullLaw, Law.prod, deterministicEpisodeLaw, deterministicFlip, target_bit]
  · cases θ <;>
      simp [deterministicFlip, hh, deterministicFullLaw, Law.prod, deterministicEpisodeLaw,
        reset_erases_bit h hh]

theorem deterministic_dataset_flip_mass (θ : Bool) (k n : ℕ)
    (xs : Fin n → Episode k × Action) :
    ((deterministicFullLaw θ k).iid n).mass (deterministicDatasetFlip k n xs) =
      ((deterministicFullLaw (!θ) k).iid n).mass xs := by
  change (∏ i, (deterministicFullLaw θ k).mass (deterministicFlip (xs i))) = _
  simp_rw [deterministic_flip_mass]
  rfl

end PomdpLogging
