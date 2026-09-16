import PomdpLogging.MemoryDistribution

noncomputable section
open scoped BigOperators

namespace PomdpLogging

/-- Physical states obtained by applying the paper's first transition and then
its common later transitions, without using the logger-memory shortcut. -/
def bitAfter (θ : Bool) : {k : ℕ} → History (k+1) → Bool
  | 0, (_,a) => transition θ a
  | _+1, (h,a) => transition (bitAfter θ h) a

theorem bitAfter_eq_stateOf (θ : Bool) {k : ℕ} (h : History (k+1)) :
    bitAfter θ h = stateOf θ (memory h) := by
  induction k with
  | zero =>
    rcases h with ⟨h,a⟩
    cases a <;> rfl
  | succ k ih =>
    rcases h with ⟨h,a⟩
    simp only [bitAfter, memory, stateOf_update, ih]

theorem target_bit (θ : Bool) (k : ℕ) : bitAfter θ (allHold (k+1)) = θ := by
  rw [bitAfter_eq_stateOf, memory_allHold]
  rfl

def targetValue (θ : Bool) : ℝ := (emissionLaw θ).expect (fun y => if y then 1 else 0)

theorem targetValue_zero : targetValue false = 1/4 := by
  norm_num [targetValue, emissionLaw, emission, Law.expect]

theorem targetValue_one : targetValue true = 3/4 := by
  norm_num [targetValue, emissionLaw, emission, Law.expect]

abbrev Episode (k : ℕ) := History (k+1) × Bool

def episodeLaw (θ : Bool) (k : ℕ) : Law (Episode k) where
  mass hy := historyMass hy.1 * emission (bitAfter θ hy.1) hy.2
  nonneg hy := le_of_lt (mul_pos (historyMass_pos hy.1) (emission_pos _ _))
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, emission_total, mul_one]
    exact historyMass_total (k+1)

theorem episode_mass_pos (θ : Bool) (k : ℕ) (e : Episode k) :
    0 < (episodeLaw θ k).mass e := mul_pos (historyMass_pos e.1) (emission_pos _ _)

theorem reset_erases_bit {k : ℕ} (h : History (k+1)) (hr : h ≠ allHold (k+1)) :
    bitAfter false h = bitAfter true h := by
  rw [bitAfter_eq_stateOf, bitAfter_eq_stateOf]
  have hm : memory h ≠ .fresh := fun he => hr ((memory_fresh_iff h).mp he)
  cases he : memory h with
  | fresh => exact False.elim (hm he)
  | zero => rfl
  | one => rfl

theorem reset_episode_likelihood_equal {k : ℕ} (e : Episode k)
    (hr : e.1 ≠ allHold (k+1)) :
    (episodeLaw false k).mass e = (episodeLaw true k).mass e := by
  simp only [episodeLaw, reset_erases_bit e.1 hr]

theorem allHold_episode_mass (θ : Bool) (k : ℕ) (y : Bool) :
    (episodeLaw θ k).mass (allHold (k+1), y) = survival k * emission θ y := by
  simp only [episodeLaw, allHold_mass, target_bit]

def finalActionLaw : Law Action where
  mass _ := 1/3
  nonneg _ := by norm_num
  total := by rw [sum_action]; norm_num

/-- The final action is included explicitly, as in the submitted data protocol. -/
def fullEpisodeLaw (θ : Bool) (k : ℕ) : Law (Episode k × Action) :=
  (episodeLaw θ k).prod finalActionLaw

theorem full_episode_mass_pos (θ : Bool) (k : ℕ) (e : Episode k × Action) :
    0 < (fullEpisodeLaw θ k).mass e := by
  change 0 < (episodeLaw θ k).mass e.1 * (1/3)
  exact mul_pos (episode_mass_pos θ k e.1) (by norm_num)

end PomdpLogging
