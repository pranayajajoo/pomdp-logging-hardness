import PomdpLogging.Episodes

noncomputable section
open scoped BigOperators

namespace PomdpLogging

inductive Symbol where
  | erased | zero | one
  deriving DecidableEq, Repr

instance : Fintype Symbol := ⟨{.erased, .zero, .one}, by
  intro w
  cases w <;> simp⟩

theorem sum_symbol (f : Symbol → ℝ) :
    ∑ w, f w = f .erased + f .zero + f .one := by
  change (∑ w ∈ ({.erased, .zero, .one} : Finset Symbol), f w) = _
  simp [add_assoc]

def compress {k : ℕ} (e : Episode k) : Symbol :=
  if e.1 = allHold (k+1) then (if e.2 then .one else .zero) else .erased

def symbolMass (θ : Bool) (k : ℕ) : Symbol → ℝ
  | .erased => 1-survival k
  | .zero => survival k * emission θ false
  | .one => survival k * emission θ true

def symbolLaw (θ : Bool) (k : ℕ) : Law Symbol where
  mass := symbolMass θ k
  nonneg w := by
    have hp := survival_pos k
    have hb := survival_le_third k
    cases w with
    | erased => simp only [symbolMass]; linarith
    | zero => exact le_of_lt (mul_pos hp (emission_pos _ _))
    | one => exact le_of_lt (mul_pos hp (emission_pos _ _))
  total := by
    rw [sum_symbol]
    cases θ <;> norm_num [symbolMass, emission] <;> ring

theorem compression_expect (θ : Bool) (k : ℕ) (f : Symbol → ℝ) :
    (episodeLaw θ k).expect (fun e => f (compress e)) =
      (symbolLaw θ k).expect f := by
  classical
  have hi (h : History (k+1)) :
      (∑ y : Bool, emission (bitAfter θ h) y * f (compress (h,y))) =
        if h = allHold (k+1) then
          emission θ false * f .zero + emission θ true * f .one
        else f .erased := by
    by_cases h' : h = allHold (k+1)
    · subst h
      simp [compress, target_bit, add_comm]
    · simp only [compress, if_neg h', ← Finset.sum_mul, emission_total, one_mul]
  change (∑ hy : History (k+1) × Bool,
    (historyMass hy.1 * emission (bitAfter θ hy.1) hy.2) * f (compress hy)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← Finset.mul_sum, hi]
  change (historyLaw (k+1)).expect (fun h => if h = allHold (k+1) then
    emission θ false * f .zero + emission θ true * f .one else f .erased) = _
  rw [Law.expect_ite_eq]
  change historyMass (allHold (k+1)) * _ + _ = _
  rw [allHold_mass]
  simp only [Law.expect, sum_symbol, symbolLaw, symbolMass, historyLaw, allHold_mass]
  ring

theorem actual_symbol_law (θ : Bool) (k : ℕ) :
    (episodeLaw θ k).map compress = symbolLaw θ k := by
  classical
  ext w
  rw [Law.map_mass, compression_expect θ k (fun w' => if w = w' then 1 else 0)]
  simp [Law.expect]

def compressFull {k : ℕ} (e : Episode k × Action) : Symbol := compress e.1

theorem full_compression_expect (θ : Bool) (k : ℕ) (f : Symbol → ℝ) :
    (fullEpisodeLaw θ k).expect (fun e => f (compressFull e)) =
      (symbolLaw θ k).expect f := by
  simp only [fullEpisodeLaw, Law.expect_prod, compressFull, Law.expect_const]
  exact compression_expect θ k f

theorem full_actual_symbol_law (θ : Bool) (k : ℕ) :
    (fullEpisodeLaw θ k).map compressFull = symbolLaw θ k := by
  classical
  ext w
  rw [Law.map_mass, full_compression_expect θ k (fun w' => if w = w' then 1 else 0)]
  simp [Law.expect]

/-- An initial testing milestone. Transport to arbitrary full-data estimators
also requires the reverse reconstruction kernel, proved separately. -/
theorem reduced_experiment_lower (k n : ℕ) (T : Test (Fin n → Symbol)) :
    (1-survival k)^n / 2 ≤ T.worstError ((symbolLaw false k).iid n)
      ((symbolLaw true k).iid n) := by
  have h := T.common_atom_lower ((symbolLaw false k).iid n)
    ((symbolLaw true k).iid n) (fun _ => Symbol.erased) (by simp [Law.iid, symbolLaw, symbolMass])
  simpa [Law.iid, symbolLaw, symbolMass] using h

end PomdpLogging
