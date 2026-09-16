import PomdpLogging.DeterministicVariant

noncomputable section
open scoped BigOperators
namespace PomdpLogging

def deterministicSymbolMass (θ : Bool) (k : ℕ) : Symbol → ℝ
  | .erased => 1-survival k
  | .zero => if θ then 0 else survival k
  | .one => if θ then survival k else 0

def deterministicSymbolLaw (θ : Bool) (k : ℕ) : Law Symbol where
  mass := deterministicSymbolMass θ k
  nonneg w := by
    have hp := survival_pos k
    have hu := survival_le_third k
    cases w <;> cases θ <;> simp [deterministicSymbolMass] <;> linarith
  total := by rw [sum_symbol]; cases θ <;> simp [deterministicSymbolMass]

theorem deterministic_compression_expect (θ : Bool) (k : ℕ) (f : Symbol → ℝ) :
    (deterministicEpisodeLaw θ k).expect (fun e => f (compress e)) =
      (deterministicSymbolLaw θ k).expect f := by
  have hi (h : History (k+1)) :
      (∑ y : Bool, (if y = bitAfter θ h then (1 : ℝ) else 0) * f (compress (h,y))) =
        if h = allHold (k+1) then f (if θ then .one else .zero) else f .erased := by
    by_cases hh : h = allHold (k+1)
    · subst h
      cases θ <;> simp [compress, target_bit]
    · simp [compress, hh]
  change (∑ hy : History (k+1) × Bool,
    (historyMass hy.1*(if hy.2 = bitAfter θ hy.1 then 1 else 0))*f (compress hy)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← Finset.mul_sum, hi]
  change (historyLaw (k+1)).expect (fun h => if h = allHold (k+1) then
    f (if θ then .one else .zero) else f .erased) = _
  rw [Law.expect_ite_eq]
  cases θ <;> simp [Law.expect, sum_symbol, deterministicSymbolLaw,
    deterministicSymbolMass, historyLaw, allHold_mass, add_comm]

/-- The deterministic full-data experiment compresses to (1-p,p,0) or (1-p,0,p). -/
theorem deterministic_actual_symbol_law (θ : Bool) (k : ℕ) :
    (deterministicFullLaw θ k).map compressFull = deterministicSymbolLaw θ k := by
  ext w
  rw [Law.map_mass]
  unfold deterministicFullLaw
  rw [Law.expect_prod]
  change ((deterministicEpisodeLaw θ k).expect fun a =>
    finalActionLaw.expect (fun _ : Action => if w = compress a then (1 : ℝ) else 0)) = _
  simp only [Law.expect_const]
  rw [deterministic_compression_expect θ k (fun w' => if w = w' then 1 else 0)]
  simp [Law.expect]

end PomdpLogging
