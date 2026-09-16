import PomdpLogging.ThreeSymbol

noncomputable section
open scoped BigOperators

namespace PomdpLogging

theorem Law.fiber_mass {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : Law α) (f : α → β) (b : β) :
    (∑ a, if f a = b then P.mass a else 0) = (P.map f).mass b := by
  classical
  rw [Law.map_mass]
  unfold Law.expect
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a = b
  · simp [h]
  · simp [h, Ne.symm h]

def Law.onFiber {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : Law α) (f : α → β) (b : β) (hb : 0 < (P.map f).mass b) : Law α where
  mass a := if f a = b then P.mass a / (P.map f).mass b else 0
  nonneg a := by split_ifs; exact div_nonneg (P.nonneg a) hb.le; rfl
  total := by
    have he : (∑ a, if f a = b then P.mass a / (P.map f).mass b else 0) =
        (∑ a, if f a = b then P.mass a else 0) / (P.map f).mass b := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    rw [he, P.fiber_mass f b, div_self hb.ne']

theorem symbol_mass_pos (θ : Bool) (k : ℕ) (w : Symbol) :
    0 < (symbolLaw θ k).mass w := by
  have hp := survival_pos k
  have hu := survival_le_third k
  cases w with
  | erased => change 0 < 1-survival k; linarith
  | zero => exact mul_pos hp (emission_pos _ _)
  | one => exact mul_pos hp (emission_pos _ _)

/-- A single kernel, defined using candidate zero, reconstructs both candidates. -/
def reconstruction (k : ℕ) (w : Symbol) : Law (Episode k × Action) :=
  (fullEpisodeLaw false k).onFiber compressFull w (by
    rw [full_actual_symbol_law]
    exact symbol_mass_pos false k w)

theorem reconstruction_mass (k : ℕ) (w : Symbol) (e : Episode k × Action) :
    (reconstruction k w).mass e = if compressFull e = w then
      (fullEpisodeLaw false k).mass e / (symbolLaw false k).mass w else 0 := by
  simp only [reconstruction, Law.onFiber, full_actual_symbol_law]

theorem likelihood_cross (θ : Bool) (k : ℕ) (e : Episode k × Action) :
    (fullEpisodeLaw θ k).mass e * (symbolLaw false k).mass (compressFull e) =
      (fullEpisodeLaw false k).mass e * (symbolLaw θ k).mass (compressFull e) := by
  cases θ with
  | false => rfl
  | true =>
    rcases e with ⟨⟨h,y⟩,a⟩
    by_cases hh : h = allHold (k+1)
    · subst h
      cases y <;>
        simp [fullEpisodeLaw, Law.prod, allHold_episode_mass, compressFull, compress,
          symbolLaw, symbolMass] <;> ring
    · simp only [fullEpisodeLaw, Law.prod]
      rw [reset_episode_likelihood_equal (h,y) hh]
      simp [compressFull, compress, hh, symbolLaw, symbolMass]

theorem reconstruction_factor (θ : Bool) (k : ℕ) (e : Episode k × Action) :
    (fullEpisodeLaw θ k).mass e =
      (symbolLaw θ k).mass (compressFull e) * (reconstruction k (compressFull e)).mass e := by
  rw [reconstruction_mass, if_pos rfl, ← mul_div_assoc]
  apply (eq_div_iff (symbol_mass_pos false k (compressFull e)).ne').mpr
  simpa [mul_comm] using likelihood_cross θ k e

/-- The reverse distributional identity in Proposition 5.1, for each model,
using the same explicitly defined reconstruction kernel. -/
theorem reconstructs_full_law (θ : Bool) (k : ℕ) :
    (symbolLaw θ k).bind (reconstruction k) = fullEpisodeLaw θ k := by
  ext e
  change (∑ w, (symbolLaw θ k).mass w * (reconstruction k w).mass e) = _
  simp_rw [reconstruction_mass, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simpa [reconstruction_mass] using (reconstruction_factor θ k e).symm

end PomdpLogging
