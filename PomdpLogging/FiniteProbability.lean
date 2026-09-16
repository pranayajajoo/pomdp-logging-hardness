import Mathlib

/-!
Finite probability distributions written with real masses. Nonnegativity and
normalization are fields with proofs; this representation makes all subsequent
conditionals finite sums. It imposes no rationality restriction on probabilities.
-/

noncomputable section
open scoped BigOperators

namespace PomdpLogging

structure Law (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace Law

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[ext] theorem ext {P Q : Law α} (h : ∀ a, P.mass a = Q.mass a) : P = Q := by
  cases P
  cases Q
  simp_all only [mk.injEq]
  exact funext h

def expect (P : Law α) (f : α → ℝ) : ℝ := ∑ a, P.mass a * f a

@[simp] theorem expect_const (P : Law α) (c : ℝ) : P.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, P.total]

theorem expect_nonneg (P : Law α) {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ P.expect f := Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (hf a))

theorem expect_mono (P : Law α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    P.expect f ≤ P.expect g :=
  Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) (P.nonneg a))

theorem expect_add (P : Law α) (f g : α → ℝ) :
    P.expect (fun a => f a + g a) = P.expect f + P.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

def pure (a : α) : Law α := by
  classical
  exact ⟨fun b => if b = a then 1 else 0, by intro b; split_ifs <;> norm_num, by simp⟩

def bind (P : Law α) (K : α → Law β) : Law β where
  mass b := ∑ a, P.mass a * (K a).mass b
  nonneg b := Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) ((K a).nonneg b))
  total := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (K _).total, mul_one]
    exact P.total

def map (P : Law α) (f : α → β) : Law β := P.bind (fun a => pure (f a))

theorem map_mass [DecidableEq β] (P : Law α) (f : α → β) (b : β) :
    (P.map f).mass b = P.expect (fun a => if b = f a then 1 else 0) := by
  classical
  simp [map, bind, pure, expect]

theorem expect_bind (P : Law α) (K : α → Law β) (f : β → ℝ) :
    (P.bind K).expect f = P.expect (fun a => (K a).expect f) := by
  simp only [expect, bind, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

@[simp] theorem expect_pure (a : α) (f : α → ℝ) : (pure a).expect f = f a := by
  classical
  simp [pure, expect]

@[simp] theorem expect_map (P : Law α) (f : α → β) (g : β → ℝ) :
    (P.map f).expect g = P.expect (fun a => g (f a)) := by
  simp [map, expect_bind]

def prod (P : Law α) (Q : Law β) : Law (α × β) where
  mass ab := P.mass ab.1 * Q.mass ab.2
  nonneg ab := mul_nonneg (P.nonneg ab.1) (Q.nonneg ab.2)
  total := by
    simp [Fintype.sum_prod_type, ← Finset.mul_sum, Q.total, P.total]

theorem expect_prod (P : Law α) (Q : Law β) (f : α × β → ℝ) :
    (P.prod Q).expect f = P.expect (fun a => Q.expect (fun b => f (a,b))) := by
  simp only [expect, prod, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem expect_ite_eq [DecidableEq α] (P : Law α) (a : α) (u v : ℝ) :
    P.expect (fun b => if b = a then u else v) = P.mass a * u + (1-P.mass a) * v := by
  classical
  have he : P.expect (fun b => if b = a then u else v) =
      (∑ b, if b = a then P.mass b * (u-v) else 0) + P.expect (fun _ => v) := by
    unfold expect
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : b = a <;> simp [h] <;> ring
  rw [he]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, expect_const]
  ring

def iid (P : Law α) (n : ℕ) : Law (Fin n → α) where
  mass xs := ∏ i, P.mass (xs i)
  nonneg xs := Finset.prod_nonneg (fun i _ => P.nonneg (xs i))
  total := by
    rw [← Fintype.prod_sum]
    simp [P.total]

@[simp] theorem iid_const_mass (P : Law α) (n : ℕ) (a : α) :
    (P.iid n).mass (fun _ => a) = P.mass a ^ n := by
  simp [iid]

theorem mass_le_one (P : Law α) (a : α) : P.mass a ≤ 1 := by
  rw [← P.total]
  exact Finset.single_le_sum (fun b _ => P.nonneg b) (Finset.mem_univ a)

end Law

/-- A randomized binary test, represented by its conditional probability of
returning model one. This permits arbitrary real-valued randomization. -/
structure Test (α : Type*) where
  one : α → ℝ
  nonneg : ∀ a, 0 ≤ one a
  le_one : ∀ a, one a ≤ 1

namespace Test

variable {α : Type*} [Fintype α]

def errorZero (T : Test α) (P : Law α) : ℝ := P.expect T.one
def errorOne (T : Test α) (Q : Law α) : ℝ := Q.expect (fun a => 1 - T.one a)
def worstError (T : Test α) (P Q : Law α) : ℝ := max (T.errorZero P) (T.errorOne Q)

omit [Fintype α] in
theorem min_le_pointwise_error (T : Test α) (p q : ℝ) (a : α) :
    min p q ≤ p * T.one a + q * (1 - T.one a) := by
  rcases le_total p q with h | h
  · rw [min_eq_left h]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (T.le_one a))]
  · rw [min_eq_right h]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (T.nonneg a)]

theorem overlap_lower (T : Test α) (P Q : Law α) :
    (∑ a, min (P.mass a) (Q.mass a)) / 2 ≤ T.worstError P Q := by
  have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
    T.min_le_pointwise_error (P.mass a) (Q.mass a) a)
  rw [Finset.sum_add_distrib] at h
  change (∑ a, min (P.mass a) (Q.mass a)) ≤ T.errorZero P + T.errorOne Q at h
  have h₀ : T.errorZero P ≤ T.worstError P Q := le_max_left _ _
  have h₁ : T.errorOne Q ≤ T.worstError P Q := le_max_right _ _
  linarith

/-- One common atom already forces error; used for the all-erasure data set. -/
theorem common_atom_lower (T : Test α) (P Q : Law α) (a : α)
    (h : P.mass a = Q.mass a) : P.mass a / 2 ≤ T.worstError P Q := by
  have hs : min (P.mass a) (Q.mass a) ≤ ∑ b, min (P.mass b) (Q.mass b) :=
    Finset.single_le_sum (fun b _ => le_min (P.nonneg b) (Q.nonneg b))
      (Finset.mem_univ a)
  rw [← h, min_self] at hs
  linarith [T.overlap_lower P Q]

end Test
end PomdpLogging
