import PomdpLogging.CompactOutcome

noncomputable section
open scoped BigOperators
namespace PomdpLogging

theorem earliestReset_append_some {n L : ℕ} (h : History n) (f : History L)
    (t : ℕ) (r : Bool) (he : earliestReset h = some (t,r)) :
    earliestReset (appendHistory h f) = some (t,r) := by
  induction L with
  | zero => exact he
  | succ L ih =>
    rcases f with ⟨f,a⟩
    simp [appendHistory, earliestReset, ih f]

theorem earliestReset_at (t : ℕ) (r : Bool) :
    earliestReset (L := t+1) (allHold t,resetTo r) = some (t,r) := by
  cases r <;> simp [earliestReset, earliestReset_allHold, resetTo]

theorem compactKey_attains_reset {L t : ℕ} (ht : t < L) (r : Bool) :
    ∃ f : Future L, compactKey f = Sum.inl (t,r) := by
  obtain ⟨l, hl⟩ : ∃ l, L = t+1+l := ⟨L-(t+1), by omega⟩
  subst L
  let h := appendHistory (n := t+1) (allHold t,resetTo r) (allHold l)
  have he : earliestReset h = some (t,r) :=
    earliestReset_append_some _ _ t r (earliestReset_at t r)
  exact ⟨(h,false), by simp [compactKey, he]⟩

theorem compactKeys_formula (L : ℕ) :
    compactKeys L = ((Finset.range L).product (Finset.univ : Finset Bool)).disjSum Finset.univ := by
  ext z
  constructor
  · intro hz
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hz
    cases he : earliestReset f.1 with
    | none => simp [compactKey, he]
    | some tr =>
      rcases tr with ⟨t,r⟩
      simpa [compactKey, he] using earliestReset_lt f.1 t r he
  · intro hz
    cases z with
    | inl tr =>
      rcases tr with ⟨t,r⟩
      have ht : t < L := by simpa using hz
      obtain ⟨f, hf⟩ := compactKey_attains_reset ht r
      exact Finset.mem_image.mpr ⟨f, Finset.mem_univ f, hf⟩
    | inr y =>
      exact Finset.mem_image.mpr ⟨(allHold L,y), Finset.mem_univ _,
        by simp [compactKey, earliestReset_allHold]⟩

/-- The compact outcome alphabet has exactly the claimed 2L+2 symbols. -/
theorem compact_cardinality (L : ℕ) : Fintype.card (CompactOutcome L) = 2*L+2 := by
  rw [Fintype.card_coe, compactKeys_formula, Finset.card_disjSum]
  change ((Finset.range L ×ˢ (Finset.univ : Finset Bool)).card +
    (Finset.univ : Finset Bool).card) = _
  rw [Finset.card_product]
  simp [Nat.mul_comm]

end PomdpLogging
