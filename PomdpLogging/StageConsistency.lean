import PomdpLogging.OutcomeProbability

noncomputable section
open scoped BigOperators
namespace PomdpLogging

/-- Splitting and concatenating action records is a bijection, at every length. -/
def historyJoinEquiv (n : ℕ) : (L : ℕ) → (History n × History L) ≃ History (n+L)
  | 0 => {
      toFun x := x.1
      invFun h := (h, ())
      left_inv x := by rcases x with ⟨h, u⟩; cases u; rfl
      right_inv _ := rfl }
  | L+1 => (Equiv.prodAssoc (History n) (History L) Action).symm.trans
      (Equiv.prodCongr (historyJoinEquiv n L) (Equiv.refl Action))

theorem historyJoinEquiv_apply (n L : ℕ) (h : History n) (f : History L) :
    historyJoinEquiv n L (h,f) = appendHistory h f := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rcases f with ⟨f,a⟩
    change (historyJoinEquiv n L (h,f),a) = (appendHistory h f,a)
    rw [ih]

def recordLaw (θ : Bool) (n : ℕ) : Law (History n × Bool) where
  mass hy := historyMass hy.1 * emission (stateOf θ (memory hy.1)) hy.2
  nonneg hy := mul_nonneg (historyMass_pos hy.1).le (emission_pos _ _).le
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, emission_total, mul_one]
    exact historyMass_total n

theorem recordLaw_eq_episodeLaw (θ : Bool) (k : ℕ) : recordLaw θ (k+1) = episodeLaw θ k := by
  ext hy
  simp only [recordLaw, episodeLaw, bitAfter_eq_stateOf]

def stageJoinEquiv (k L : ℕ) :
    (History (k+1) × Future L) ≃ (History (k+1+L) × Bool) :=
  (Equiv.prodAssoc (History (k+1)) (History L) Bool).symm.trans
    (Equiv.prodCongr (historyJoinEquiv (k+1) L) (Equiv.refl Bool))

theorem stageJoinEquiv_apply (k L : ℕ) (hf : History (k+1) × Future L) :
    stageJoinEquiv k L hf = (appendHistory hf.1 hf.2.1, hf.2.2) := by
  change (historyJoinEquiv (k+1) L (hf.1,hf.2.1),hf.2.2) = _
  rw [historyJoinEquiv_apply]

theorem stage_joint_mass (θ : Bool) (k L : ℕ) (hf : History (k+1) × Future L) :
    (recordLaw θ (k+1+L)).mass (stageJoinEquiv k L hf) =
      (prefixFutureLaw θ k L).mass hf := by
  rw [stageJoinEquiv_apply]
  simp only [recordLaw, prefixFutureLaw, futureLaw, bitAfter_eq_stateOf]
  rw [historyMass_append (by omega), memory_append, stateOf_runMemory]
  ring

theorem Law.map_equiv_mass {α β : Type*} [Fintype α] [Fintype β]
    (P : Law α) (e : α ≃ β) (a : α) : (P.map e).mass (e a) = P.mass a := by
  classical
  rw [Law.map_mass]
  simp only [e.injective.eq_iff]
  simp [Law.expect]

/-- Every stagewise joint distribution used in revealing is a reindexing of
the same full episode generator, with a positive-length action prefix. -/
theorem stage_joint_consistency (θ : Bool) (k L : ℕ) :
    (prefixFutureLaw θ k L).map (stageJoinEquiv k L) = recordLaw θ (k+1+L) := by
  ext z
  obtain ⟨hf, rfl⟩ := (stageJoinEquiv k L).surjective z
  rw [Law.map_equiv_mass]
  exact (stage_joint_mass θ k L hf).symm

end PomdpLogging
