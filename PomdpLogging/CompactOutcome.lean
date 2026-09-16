import PomdpLogging.FirstReset
import PomdpLogging.SufficientChannel
import PomdpLogging.WeightedRevealing

noncomputable section
open scoped BigOperators
namespace PomdpLogging

def resetResidual {L : ℕ} (f : Future L) (t : ℕ) (r : Bool) : ℝ :=
  (futureLaw false .fresh L).mass f / resetPrefixProbability .fresh t r

theorem future_firstReset_factor (s : Bool) (m : Memory) {L : ℕ}
    (f : Future L) (t : ℕ) (r : Bool) (he : earliestReset f.1 = some (t,r)) :
    (futureLaw s m L).mass f = resetPrefixProbability m t r * resetResidual f t r := by
  have hn : earliestReset f.1 ≠ none := by rw [he]; simp
  have hc := continuation_firstReset_factor m f.1 t r he
  have hp := (resetPrefixProbability_pos .fresh t r).ne'
  change continuationMass m f.1 * emission (runState s f.1) f.2 =
    resetPrefixProbability m t r *
      ((continuationMass .fresh f.1 * emission (runState false f.1) f.2) /
        resetPrefixProbability .fresh t r)
  rw [runState_after_reset s false f.1 hn]
  field_simp
  nlinarith [congrArg (fun x : ℝ => x * emission (runState false f.1) f.2) hc]

def compactResetEntry (θ : Bool) (k t : ℕ) (r s : Bool) : ℝ :=
  (survival k * (if s = θ then resetPrefixProbability .fresh t r else 0) +
    (1-survival k)/2 * (if s = false then resetPrefixProbability .zero t r else 0) +
    (1-survival k)/2 * (if s = true then resetPrefixProbability .one t r else 0)) / stateMass θ k s

theorem outcome_firstReset_factor (θ : Bool) (k : ℕ) {L : ℕ}
    (f : Future L) (t : ℕ) (r : Bool) (he : earliestReset f.1 = some (t,r)) (s : Bool) :
    outcome θ k L f s = compactResetEntry θ k t r s * resetResidual f t r := by
  rw [outcome_memory_formula,
    future_firstReset_factor θ .fresh f t r he,
    future_firstReset_factor false .zero f t r he,
    future_firstReset_factor true .one f t r he]
  unfold compactResetEntry
  split_ifs <;> ring

def compactKey {L : ℕ} (f : Future L) : Sum (ℕ × Bool) Bool :=
  match earliestReset f.1 with
  | none => .inr f.2
  | some tr => .inl tr

theorem compactKey_cross (θ : Bool) (k L : ℕ) (f g : Future L)
    (he : compactKey f = compactKey g) (s : Bool) :
    outcome θ k L f s * outcome θ k L g false =
      outcome θ k L f false * outcome θ k L g s := by
  cases hf : earliestReset f.1 with
  | none =>
    cases hg : earliestReset g.1 with
    | none =>
      have hy : f.2 = g.2 := by simpa [compactKey, hf, hg] using he
      have hh : f.1 = g.1 :=
        ((earliestReset_none_iff f.1).mp hf).trans ((earliestReset_none_iff g.1).mp hg).symm
      have hfg : f = g := Prod.ext hh hy
      subst g
      ring
    | some tr => simp [compactKey, hf, hg] at he
  | some tr =>
    cases hg : earliestReset g.1 with
    | none => simp [compactKey, hf, hg] at he
    | some tr' =>
      have htr : tr = tr' := by simpa [compactKey, hf, hg] using he
      subst tr'
      rcases tr with ⟨t,r⟩
      rw [outcome_firstReset_factor θ k f t r hf s,
        outcome_firstReset_factor θ k g t r hg false,
        outcome_firstReset_factor θ k f t r hf false,
        outcome_firstReset_factor θ k g t r hg s]
      ring

def compactKeys (L : ℕ) : Finset (Sum (ℕ × Bool) Bool) :=
  Finset.univ.image (compactKey (L := L))

abbrev CompactOutcome (L : ℕ) := ↥(compactKeys L)

def compactFuture {L : ℕ} (f : Future L) : CompactOutcome L :=
  ⟨compactKey f, Finset.mem_image.mpr ⟨f, Finset.mem_univ f, rfl⟩⟩

theorem compactFuture_surjective (L : ℕ) : Function.Surjective (compactFuture (L := L)) := by
  intro z
  obtain ⟨f, _, hf⟩ := Finset.mem_image.mp z.property
  exact ⟨f, Subtype.ext hf⟩

def compactChannel (θ : Bool) (k L : ℕ) : PositiveChannel (CompactOutcome L) :=
  (actualChannel θ k L).coarse compactFuture (compactFuture_surjective L)

def compactKernel (θ : Bool) (k L : ℕ) : CompactOutcome L → Law (Future L) :=
  (actualChannel θ k L).fiberKernel compactFuture (compactFuture_surjective L)

theorem compact_channel_cross (θ : Bool) (k L : ℕ) (f g : Future L)
    (he : compactFuture f = compactFuture g) (s : Bool) :
    (actualChannel θ k L).entry f s * (actualChannel θ k L).entry g false =
      (actualChannel θ k L).entry f false * (actualChannel θ k L).entry g s :=
  compactKey_cross θ k L f g (congrArg Subtype.val he) s

/-- The actual first-reset/no-reset-terminal-bit statistic has a common
reconstruction kernel for both physical-state columns in a fixed model. -/
theorem compact_reconstruction_factor (θ : Bool) (k L : ℕ) (f : Future L) (s : Bool) :
    outcome θ k L f s = (compactKernel θ k L (compactFuture f)).mass f *
      (compactChannel θ k L).entry (compactFuture f) s :=
  (actualChannel θ k L).sufficient_reconstruction_factor compactFuture
    (compactFuture_surjective L) (compact_channel_cross θ k L) f s

/-- Proposition D.1: exact preservation of both revealing matrices. -/
theorem compact_preserves_grams (θ : Bool) (k L : ℕ) :
    (actualChannel θ k L).gram = (compactChannel θ k L).gram ∧
      (actualChannel θ k L).weightedGram (stateMass θ k true) =
        (compactChannel θ k L).weightedGram (stateMass θ k true) := by
  constructor
  · exact (actualChannel θ k L).sufficient_gram compactFuture
      (compactFuture_surjective L) (compact_channel_cross θ k L)
  · exact (actualChannel θ k L).sufficient_weightedGram compactFuture
      (compactFuture_surjective L) (compact_channel_cross θ k L)
      (by linarith [stateMass_ge_third θ k true])
      (by linarith [stateMass_le_two_thirds θ k true])

end PomdpLogging
