import PartialMonad.CoroutineM.Join
import Std.Data.Sum.Basic

namespace CoroutineM

#check Sum.LiftRel

-- @[simp] theorem join_next_inl (x : CoroutineM (CoroutineM α)) (s) :
--     x.join.next (Sum.inl s) = .inl (x.next s) := by
--   sorry

def joinLawful' {α : Type u} (x : LawfulCoroutineM (CoroutineM α)) :
    LawfulCoroutineM (ULift.{u+1} α) :=
  Quotient.liftOn x (LawfulCoroutineM.ofCoroutine ∘ join) <| by
    intro a b ⟨R, bisim, state⟩
    apply Quotient.sound
    -- simp [join]
    let R' : (join _).σ → (join _).σ → Prop :=
      Sum.LiftRel
        (fun ⟨s₁, _⟩ ⟨s₂, _⟩ => R s₁ s₂)
        (fun ⟨_, s₁, _⟩ ⟨_, s₂, _⟩ => HEq s₁ s₂)
    refine ⟨R', ?_, ?_⟩
    · rintro (⟨s₁, hs₁⟩|⟨ht₁, s₁', next₁⟩) (⟨s₂, hs₂⟩|⟨ht₂, s₂', next₂⟩) (hR'|hR')
      · constructor
        simp at *
        have := bisim _ _ hR'
        split <;> split <;> simp_all <;> (cases this) <;> constructor
        next => assumption
        next inner ha hb =>
          simp only
          sorry
      · simp [join]
    · simpa [join, R'] using state

def joinLawful (x : CoroutineM (LawfulCoroutineM α)) : LawfulCoroutineM α :=
  sorry

end CoroutineM
