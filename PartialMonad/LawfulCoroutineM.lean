import PartialMonad.CoroutineM
import PartialMonad.CoroutineM.Bisim
import PartialMonad.CoroutineM.Run

import Mathlib.Data.Quot

/-!
This file defines the `LawfulCoroutineM` monad.

As the name suggests, this is a lawful version of `CoroutineM`, it is constructed by quotienting
coroutines through the bisimilarity relation.
-/

def CoroutineM.bumpUniverse.{r,s} {α : Type s} (x : CoroutineM.{s} α) :
    CoroutineM.{max s r} (ULift.{r,s} α) where
  σ := ULift.{r} x.σ
  state := .up x.state
  next s := x.next s.down |>.map .up .up

def LawfulCoroutineM (α : Type u) := Quotient (CoroutineM.setoid α)

namespace LawfulCoroutineM

/-- `pure a` gives a trivial coroutine, which completes in a single step, yielding the value `a` -/
def pure (a : α) : LawfulCoroutineM α :=
  ⟦CoroutineM.pure a⟧

/-- `map f` applies a pure function `f` after the coroutine finishes -/
def map (f : α → β) : LawfulCoroutineM α → LawfulCoroutineM β :=
  Quotient.lift (⟦CoroutineM.map f ·⟧) <| by
    intro a b ⟨R, R_is_bisim, R_state⟩
    apply Quotient.sound
    simp [CoroutineM.map]
    refine ⟨R, ?_, R_state⟩
    intro s₁ s₂ Rs
    simp only
    have := R_is_bisim _ _ Rs
    revert this
    cases a.next s₁ <;> cases b.next s₂ <;> rintro ⟨h_bisim⟩ <;> constructor
    exact h_bisim

instance : Functor (LawfulCoroutineM) := {map}

/-- Unwrap the VM representation of the `LawfulCoroutineM` quotient to access the underlying
`CoroutineM`. Computable, but unsound -/
unsafe def toCoroutineImpl : LawfulCoroutineM α → CoroutineM α :=
  Quot.unquot

@[implemented_by toCoroutineImpl]
-- ^^^ Is it OK to implement the `choose` version with the horibly unsound version?
--     The fact that mathlib has `Quotient.unquot` and `Quotient.out`, but does not do this
--     `implemented_by` trick makes me nervous there is something bad with it.
--     I checked with Sid, he says it should be fine
def toCoroutine : LawfulCoroutineM α → CoroutineM α :=
  Quotient.out

/-!
I was a bit worried that this would allow us to proof `False` using `native_decide`: by
defining two coroutine's which are distinct, but bisimilar, and then proving that
`toCoroutine ∘ ofCoroutine` yields the same result on both (using the fact that they are mapped
into the same equivalence class, and `choose` is deterministinc), but also somehow using
`native_decide` (which will use the `implented_by` version of `toCoroutine`) to show that the result
of `toCoroutine ∘ ofCoroutine` is different on both inputs (because the original coroutines are
distinct, and this operation is just a no-op in the VM).
But, it seems my strategy does not actually go through, because we store the state type we can't
actually have decidable equality.

In fact, in the model there is no guarantee about what the state type of the result of `toCoroutine`
is, so we can't have anything decidable that depends on the state type (since we cannot have
decidable equality of types). -/

open CoroutineM (Bisim) in
def bind {α β : Type u} (x : LawfulCoroutineM α) (f : α → LawfulCoroutineM β) :
    LawfulCoroutineM β :=
  Quotient.liftOn x (⟦CoroutineM.bind · (f ·|>.toCoroutine)⟧) <| by
    intro x y ⟨R, bisim, state⟩
    apply Quotient.sound
    refine ⟨Sum.LiftRel R fun
      | ⟨a₁, s₁, f₁⟩, ⟨a₂, s₂, f₂⟩ =>
          CoroutineM.Bisim {state := s₁, next := f₁} {state := s₂, next := f₂},
      ?_, ?_⟩
    · rintro (s₁|⟨_, s₁, next₁⟩) (s₂|⟨_, s₂, next₂⟩) (h_eqv|h_eqv)
      <;> (simp [CoroutineM.bind])
      · specialize bisim _ _ h_eqv
        constructor
        revert bisim
        cases x.next s₁ <;> cases y.next s₂ <;> rintro ⟨bisim⟩
        <;> constructor
        · assumption
        · exact Bisim.rfl _
      · rcases h_eqv with ⟨R', bisim', (state' : R' s₁ s₂)⟩
        -- specialize bisim' _ _ state'
        have := bisim' _ _ state'
        revert this
        simp only
        rcases next₁ s₁ with s₁'|s₁'
        <;> rcases next₂ s₂ with s₂'|s₂'
        <;> rintro ⟨bisim_next'⟩
        <;> constructor
        · simp only [Sum.liftRel_inr_inr]
          exact (⟨R', bisim', bisim_next'⟩ : Bisim ⟨next₁, s₁'⟩ ⟨next₂, s₂'⟩)
    · simpa [CoroutineM.bind] using state

#print axioms bind -- no `sorry`, yay!

instance : Monad LawfulCoroutineM where
  pure := pure
  bind := bind

/-! Show that `LawfulCoroutineM` is indeed a `LawfulMonad` -/
section LawfulFunctor

@[simp] lemma mk_toCoroutine (x : LawfulCoroutineM α) :
    ⟦toCoroutine x⟧ = x := by
  simp [toCoroutine]

instance : LawfulFunctor (LawfulCoroutineM) where
  map_const       := by simp [Functor.mapConst, Functor.map]
  id_map x        := by
    simp only [Functor.map, map, CoroutineM.map_id]
    rw [← mk_toCoroutine x, Quotient.lift_mk, mk_toCoroutine]
  comp_map f g x  := by
    simp only [Functor.map, map]
    rw [← mk_toCoroutine x]
    simp only [Quotient.lift_mk, CoroutineM.map_comp]

end LawfulFunctor

-- section toOption

-- def Terminates : LawfulCoroutineM.

-- noncomputable def toOption (x : LawfulCoroutineM α) : Option α :=
--   match Classical.em x.Terminates with
--     | _ => _
--   -- if h : x.Terminates then
--   --   .some x.run h
--   -- else
--   --   .none

-- end toOption

end LawfulCoroutineM
