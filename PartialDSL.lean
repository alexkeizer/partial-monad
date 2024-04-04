import Std.Data.Sum.Basic

/-!

Including the type of states `σ` and the transition function into the `PartialM` monad requires a
universe bump. This universe bump causes all kinds of problems when trying to define `PartialM.bind`.

Thus, in this file we explore an alternative idea, we keep the state type external, as a parameter
to `PartialM`.
Then, we lose the ability to compose partial computations from different statemachines
together with just `do`-notation, so we recover this with a specialized `partial` dsl.

Sadly, I'm not sure that `PartialStateM σ : Type → Type`, for some fixed state `σ` is a monad.
How would we define `pure`, without being able to control the state machine?
In fact, how do we even

-/

structure PartialStateM.Raw (σ α : Type) :
    Type where
  state : σ
  next : σ → σ ⊕ α

namespace PartialStateM.Raw

def nextState (x : Raw σ α) : Raw σ α ⊕ α :=
  x.next x.state |>.map ({x with state := ·}) id

def pure {σ : Type} [Inhabited σ] {α} (a : α) : Raw σ α where
  state := default
  next := fun _ => .inr a

/-!
Side Note: `pure` is the reason we store `next` in `Raw` as well,
rather than having a fixed transition function determined by `σ`.

If we did the latter, then both the state space and the computation would be fixed,
we could only pick the state at which to start the computation. This means that the choice of `σ`
would also determine the output type `α`, hence, there would be no way to define `pure` as above.

We could make `next` a parameter to `Raw` as well, but then could only define `pure` for
particular values of `next`, where in particular `next` depends on `α`,
so we still would not get a proper `Monad` instance. -/

def map (f : α → β) (x : Raw σ α) : Raw σ β where
  state := x.state
  next s := match x.next s with
    | .inl s' => .inl s'
    | .inr a  => .inr (f a)

instance : Functor (Raw σ) where
  map := map

/-- `join x` collapses a nested state-machine `x : Raw (Raw σ)` into a single state machine `Raw α`.
Operationally, `join x` first runs `x` until it yields the inner state machine,
which is then run until completion as well -/
def join (x : Raw σ₁ (Raw σ₂ α)) : Raw (σ₁ ⊕ Raw σ₂ α) α where
  state := .inl x.state
  next := fun
    | .inl s₁ => .inl <| x.next s₁
    | .inr s₂ => s₂.nextState |> Sum.map .inr id

/-!
## A note on homogeneous join
Even if we know that `σ₁ = σ₂`, we are not automatically able to join this into a state machine
with the same state space.
This is because the nested state machine might use a different transition function, so we actually
need to store the nested transition function as well.

(I guess this would be a good argument for externalising the transition function as well, but then
 how do we define `pure`?)
-/

def bind (x : Raw σ₁ α) (f : α → Raw σ₂ β) : Raw (σ₁ ⊕ (Raw σ₂ β)) β :=
  (x.map f).join


section BisimSection

def IsBisimulation (x : Raw σ₁ α) (y : Raw σ₂ α) (R : σ₁ → σ₂ → Prop) : Prop :=
  ∀ (s₁ : σ₁) (s₂ : σ₂), R s₁ s₂ → (Sum.LiftRel R Eq) (x.next s₁) (y.next s₂)

inductive Bisim (x : Raw σ₁ α) (y : Raw σ₂ α) : Prop where
  | mk
    (R : σ₁ → σ₂ → Prop)
    (bisim : IsBisimulation x y R)
    (state : R x.state y.state)

/-! `Bisim` is an equivalence -/
section BisimIsEquiv

theorem isBisimulation_eq {x : Raw σ α} : IsBisimulation x x Eq := by
  simp only [IsBisimulation, forall_eq', implies_true]
  intro s; cases x.next s <;> (constructor; rfl)

namespace Bisim

theorem rfl (x : Raw σ α) : Bisim x x :=
  .mk Eq isBisimulation_eq (by rfl)

theorem trans : Bisim x y → Bisim y z → Bisim x z
  | ⟨R₁, bisim₁, state₁⟩, ⟨R₂, bisim₂, state₂⟩ =>
    .mk
      (R := fun x z => ∃ y, R₁ x y ∧ R₂ y z)
      (state := ⟨y.state, state₁, state₂⟩)
      (bisim := by
        intro s₁ s₃
        simp
        intro s₂ hR₁ hR₂
        specialize bisim₁ _ _ hR₁; revert bisim₁
        specialize bisim₂ _ _ hR₂; revert bisim₂

        rcases x.next s₁ with s₁'|a₁
        <;> rcases y.next s₂ with s₂'|a₂
        <;> rcases z.next s₃ with s₃'|a₃
        <;> rintro ⟨next₂⟩ ⟨next₁⟩
        <;> constructor
        · exact ⟨_, next₁, next₂⟩
        · simp_all
      )

theorem symm : Bisim x y → Bisim y x
  | ⟨R, bisim, state⟩ =>
      .mk (R := fun s₂ s₁ => R s₁ s₂) (state := state) (bisim := by
        intros s₁ s₂ hR
        specialize bisim _ _ hR
        revert bisim
        cases x.next s₂ <;> cases y.next s₁
        <;> rintro ⟨bisim⟩
        <;> constructor
        · assumption
        · simp_all
      )

def equivalence : Equivalence (Bisim (σ₁ := σ) (σ₂ := σ) (α := α)) where
  refl := rfl
  trans := trans
  symm := symm

end Bisim

instance setoid (α : Type _) : Setoid (Raw σ α) where
  r := Bisim
  iseqv := Bisim.equivalence

end BisimIsEquiv
end BisimSection

end Raw

/-
So far, so good, but we already highlighted that there is no hope for a `Monad` instance here.
The whole reason for bothering with quotients, is that they were required to make the `Monad`
instance on raw state machines (with bundled state types) lawful.
If we don't have a Monad instance to begin with, what's the point?

I guess there is still the benefit of it being the proper thing to do, so that equality does not
distinguish what we don't want distuinguished.

However, for LeanMLIR the quotient might not even be necessary:
We can just define the refinement relation on partial computations to consider bisimular
computations refinements of eachother, thus side-stepping the mis-behaving equality -/
