import Std.Data.Sum.Basic
import Std.Data.Sum.Lemmas

/-!
This file defines the `CoroutineM` monad.

A coroutine is a suspendable, potentially non-terminating computation.
Note that this file defines such coroutines directly in terms of state machines,
which means different computations resulting in the same final value are not necessarily equal.
In particular, this monad is *not* an instance of `LawfulMonad`.

For a lawful, but more complicated version, see `LawfulCoroutineM`
-/

structure CoroutineM.StateMachine (α : Type u) : Type (u+1) where
  {σ : Type u}
  (next : σ → σ ⊕ α)

structure CoroutineM (α : Type u) extends CoroutineM.StateMachine α where
  (state : σ)

namespace CoroutineM

/-- We generally identify a state machine with its transition function;
with the following `CoeFun` instance, we can use `c : StateMachine α` wherever a function of type
`c.σ → c.σ ⊕ α` is expected, and Lean will coerce it automatically -/
instance : CoeFun (StateMachine α) (fun c => c.σ → c.σ ⊕ α) where
  coe c := c.next

/-- Establish the coerced form as the simp-normal form  -/
@[simp] theorem next_eq (c : StateMachine α) : c.next = c := rfl

/-!
TODO: figure out how this simp normal form interacts with `x : CoroutineM α`, would the normal form
now be `x.toStateMachine` over `x.next`? That is a bit ugly.
-/

/-- Runs the coroutine for a single step -/
def nextState (x : CoroutineM α) : (CoroutineM α) ⊕ α :=
  (x.next x.state).map (fun state => {x with state}) id

/-- `pure a` gives a trivial coroutine, which completes in a single step, yielding the value `a` -/
def pure (a : α) : CoroutineM α where
  state := ()
  next _ := .inr a

instance : Pure (CoroutineM) := {pure}

/-- `map f x` applies a pure function `f : α → β` to the final result of state machine `x`,
after it has completed. -/
def map {α β : Type u} (f : α → β) (x : CoroutineM α) : CoroutineM β where
  state  := x.state
  next s := x.next s |>.map id f

instance : Functor (CoroutineM) := {map}

-- def bind {α β : Type u} (x : CoroutineM α) (f : α → CoroutineM β) : CoroutineM β where
--   σ := x.σ ⊕ Σ (a : α), let σ' := (f a).σ; σ' × (σ' → σ' ⊕ β)
--   -- /-^^^---^^^^^^^^^^^^^^^^^^
--   -- | The state of `bind x f` is the sum of states of `x` and `f`
--   -- | However, `f` is a *function*, not a straight state machine,
--   -- | so read "the states of `f`" as:
--   -- |   "the infinite sum of all state types `(f x').σ`, for all possible values `a : α`"
--   state := .inl x.state
--   next := fun
--     | .inl (s : x.σ) =>
--       .inl <| (x.next s).map id (fun a => ⟨_, (f a).state, (f a).next⟩)
--         --  /----------------^^-----------^^^^^^^^^^^^^^^^^^^^^^^^^^^
--         --  | If `x` is still going, step into the next state of `x`,
--         --  |
--         --  | Otherwise, if `x` has completed, and yielded some value `a`,
--         --  | step into the first state of `f` that corresponds to `a`.
--         --  | Additionally, we store the transition function, so that we don't have to recompute it
--         --  | at every step
--     | .inr ⟨a, s, next⟩ => (next s).map (.inr ⟨a, ·, next⟩) id
--     -- ^^^^^^^^^^ Finally, run `f` until completion, mapping its state into
--     --            the combined sum state each step

-- instance : Monad (CoroutineM) where
--   pure := pure
--   bind := bind



end CoroutineM
