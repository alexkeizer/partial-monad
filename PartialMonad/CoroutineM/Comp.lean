import PartialMonad.CoroutineM
import PartialMonad.CoroutineM.Run

namespace CoroutineM

/-- Generalized composition of coroutines:
`comp x y f` will return a coroutine which first runs `x`, then uses the function `f` to pick an
initial state of `y` based on the result of `x`, and then runs the obtained coroutine to completion
-/
def comp {α : Type u} {β : Type (max u v)}
    (x : CoroutineM α) (y : StateMachine β) (f : α → y.σ) : CoroutineM β where
  σ := x.σ ⊕ y.σ
  state := .inl x.state
  next := fun
    | .inl (s : x.σ) => .inl <| (x.next s).map id f
    --  /--------------------------------------^^-^
    --  | If `x` is still going, step into the next state of `x`.
    --  | Otherwise, if `x` has completed, and yielded some value `a`,
    --  |   step into the first state of `y` that corresponds to `a`.
    | .inr (s : y.σ) => (y.next s).map .inr id
    -- ^^^^^^^^^^ Finally, run `y` until completion, mapping its state into
    --            the combined sum state each step

-- TODO: We might want to generalize the type of `f` in `comp _ _ f` to `{a // ∃h, x.run h = a}`
--       That is: "The function `f` is given the value computed by `x` plus a proof that this value
--                  is indeed the result of running `x`."
--       Having this proof might be useful when doing dependently typed shenanigans in the state.
--       However, it would require some extra invariant tracking in the state of `comp`

/-! ## `seq` -/

/-- `seq f y` first runs coroutine `f`, then `y`, and finally applies the result of `f` to the
result of `y`. The computation of `y` *cannot* depend on `f`, the state machines are independent -/
def seq {α β : Type u} (f : CoroutineM (α → β)) (y : CoroutineM α) : CoroutineM β :=
  comp.{u,u} f {
    σ := y.σ × (α → β)
    next := fun ⟨s, f⟩ => (y.next s).map (·, f) f
  } (fun f => (y.state, f))

instance : Applicative (CoroutineM) where
  seq f x := seq f (x ())

/-! ## `bind` -/

/-- Take the (infinite) sum of a family of coroutines `f` -/
def StateMachine.ofFun {α : Type u} {β : Type (max u v)} (f : α → CoroutineM β) : StateMachine β where
  σ     := Σ a, (f a).σ × ((f a).σ → (f a).σ ⊕ β)
  next  := fun ⟨_, s, next⟩ => next s |>.map (⟨_, ·, next⟩) id

/-- `bind x f`, composes two state machines together, by running `f` after `x` completes,
where the second state machine, `f`, may depend on the result of `x`  -/
def bind {α β : Type u} (x : CoroutineM α) (f : α → CoroutineM β) : CoroutineM β :=
  comp.{u,u} x (StateMachine.ofFun.{u,u} f) (fun a => ⟨a, (f a).state, (f a).next⟩)

instance : Monad (CoroutineM) := {bind}
