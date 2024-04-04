import «PartialMonad».Basic

inductive PartialStep (σ : Type u) (α : Type v) : Type (max u v)
  | running (nextState : σ)
  | complete (result : α)

namespace PartialStep

def map (f_state : σ → σ') (f_result : α → α') : PartialStep σ α → PartialStep σ' α'
  | .running s => .running <| f_state s
  | .complete r => .complete <| f_result r

end PartialStep

structure PartialM.Raw.StateMachine.{u, v} (α : Type u) : Type (max u (v+1)) where
  {σ : Type v}
  (next : σ → PartialStep σ α)

structure PartialM.Raw (α : Type u) extends Raw.StateMachine α where
  (state : σ)

/-
I was hoping to simplify things by mandating that the state type `σ` always lives in `Type`,
however, that precludes us from using a dependent sum `Σ (a : α), _` as a state in `bind`, since `α`
lives in an arbitrary universe `Type u`, the dependent sum will live at least in `u` as well.

I really don't want a hidden universe parameter for the state type,
so instead I've tied the state type to live in the same universe as the parameter `α`, and
changed `bind` to have `α` and `β` live in the same universe.
In fact, `Bind.bind` also has `α` and `β` in the same universe, so the previous heterogenous version
was more general than required anyway.

So far, this works
-/


namespace PartialM.Raw

/-! We show that `PartialM.Raw` is a `Monad`:
  `pure a` just returns a state machine that immediately completes, yielding `a`, while
  `bind x f` gives a state machine that morally first runs `x` to completion,
    and then runs `f` using the result yielded by `x` -/
section MonadInstance
/-- We can wrap a value `x : α` into a state machine which immediately completes and yields `x` -/
def pure (x : α) : PartialM.Raw α where
  state := ()
  next _ := .complete x

#check ULift

/-- `map f x` applies a pure function `f : α → β` to the final result of state machine `x`,
after it has completed.
It is allowed for `β` to live in a higher universe from `α`, but not a lower one -/
-- def map {α : Type u} {β : Type (max u v)} (f : α → β) (x : PartialM.Raw α) : PartialM.Raw β where
--   state := ULift.up.{v} x.state
--   next s := match x.next s.down with
--     | .running s => .running (.up s)
--     | .complete a => .complete (f a)
def map {α : Type u} {β : Type v} (f : α → β) (x : PartialM.Raw α) : PartialM.Raw β where
  state := x.state
  next s := match x.next s with
    | .running s => .running (s)
    | .complete a => .complete (f a)

def nextState (x : PartialM.Raw α) : PartialStep (PartialM.Raw α) α :=
  (x.next x.state).map (fun state => {x with state}) id

open PartialStep in
def iterate (x : PartialM.Raw α) : Nat → PartialStep (PartialM.Raw α) α
  | 0    => running x
  | n+1  => match x.nextState with
    | running x => x.iterate n
    | complete a => complete a

theorem iterate_succ (x : PartialM.Raw α) (n : Nat) :
    x.iterate (n+1) = match (x.iterate n) with
      | .running x => x.nextState
      | .complete a => .complete a := by
  induction n generalizing x
  case zero =>
    simp only [iterate]
    split <;> simp_all
  case succ n ih =>
    stop
    rw [iterate]
    -- rcases h_iterate_n : x.iterate n with x_n | a
    rcases h_nextState : x.nextState with x'|a
    · simp
    · simp
    -- · simp [h_iterate_n] at ih
    --   rcases h_nextState : x.nextState with x' | a'
    --   · simp [iterate, h_nextState]
    --   · simp_all
    -- · sorry

/-- `x.CompletesInNSteps n` holds if the state machine `x` yields a value in at most `n` steps -/
def CompletesInNSteps (x : Raw α) (n : Nat) : Prop := ∃ a, x.iterate n = .complete a

/-- If a state machine is known to complete in a finite number of steps, we can compute it's result
 -/
def getOfCompletes (x : Raw α) {n} (h : x.CompletesInNSteps n) : α :=
  match hi : x.iterate n with
    | .running _ => False.elim <| by simp_all [CompletesInNSteps]
    | .complete a => a

/-
> [!todo]
> We could generalize `CompletesInNSteps` to just `CompletesInFiniteTime`, by moving the `n` into
> an existential in the property, as in ``
> ```lean
> def CompletesInFiniteTime (x : Raw α) : Prop := ∃ n a, x.iterate n = .complete a
> ```
> We can then write `getOfCompletes` as a function which matches on `x.nextStep`, and recursively
> calls itself in the `running` branch, using the proof of completion to show that this terminates.
>
> This then leads to a nice noncomputable `toOption` implementation, by using `Classical.em` on
> `x.CompletesInFiniteTime`
-/

/-- `join x` collapses a nested state-machine `x : Raw (Raw σ)` into a single state machine `Raw α`.
Operationally, `join x` first runs `x` until it yields the inner state machine,
which is then run until completion as well -/
def join {α : Type u} (x : PartialM.Raw.{u+1,u} (PartialM.Raw.{u,u} α)) : PartialM.Raw.{u,u} α where
  σ := {state : x.σ × Nat // x.iterate state.2 = .running {x with state := state.1}}
       ⊕ Σ' (n : Nat) (h : x.CompletesInNSteps n), (x.getOfCompletes h).σ
  -- /-  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  -- | The state of `join x` is the sum of states of the outer state machine `x`, and
  -- | the states of the nested state machine that is yielded by `x`
  -- | However, we don't actually know the type of states that this inner machine has, a-priori.
  -- | So, read "the states of the nested state machine" as: the states of the state machine
  -- | returned by `x` in `n` steps, assuming that `x` indeed terminates in `n` steps.
  -- | Then, to actually be able to transition into one of these nested states, we have to show
  -- | that `x` indeed terminates, so we track for the states of `x`, those on the LHS of the sum,
  -- | that indeed we only enter states which are reachable from `x`'s starting state
  state := .inl ⟨⟨x.state, 0⟩, rfl⟩
  next  := fun
    | .inl ⟨⟨(s : x.σ), n⟩, hs⟩ =>
      .running <| match hs' : x.next s with
        | .running s'    => .inl ⟨(s', n+1), by simp [iterate_succ, nextState, hs, hs']; rfl⟩
        -- ^^^^^^^^ If `x` is still `running`, continue with the next state of `x`
        | .complete inner =>
        -- ^^^^^^^^ Otherwise, if `x` has completed,
        --          go to the first state of the nested state machine
          have h_complete := by
            simp only [CompletesInNSteps, iterate_succ, hs, nextState, hs']
            exact ⟨inner, rfl⟩
          have h_cast := by
            simp [getOfCompletes]
            split
            next => exfalso; apply getOfCompletes.proof_1; repeat assumption
            next h =>
              simp only [iterate_succ, hs, nextState, hs'] at h
              change PartialStep.complete inner = _ at h
              injection h with h
              rw [h]
          .inr <| ⟨n+1, h_complete, cast h_cast inner.state⟩
    | .inr ⟨n, h, s⟩ => ((x.getOfCompletes h).next s).map (.inr ⟨n, h, ·⟩) id
    -- ^^^^^^^^^^^^^^^^^^^^^^ Finally, run `f` until completion, mapping its state into
    --                        the combined sum state each step

-- > [!todo]
-- > The setup of `join` is pretty bad. Fixing the state `σ` to live in `Type`, while the return
-- > type may live in arbitrary universes, means that we are not able to store the state-transition
-- > function of the nested state machine in the state of the combined state machine.
-- > Instead, we can only store the proof that the outer machine terminates in `n` steps, and then
-- > re-run the outer state machine until completion for each step of the nested state machine.
-- >
-- > There is some hope that in an eventual "`PartialM.run`" function, the loop that repeatedely
-- > polls the `join` state machine gets inline, so that `CSE` can kick in, and the outer state machine
-- > might not actually be re-run for every step, but having to rely on this series of "hopes" and
-- > "mights" makes me nervous
-- >
-- > I attempted to fix things by introducing a new universe level for the state, in the hopes of
-- > keeping this an internal implementation detail, but, actually storing a state machine in the
-- > `join` result would require a universe bump of the state universe.
-- > This is an unacceptable leak of universe levels, I'm sticking with the computationally horrible
-- > recomputation for now

/-- `bind x f`, composes two state machines together, by running `f` after `x` completes,
where the second state machine, `f`, may depend on the result of `x`  -/
def bind {α β : Type u} (x : PartialM.Raw α) (f : α → PartialM.Raw β) : PartialM.Raw β where
  σ := x.σ ⊕ Σ (a : α), (f a).σ
  -- /-^^^---^^^^^^^^^^^^
  -- | The state of `bind x f` is the sum of states of `x` and `f`
  -- | However, `f` is a *function*, not a straight state machine,
  -- | so read "the states of `f`" as:
  -- |   "the infinite sum of all state types `(f x').σ`, for all possible values `a : α`"
  -- |
  state := .inl x.state
  next := fun
    | .inl (s : x.σ) =>
      .running <| match x.next s with
        | .running s'    => .inl s'
        -- ^^^^^^^ If `x` is still going, `running` into the next state of `x`
        | .complete a => .inr <| ⟨_, (f a).state⟩
        -- ^^^^^^^ Otherwise, if `x` has completed, and yielded some value `a`,
        --         step into the first state of `f` that corresponds to `a`
    | .inr ⟨a, s⟩ => ((f a).next s).map (.inr ⟨_, ·⟩) id
    --          ^^^^^^^^^^^^^^^^^^^^^^ Finally, run `f` until completion, mapping its state into
    --                                 the combined sum state each step

instance : Monad (PartialM.Raw) where
  pure := pure
  bind := bind

end MonadInstance

/-! However, `PartialM.Raw` is not quite lawful -/
section NonLawfulExample

example :
    let x : PartialM.Raw Nat := pure 1
    x ≠ (id <$> x) := by
  simp [pure, Functor.map, Raw.bind, Raw.pure]
  intro h
  exfalso
  /- At this point, the goal is
  ```
  h : Unit = (Unit ⊕ (_ : Nat) × Unit)
  ⊢ False
  ```
  `h` is clearly contradictory, by a type cardinality argument:
    `Unit` has only one inhabitant, while the sum type on the RHS has countably infinite inhabitants
  Thus, the goal should be provable, I just can't be bothered at the moment -/
  sorry

end NonLawfulExample

/-!
In short, we can describe the same computation, resulting in the same final result,
with many different intermediate states.
However, we should care only about the final result, with the intermediate states just being a
computational detail.

Indeed `(id <$> x)` does not change the final result that is computed, but it does change the
state machines internal detail.

Thus, we quotient through a bisimilarity relation, to hide these internal states. -/

inductive PartialStepAgrees (R : σ₁ → σ₂ → Prop) : PartialStep σ₁ α → PartialStep σ₂ α → Prop
  | running {s₁ s₂} : R s₁ s₂ → PartialStepAgrees R (.running s₁) (.running s₂)
  | complete {a} : PartialStepAgrees R (.complete a) (.complete a)

def IsBisimulation {x y : Raw.StateMachine α} (R : x.σ → y.σ → Prop) : Prop :=
  ∀ (s₁ : x.σ) (s₂ : y.σ), R s₁ s₂ → PartialStepAgrees R (x.next s₁) (y.next s₂)

inductive Bisim (x y : PartialM.Raw α) : Prop where
  | mk
    (R : x.σ → y.σ → Prop)
    (bisim : IsBisimulation R)
    (state : R x.state y.state)

/-! `Bisim` is an equivalence -/
section BisimIsEquiv

theorem PartialStepAgrees.rfl (h : ∀ a, R a a) : PartialStepAgrees R x x := by
  cases x <;> constructor
  exact h _

theorem isBisimulation_eq {x : Raw.StateMachine α} : @IsBisimulation _ x x Eq := by
  simp only [IsBisimulation, forall_eq', implies_true, PartialStepAgrees.rfl]

namespace Bisim

theorem rfl (x : PartialM.Raw α) : Bisim x x :=
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
        exact ⟨_, next₁, next₂⟩
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
        assumption
      )

def equivalence : Equivalence (Bisim (α := α)) where
  refl := rfl
  trans := trans
  symm := symm

end Bisim

instance setoid (α : Type _) : Setoid (PartialM.Raw α) where
  r := Bisim
  iseqv := Bisim.equivalence

end BisimIsEquiv


end Raw

/-- TODO: describe `PartialM` -/
def PartialM.{u} (α : Type u) : Type _ := Quotient (PartialM.Raw.setoid.{u,0} α)

namespace PartialM

/-- The canonical map from a raw statemachine into `PartialM` -/
def ofRaw : PartialM.Raw α → PartialM α := Quotient.mk _

def pure (a : α) : PartialM α :=
  .ofRaw <| Raw.pure a

def map (f : α → β) (x : PartialM α) : PartialM β :=
  Quotient.liftOn x (ofRaw ∘ Raw.map f) <| by
    rintro x x' ⟨R, bisim, state⟩
    apply Quotient.sound
    refine ⟨R, ?_, state⟩
    intro s₁ s₂ hR
    simp only [Raw.map]
    specialize bisim _ _ hR
    revert bisim
    cases x.next s₁ <;> cases x'.next s₂
    <;> rintro ⟨hR_nextState⟩
    <;> constructor
    · exact hR_nextState

def Raw.join : PartialM.Raw (PartialM.Raw α) → PartialM.Raw α :=
  (Raw.bind · (fun (x : PartialM.Raw α) => x))

def join (x : PartialM (PartialM α)) : PartialM α :=
  let f_lift (x : Raw (PartialM α)) : PartialM α :=
    -- let xf := x.map _
  have h_lift_sound := by sorry
  Quotient.liftOn x f_lift h_lift_sound

def bind (x : PartialM α) (f : α → PartialM β) : PartialM β :=
  let bind_f (x : PartialM.Raw α) : PartialM β :=
    _
  Quotient.liftOn x bind_f _

/-- `bind'` relies on `PartialFun.mk`, which might not be definable in a sound and computable way -/
def bind' (x : PartialM α) (f : α → PartialM β) : PartialM β :=
  /-
    Defining `bind` is a bit problematics: we can't just lift `Raw.bind`, because
    `Quotient.lift₂` expects both arguments to be a `Quotient`, but `f` is actually a function
      from `α` to a quotient.
    Maybe we can somehow lift the quotient to the top-level, and then lift the function?
  -/
  have h_lift_is_sound := by
    rintro x₁ f₁ x₂ f₂ ⟨Rx, bisim_x, state_x⟩ ⟨Rf, bisim_f, state_f⟩
    apply Quotient.sound
    unfold Raw.bindAux
    refine ⟨
      -- First, we define the relation `R` that will be our bisimulation
      fun
        | .inl s₁, .inl s₂ => Rx s₁ s₂
        | .inr s₁, .inr s₂ => Rf s₁ s₂
        | _, _ => False,
      -- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ This defines `R`
      ?_, state_x⟩
    --    ^^^^^^^ The initial states are related by `R`
    -- And now, we prove that `R` is indeed a bisimulation
    rintro (s₁|s₁ : _ ⊕ _) (s₂|s₂ : _ ⊕ _) h <;> (simp only at h)
    · constructor
      specialize bisim_x _ _ h
      revert bisim_x
      cases x₁.next s₁ <;> cases x₂.next s₂ <;> rintro ⟨h_next⟩
      · exact h_next
      · apply state_f
    · simp [PartialStep.map]
      specialize bisim_f _ _ h
      revert bisim_f
      cases f₁.next s₁ <;> cases f₂.next s₂ <;> rintro ⟨bisim_f⟩
      <;> constructor
      · exact bisim_f

  Quotient.lift₂
    (fun (x : Raw α) (f : RawFun α β) => ofRaw <| Raw.bindAux x f)
    h_lift_is_sound x (PartialFun.mk f)

/-! With `pure` and `bind`, we've shown the quotiented type is still a `Monad` -/
instance : Monad (PartialM) where
  pure := pure
  bind := bind

/-! Furthermore, `PartialM` is actually a `LawfulMonad`, unlike before -/
section Lawful

instance : LawfulFunctor (PartialM) where
  map_const := by simp [Functor.mapConst, Functor.map]
  id_map    := by
    intro _α x
    simp [Functor.map, bind]

  comp_map := sorry

end Lawful

end PartialM

/-!
Next steps:
- [ ] Figure out how to write `bind` on the quotiented `PartialM`
- [ ] Write a good description doc-string for `PartialM`
- [ ] Get the prototype into a working state
- [ ] Find better names for `Raw`, `StateMachine` and `RawFun`
- [ ] Implement Ackermann using `PartialM`
- [ ] Benchmark Ackermann against a "standard" implementation using `partial`
- [ ] Think about combinators for `for` and `while` loops, I want to be able to write code in a
      clean imperative style, so that `PartialM` is a clear improvement over `partial`, without
      trade-offs (besides the extra dependency)
- [ ] Think about how this design relates to Futures (although I'd guess true Futures might also
        involve some non-determinism)
-/

end Bisim







-- instance : LawfulFunctor (PartialM) where
--   map_const := by simp only [Functor.mapConst, Functor.map, forall_const]
--   id_map x := by simp [Functor.map, bind, completed];
--   comp_map := sorry

-- instance : LawfulApplicative (PartialM) where
--   seqLeft_eq := sorry
--   seqRight_eq := sorry
--   pure_seq := sorry
--   map_pure := sorry
--   seq_pure := sorry
--   seq_assoc := sorry

-- instance : LawfulMonad (PartialM) where
--   bind_pure_comp := sorry
--   bind_map := sorry
--   pure_bind := sorry
--   bind_assoc := sorry

-- end MonadInstance
