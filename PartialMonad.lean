import «PartialMonad».Basic

inductive PartialStep (σ : Type u) (α : Type v) : Type (max u v)
  | step (nextState : σ)
  | complete (result : α)

namespace PartialStep

def map (f_state : σ → σ') (f_result : α → α') : PartialStep σ α → PartialStep σ' α'
  | .step s => .step <| f_state s
  | .complete r => .complete <| f_result r

end PartialStep

structure PartialM.Raw.StateMachine (α : Type u) : Type (u+1) where
  {σ : Type u}
  (next : σ → PartialStep σ α)

structure PartialM.Raw (α : Type u) extends Raw.StateMachine α where
  (state : σ)

/-- `RawFun α β` represents a function `α → Raw β` in such a way that we can quotient it, by
summing all possible states into one state machine, and letting the initial state depend on some
value `a : α` -/
structure PartialM.RawFun (α : Type u) (β : Type v) extends Raw.StateMachine (ULift β) where
  (stateFun : α → σ)

def PartialM.RawFun.apply (f : RawFun α β) (a : α) : (PartialM.Raw β) where
  toStateMachine := f.toStateMachine
  state := f.stateFun a

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

/-- `ofFun f` turns a `f : α → Raw β` into the equivalent `RawFun α β`  -/
def ofFun {α : Type u} {β : Type v} (f : α → Raw β) : RawFun α β where
  σ := Σ a, (f a).σ
  next := fun ⟨a, s⟩ => (f a).next s |>.map (⟨_, ·⟩) id
  stateFun := fun a => ⟨_, (f a).state⟩

def bindAux (x : PartialM.Raw α) (f : PartialM.RawFun α β) : PartialM.Raw β where
  σ := x.σ ⊕ f.σ
  -- /-^^^---^^^
  -- | The state of `bind x f` is the sum of states of `x` and `f`
  -- | However, `f` is a *function*, not a straight state machine,
  -- | so read "the states of `f`" as:
  -- |   "the infinite sum of all state types `(f x').σ`, for all possible values `a : α`"
  state := .inl x.state
  next := fun
    | .inl s      =>
      .step <| match x.next s with
        | .step s'    => .inl s'
        -- ^^^^^^^ If `x` is still going, `step` into the next state of `x`
        | .complete a => .inr <| f.stateFun a
        -- ^^^^^^^ Otherwise, if `x` has completed, and yielded some value `a`,
        --         `step` into the first state of `f` that corresponds to `a`
    | .inr s => (f.next s).map .inr id
    --          ^^^^^^^^^^^^^^^^^^^^^^ Finally, run `f` until completion, mapping its state into
    --                                 the combined sum state each step

/-- `bind x f`, composes two state machines together, by running `f` after `x` completes,
where the second state machine, `f`, may depend on the result of `x`  -/
def bind (x : PartialM.Raw α) (f : α → PartialM.Raw β) : PartialM.Raw β :=
  bindAux x (ofFun f)

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
  | step {s₁ s₂} : R s₁ s₂ → PartialStepAgrees R (.step s₁) (.step s₂)
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

/-! The notion of `Bisim`ilarity generalizes to `RawFun` -/
inductive RawFun.Bisim (x y : PartialM.RawFun α β) : Prop where
  | mk
    (R : x.σ → y.σ → Prop)
    (bisim : Raw.IsBisimulation R)
    (state : ∀ a, R (x.stateFun a) (y.stateFun a))

/-! `RawFun.Bisim`, too, is an equivalence -/
namespace RawFun.Bisim
open PartialM (RawFun)
open PartialM.Raw (isBisimulation_eq)


theorem rfl (x : RawFun α β) : Bisim x x :=
  .mk Eq isBisimulation_eq (by intro; rfl)

theorem trans : Bisim x y → Bisim y z → Bisim x z
  | ⟨R₁, bisim₁, state₁⟩, ⟨R₂, bisim₂, state₂⟩ =>
    .mk
      (R := fun x z => ∃ y, R₁ x y ∧ R₂ y z)
      (state := fun a => ⟨y.stateFun a, state₁ a, state₂ a⟩)
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

def equivalence : Equivalence (Bisim (α := α) (β := β)) where
  refl := rfl
  trans := trans
  symm := symm

end RawFun.Bisim

instance RawFun.setoid (α β : Type) : Setoid (PartialM.RawFun α β) where
  r := Bisim
  iseqv := Bisim.equivalence

/-- TODO: describe `PartialM` -/
def PartialM (α : Type u) : Type (u+1) := Quotient (PartialM.Raw.setoid α)

/-- `PartialFun α β` represents a function `α → PartialM β` -/
def PartialFun (α β : Type) : Type 1 := Quotient (RawFun.setoid α β)

namespace PartialFun

def apply (f : PartialFun α β) : α → PartialM β := fun a =>
  Quotient.liftOn f (fun rf => Quotient.mk _ <| rf.apply a) <| by
    rintro rf₁ rf₂ ⟨R, bisim, stateFun⟩
    apply Quotient.sound
    exact ⟨R, bisim, stateFun _⟩

#check Raw.bind

/-!
  How do I actually define `mk`?
  I assume I have to go through `Quotient.lift`, or one of it's variants, somehow, but those
  all operate on `x : Quotient _`, but what I have is a function `f : α → Quotient _`

  Mathlib has [`Quotient.choice`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Quot.html#Quotient.choice),
  which does what i want, but is noncomputable, and
  [`Quotient.finChoice`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Quotient.html#Quotient.finChoice),
  which is computable, but only works if the argument of the function-type is a finite type.

  The fact that `Quotient.choice` is exactly the signature I need, makes me suspect that it is
  fundamentally impossible to do this computably.

  That means, I could only define `bind` over `PartialM α` when `α` is a finite type.
  Thus, `PartialM` would not be a true `Monad` (since `Monad` mandates a `Type u → Type v` signature,
  it leaves no room for the extra `Fintype` assumption).

  `Raw : Type → Type`

-/

def mk (f : α → PartialM β) : PartialFun α β :=
  -- Quotient.hrecOn _ _ _
  sorry

end PartialFun

namespace PartialM

/-- The canonical map from a raw statemachine into `PartialM` -/
def ofRaw : PartialM.Raw α → PartialM α := Quotient.mk _

def pure (a : α) : PartialM α :=
  .ofRaw <| Raw.pure a

def Raw.map (f : α → β) (x : PartialM.Raw α) : PartialM.Raw β where
  state := x.state
  next s := match x.next s with
    | .step s => .step s
    | .complete a => .complete (f a)

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
  Quotient.liftOn x _ _

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
