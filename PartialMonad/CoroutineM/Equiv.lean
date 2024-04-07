import PartialMonad.CoroutineM.Run
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Relation.Trans


namespace CoroutineM

/-- Two coroutines are considered equivalent if both terminate and yield the same result,
or if neither coroutine terminates -/
inductive Equiv (x y : CoroutineM α) : Prop
  | terminates : (hx : x.Terminates) → (hy : y.Terminates) → x.run hx = y.run hy → Equiv x y
  | non_terminates : ¬x.Terminates → ¬y.Terminates → Equiv x y

-- inductive Bisim (x y : CoroutineM α) : Prop
--   | mk
--     (R : x.σ → y.σ → Prop)
--     (state : R x.state y.state)
--     (is_bisim : ∀ s₁ s₂, R s₁ s₂ → _)

namespace Equiv

/-! Show that `Equiv` is an equivalence relation -/
section Equivalence

theorem rfl (x : CoroutineM α) : Equiv x x := by
  by_cases h : x.Terminates
  · exact Equiv.terminates h h _root_.rfl
  · exact Equiv.non_terminates h h

theorem symm : Equiv x y → Equiv y x
  | terminates hx hy run_eq => terminates hy hx run_eq.symm
  | non_terminates hx hy => non_terminates hy hx

theorem trans : Equiv x y → Equiv y z → Equiv x z
  | terminates hx _ run_xy_eq,  terminates _ hz run_yz_eq => terminates hx hz (by simp_all)
  | non_terminates hx _,        non_terminates _ hz       => non_terminates hx hz
  | non_terminates ..,          terminates ..             => by contradiction

def is_equivalence (α : Type u) : Equivalence (@Equiv α) := {refl := rfl, symm, trans}

instance setoid (α : Type u) : Setoid (CoroutineM α) where
  r := Equiv
  iseqv := is_equivalence α

instance : Trans (@Equiv α) (Equiv) (Equiv) := {trans}
instance : Trans (@HasEquiv.Equiv (CoroutineM α) _) (HasEquiv.Equiv) (HasEquiv.Equiv) := {trans}

end Equivalence

/-! `Equiv` is a strictly weaker relation than (strong) bisimilarity -/
section OfBisim

inductive StepAgrees (R : σ₁ → σ₂ → Prop) : σ₁ ⊕ α → σ₂ ⊕ α → Prop
  | inl {s₁ s₂} : R s₁ s₂ → StepAgrees R (.inl s₁) (.inl s₂)
  | inr {a} : StepAgrees R (.inr a) (.inr a)

def IsBisimulation {x y : CoroutineM α} (R : x.σ → y.σ → Prop) : Prop :=
  ∀ (s₁ : x.σ) (s₂ : y.σ), R s₁ s₂ → StepAgrees R (x.next s₁) (y.next s₂)

def IsBisimulation' {x y : CoroutineM α} (R : x.σ → y.σ → Prop) : Prop :=
  ∀ (s₁ : x.σ) (s₂ : y.σ), R s₁ s₂ →
    ∃ n m, StepAgrees R ({x with state := s₁}.iterate n) ({y with state := s₂}.iterate m)

theorem iterate_agrees_of_bisim {x y : CoroutineM α}
      {R} (h_bisim : IsBisimulation R) (h_state : R x.state y.state) :
    ∀ n, (StepAgrees R) (x.iterate n) (y.iterate n) := by
  intro n
  induction n
  case zero => exact .inl h_state
  case succ n ih =>
    simp [iterate_succ]
    revert ih
    cases iterate x n <;> cases iterate y n
    <;> rintro ⟨hR_val⟩
    <;> simp only
    · apply h_bisim _ _ hR_val
    · constructor

/-!
`iterate_of_bisim` exposes the crux of why `Bisim` is flawed: it mandates that the state machines
agree at each iteration `n`, whereas we would like it to mean that for every `n`, there is some `m`
so that `x.iterate n` and `y.iterate m` agree, to allow for extra computation steps taken by
either -/

theorem StepAgrees.isLeft_iff {R} {s₁ : σ₁ ⊕ α} {s₂ : σ₂ ⊕ α} (h : StepAgrees R s₁ s₂) :
    s₁.isLeft ↔ s₂.isLeft := by
  cases h <;> simp

theorem StepAgrees.isRight_iff {R} {s₁ : σ₁ ⊕ α} {s₂ : σ₂ ⊕ α} (h : StepAgrees R s₁ s₂) :
    s₁.isRight ↔ s₂.isRight := by
  cases h <;> simp

theorem StepAgrees.eq_of_inr {R : σ₁ → σ₂ → Prop} {a : α} {y : σ₂ ⊕ α} :
    StepAgrees R (.inr a) y → y = .inr a := by
  rintro ⟨⟩; rfl

-- theorem minimumStepsToTerminate_eq_of_bisim {x y : CoroutineM}

#check run

theorem of_bisim {x y : CoroutineM α} (h : ∃ R, IsBisimulation R ∧ R x.state y.state) :
    x ≈ y := by
  rcases h with ⟨R, bisim, state⟩
  by_cases h : x.Terminates
  · have iterate_agrees := iterate_agrees_of_bisim bisim state (x.minimumStepsToTerminate h)
    apply Equiv.terminates h ?y_terminates
    · rw [iterate_minimumStepsToTerminate] at iterate_agrees
      rw [run_eq_of_iterate_eq_inr iterate_agrees.eq_of_inr]
    · use (x.minimumStepsToTerminate h)
      simp [← iterate_agrees.isRight_iff, iterate_minimumStepsToTerminate]
  · apply Equiv.non_terminates h
    simp_all only [Terminates, not_exists, Bool.not_eq_true, Sum.isRight_eq_false]
    intro n
    rw [← iterate_agrees_of_bisim bisim state n |>.isLeft_iff]
    exact h n



end OfBisim

#exit

/-- If a coroutine `x` terminates, yielding some value `a`, then `x` is equivalent to `pure a` -/
theorem pure_run_equiv (x : CoroutineM α) (h : x.Terminates) :
    pure (x.run h) ≈ x := by
  apply terminates (pure_terminates _) h (run_pure _)

theorem terminates_of_equiv {x y : CoroutineM α} (h_eqv : x ≈ y) :
    x.Terminates → y.Terminates := by
  intro h_terminates
  cases h_eqv
  · assumption
  · contradiction

-- theorem pure_equiv_iff {a : α} {x : CoroutineM α} :
--     pure a ≈ x ↔ (∃ (h : x.Terminates), x.run h = a) := by
--   sorry

-- theorem iterate_bind_eq_of_iterate_x_eq

@[simp] theorem bind_next_inl (x : CoroutineM α) (f : α → CoroutineM β) (s : x.σ) :
    (x >>= f).next (.inl s) = .inl ((x.next s).map id (⟨·, (f _).state, (f _).next⟩)) := by
  rfl

@[simp] theorem nextState_mk {σ α} (next : σ → σ ⊕ α) (s : σ) :
    nextState (mk next s) = (next s).map (mk next ·) id := by
  rfl

-- theorem iterate_bind_eq_of_x_iterate {x : CoroutineM α} {n} (h : (x.iterate n = .inl {})
-- TODO: a theorem states that if `x.iterate n` has not yet completed, but is at new state `s'`,
--       then `(x >>= f)` is at state `.inl s'`
-- To phrase this nicely, we really need `iterate` to just return a state, rather than a full-blown
-- coroutine

theorem iterate_bind_isLeft_of {x : CoroutineM α} {n} (h : (x.iterate n).isLeft)
    (f : α → CoroutineM β) : (iterate (x >>= f) n).isLeft := by
  rw [show (x >>= f) = {(x >>= f) with state := .inl x.state} from _root_.rfl]
  rw [show x = {x with state := x.state} from _root_.rfl] at h
  generalize x.state = state at *
  induction n generalizing state
  case zero       => rfl
  case succ n ih  => cases h' : x.next state <;> simp_all [iterate]

theorem bind_iterate_minimumStepsToTerminate_x {x : CoroutineM α} (h : x.Terminates)
    (f : α → CoroutineM β) :
    (x >>= f).iterate (x.minimumStepsToTerminate h)
    = .inl (.inr ⟨x.run h, (f _).state, (f _).next⟩) := by
  simp only
  sorry


/-- If `x` terminates, yielding some value `a`, then `x >>= f` is equivalent to `f a` -/
theorem bind_equiv_of_terminates {x : CoroutineM α} (h : x.Terminates) :
    (x >>= f) ≈ f (x.run h) := by
  by_cases (f <| x.run h).Terminates
  case pos h_f_terminates => sorry
  case neg h_f_not_terminates =>
    apply non_terminates _ h_f_not_terminates
    sorry


theorem non_terminates_of_cycle (x : CoroutineM α) (S : Set x.σ)
    (h_state : x.state ∈ S)
    (h_closed : ∀ s ∈ S, ∃ s' ∈ S, x.next s = .inl s') :
    ¬x.Terminates := by
  intro h_terminates
  have iterate_mem_S : ∀ n, ∃ state ∈ S, x.iterate n = .inl state := by
    intro n
    induction n
    case zero =>
      simp [h_state]
    case succ n ih =>
      rcases ih with ⟨s, s_mem_S, hs⟩
      rcases h_closed _ s_mem_S with ⟨s', s'_mem, hs'⟩
      simp [iterate_succ, hs, hs', s'_mem]
  have ⟨s, _s_mem, hs⟩ := iterate_mem_S (x.minimumStepsToTerminate h_terminates)
  have := x.iterate_minimumStepsToTerminate h_terminates
  rw [hs] at this
  contradiction

-- theorem cycle_of_non_terminates {x : CoroutineM α} (h : ¬x.Terminates) :
--   ∃ S, x.state ∈ S ∧ (∀ s ∈ S, ∃ s' ∈ S, x.next s = .inl s')

theorem nextState_isLeft_of_iterate_succ_isLeft {x : CoroutineM α} :
    (x.iterate (n+1)).isLeft → (x.next x.state).isLeft := by
  unfold iterate; cases x.next x.state <;> simp

-- @[simp] theorem nextState_bind (x : CoroutineM α) (f : α → CoroutineM β) :
--     nextState (x >>= f) = match nextState x with
--       | .inl _ => .inl { x >>= f with state := _}
--       | .inr _ => _ := by
--   sorry

theorem bind_non_terminates_of_left {x : CoroutineM α} (h : ¬x.Terminates) :
    ¬(x >>= f).Terminates := by
  simp only [Terminates, not_exists, Bool.not_eq_true, Sum.isRight_eq_false] at h ⊢
  intro n
  apply iterate_bind_isLeft_of (h n)

theorem bind_equiv {x y : CoroutineM α} (f g : α → CoroutineM β) (hxy : x ≈ y)
    (hfg : (h : x.Terminates) → (f <| x.run h) ≈ (g <| y.run <| terminates_of_equiv hxy h)) :
    (x >>= f) ≈ (y >>= g) :=
  match hxy with
    | terminates hx hy _ =>
        calc
          x >>= f ≈ f (x.run hx)  := by apply bind_equiv_of_terminates
                _ ≈ g (y.run hy)  := by apply hfg hx
                _ ≈ y >>= g       := by apply Equiv.symm; apply bind_equiv_of_terminates
    | non_terminates hx hy =>
        non_terminates (bind_non_terminates_of_left hx) (bind_non_terminates_of_left hy)

#print axioms bind_equiv
