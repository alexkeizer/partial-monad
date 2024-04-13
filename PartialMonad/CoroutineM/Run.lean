import PartialMonad.CoroutineM
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Order.SetNotation

import Mathlib

/-!
# Extracting Values From Coroutines

Main definitions:
* `iterate x n`, which runs coroutine `x` for `n` steps
* `Terminates x` holds if the coroutine `x` terminates in finite time
* `run x h`, which runs `x` until completion, given a proof `h` that this will
    happen in finite time
-/

namespace CoroutineM

namespace StateMachine

/-- `c.iterate s n` runs the state machine `c` for `n` steps, starting at state `s` -/
def iterate (c : StateMachine α) (s : c.σ) : Nat → c.σ ⊕ α
  | 0   => .inl s
  | n+1 => match c s with
      | .inl s' => iterate c s' n
      | .inr a  => .inr a

/-- A state `s` of some state machine `c` is said to terminate, if starting at that state, the
state machine will yield a value in a finite number of steps -/
def StateTerminates (c : StateMachine α) (s : c.σ) : Prop :=
  ∃ n, (c.iterate s n).isRight

/-- `x.minimumStepsToTerminate s h` is the smallest number `n`, such that, starting from state `s`,
the state machine produces a result in `n` steps.
This number is produced with the axiom of choice, and is thus noncomputable, but it makes for a good
measure to show termination of functions that operate on coroutines which are known to terminate -/
noncomputable def minimumStepsToTerminate (c : StateMachine α) (s : c.σ)
    (_h : c.StateTerminates s) : Nat :=
--   ^^ Technically, this assumption is not necessary: if `s` does not terminate, then the set
--      used below is empty, and the supremum if an empty set is defined (as `0`)
--      Still, that number doesn't make much sense for non-terminating states, so we keep the
--      assumption
  sInf {n | (c.iterate s n).isRight}

/-- Every coroutine needs at least one step to terminate -/
theorem minimumStepsToTerminate_pos (c : StateMachine α) (s : c.σ)
    (s_terminates : c.StateTerminates s) :
    0 < c.minimumStepsToTerminate s s_terminates := by
  by_contra h
  simp [minimumStepsToTerminate, iterate] at h
  rcases s_terminates with ⟨n, iterate_n_eq⟩
  apply Set.not_mem_empty n
  simpa only [← h] using iterate_n_eq

theorem iterate_isLeft_of_le_minimumStepsToTerminate (c : StateMachine α) (s : c.σ)
    (s_terminates : c.StateTerminates s) {n}
    (h_lt : n < c.minimumStepsToTerminate s s_terminates) :
    (c.iterate s n).isLeft := by
  simpa using Nat.not_mem_of_lt_sInf h_lt

section Lemmas

@[simp] theorem iterate_zero (c : StateMachine α) (s) : c.iterate s 0 = .inl s := rfl
@[simp] theorem iterate_one (c : StateMachine α) (s) : c.iterate s 1 = c s := by
  unfold iterate; cases c s <;> rfl

theorem iterate_add (c : StateMachine α) (s : c.σ) (n m : Nat) :
    c.iterate s (n+m) = match (c.iterate s n) with
      | .inl s => (c.iterate s m)
      | .inr a => .inr a := by
  induction n generalizing s
  case zero => simp
  case succ n ih =>
    have : n.succ + m = (n + m) + 1 := by ac_rfl
    rw [this, iterate]
    cases hx : c.next s
    case inl s' => simp only; rw [ih s', iterate, hx]
    case inr _  => simp [iterate, hx]

theorem iterate_succ (c : StateMachine α) (s : c.σ) (n : Nat) :
    c.iterate s (n+1) = match (c.iterate s n) with
      | .inl s => c s
      | .inr a => .inr a := by
  simp [iterate_add]

theorem iterate_succ_of_next_eq_inl {c : StateMachine α} {state state'}
    (h : c.next state = .inl state') :
    ∀ n, c.iterate state (n+1) = c.iterate state' n := by
  intro; rw [iterate, h]

end Lemmas

end StateMachine

/-- `x.iterate n` runs the coroutine for `n` steps -/
def iterate (x : CoroutineM α) : Nat → x.σ ⊕ α :=
  x.toStateMachine.iterate x.state

@[simp] theorem iterate_zero (x : CoroutineM α) : x.iterate 0 = .inl x.state := rfl
theorem iterate_succ (x : CoroutineM α) (n : Nat) :
    x.iterate (n+1) = match (x.iterate n) with
      | .inl s => x.next s
      | .inr a => .inr a := by
  simp only [iterate, StateMachine.iterate_succ]
  cases x.toStateMachine.iterate x.state n <;> rfl

def Terminates (x : CoroutineM α) : Prop :=
  x.toStateMachine.StateTerminates x.state

/-- `x.minimumStepsToTerminate h` is the smallest number `n`, such that `x` terminates in `n` steps -/
protected noncomputable def minimumStepsToTerminate (x : CoroutineM α) (h : x.Terminates)  : Nat :=
  x.toStateMachine.minimumStepsToTerminate x.state h
theorem minimumStepsToTerminate_eq {x : CoroutineM α} {h} :
    x.minimumStepsToTerminate h = sInf {n | (x.iterate n).isRight} := rfl

theorem minimumStepsToTerminate_pos (x : CoroutineM α) (h : x.Terminates) :
    0 < x.minimumStepsToTerminate h :=
  StateMachine.minimumStepsToTerminate_pos _ x.state h

open StateMachine in
/-- We can soundly run a coroutine until completion, given a proof that it will terminate in finite
time -/
def run (x : CoroutineM α) (h_terminates : x.Terminates) : α :=
  match h_nextState : x.next x.state with
    | .inl state' =>
        let x' := {x with state := state'}
        have h_terminates' : x'.Terminates := by
          rcases h_terminates with ⟨n, h⟩
          cases n
          case zero =>
            simp at h
          case succ n =>
            simp [iterate, StateMachine.iterate, h_nextState] at h
            exact ⟨_, h⟩
        have : x'.minimumStepsToTerminate h_terminates'
               < x.minimumStepsToTerminate h_terminates := by
          apply Nat.lt_of_succ_lt_succ
          show _ + 1 < _ + 1
          unfold CoroutineM.minimumStepsToTerminate minimumStepsToTerminate
          simp only [← iterate_succ_of_next_eq_inl h_nextState]
          rw [Nat.sInf_add (p:=fun m =>
            Sum.isRight (StateMachine.iterate x.toStateMachine x.state m))]
          · constructor
          · apply Nat.succ_le_of_lt <| minimumStepsToTerminate_pos _ h_terminates
        x'.run h_terminates'

    | .inr a => a
termination_by x.minimumStepsToTerminate h_terminates

#print axioms run -- `sorry`-free, yay!

theorem iterate_minimumStepsToTerminate {x : CoroutineM α} (h) :
    x.iterate (x.minimumStepsToTerminate h) = .inr (x.run h) := by
  stop
  have n_spec := iterate_minimumStepsToTerminate_isRight x h
  generalize x.minimumStepsToTerminate h = n at *
  rcases x with ⟨x, state⟩
  induction n generalizing state
  case zero => simp at n_spec
  case succ n ih =>
    unfold run
    split
    next state' h_state' =>
      simp only at h_state'
      simp only [iterate, h_state'] at n_spec ⊢
      apply ih _ _ n_spec
    next a =>
      simp_all [iterate]

-- /-- If iterating `` -/
-- theorem ge_minimumStepToIterate_of_iterate_eq {x : CoroutineM α} {n} {a} :
--     x.iterate n = .inr a → ∀ h, n ≥ x.minimumStepsToTerminate h

/-- If we can show that iterating a coroutine for some number of steps yiels a result `a`, then
running that coroutine until completion yields that same result -/
theorem run_eq_of_iterate_eq_inr {x : CoroutineM α} {n} {a} (h : x.iterate n = .inr a)
    (x_terminates : x.Terminates := ⟨n, by simp_all [iterate]⟩) :
    x.run x_terminates = a := by
  apply Sum.inr_injective
  rw [← iterate_minimumStepsToTerminate, minimumStepsToTerminate_eq]
  sorry


/-! Show that various constructions terminate (assuming that it's arguments terminate) -/
section Terminates

@[simp] theorem pure_terminates (a : α) : (pure a).Terminates := ⟨1, by rfl⟩
@[simp] theorem next_pure (a : α) (s) : (pure a).next s = .inr a := rfl
@[simp] theorem nextState_pure (a : α) : nextState (pure a) = .inr a := rfl
@[simp] theorem run_pure (a : α) (h : (pure a).Terminates := pure_terminates a) :
    run (pure a) h = a := by
  unfold run; rfl

end Terminates

section Reachable

namespace StateMachine

/-- `ReachableFrom s` is the set of all states that are reachable from state `s` -/
def ReachableFrom {c : StateMachine α} (s : c.σ) : Set c.σ :=
  { state | ∃ i, c.iterate s i = .inl state }

variable {c : StateMachine α} (s : c.σ)

@[simp] theorem init_mem_reachable : s ∈ ReachableFrom s := Exists.intro 0 rfl
@[simp] theorem mem_reachable_of_next_eq {t u} (h : c t = .inl u) :
    t ∈ ReachableFrom s → u ∈ ReachableFrom s := by
  rintro ⟨n, hn⟩; use n+1; simp [iterate_succ, hn, h]


end StateMachine

/-- `x.ReachableStates` is the set of all states that are reachable from the initial state of `x` -/
def ReachableStates (x : CoroutineM α) : Set x.σ :=
  x.toStateMachine.ReachableFrom x.state

@[simp] theorem state_mem_reachable (x : CoroutineM α) : x.state ∈ x.ReachableStates :=
  Exists.intro 0 rfl

end Reachable


end CoroutineM
