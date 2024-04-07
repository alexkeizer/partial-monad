import PartialMonad.CoroutineM
import Mathlib.Data.Set.Basic

/-!
# Extracting Values From Coroutines

* `CoroutineM.Terminates x` holds if the coroutine `x` terminates in finite time, and
* `CoroutineM.run x h`, which runs `x` until completion, given a proof `h` that this will
    happen in finite time
-/

namespace CoroutineM

-- TODO: probbaly we want `iterate` and `nextState` to return just the state (`x.σ`),
--       instead of the whole `CoroutineM`

/-- `x.iterate n` runs the coroutine for `n` steps -/
def iterate (x : CoroutineM α) : Nat → x.σ ⊕ α
  | 0   => .inl x.state
  | n+1 => match x.next x.state with
      | .inl state => iterate {x with state} n
      | .inr a     => .inr a

@[simp] theorem iterate_zero (x : CoroutineM α) : x.iterate 0 = .inl x.state := rfl
theorem iterate_succ (x : CoroutineM α) (n : Nat) :
    x.iterate (n+1) = match (x.iterate n) with
      | .inl s => x.next s
      | .inr a => .inr a := by
  rw [show x = ⟨⟨x.next⟩, x.state⟩ from rfl]; simp only
  generalize x.state = state
  induction n generalizing state
  case zero =>
    simp only [iterate]; cases x.next state <;> rfl
  case succ n ih =>
    rw [iterate]
    simp
    cases hx : x.next state
    case inl state' =>
      simp only; rw [ih state', iterate, hx]; simp only
      cases (iterate ⟨⟨x.next⟩, state'⟩ n) <;> rfl
    case inr _ =>
      simp [iterate, hx]

theorem iterate_succ_of_next_eq_inl {x : CoroutineM α} {state'}
    (h : x.next x.state = .inl state') :
    x.iterate (n+1) = {x with state := state'}.iterate n := by
  rw [iterate, h]

def Terminates (x : CoroutineM α) : Prop :=
  ∃ n, (x.iterate n).isRight

/-- `x.minimumStepsToTerminate h` is the smallest number `n`, such that `x` terminates in `n` steps -/
protected noncomputable def minimumStepsToTerminate (x : CoroutineM α) (h : x.Terminates)  : Nat :=
  go h.choose
where go : Nat → Nat
  | 0 => 0
  | n+1 => match x.iterate n with
    | .inl _ => n+1
    --^^^^^^ `x` does *not* terminate in `n` steps, so `n+1` is the minimum
    | .inr _ => go n
    --^^^^^^ `x` still terminates in `n` steps, so try to minimize further

theorem minimumStepsToTerminate_pos (x : CoroutineM α) (h : x.Terminates) :
    0 < x.minimumStepsToTerminate h := by
  unfold CoroutineM.minimumStepsToTerminate
  have n_spec := h.choose_spec
  generalize h.choose = n at *

  induction n
  case zero => simp at n_spec
  case succ n ih =>
    simp [minimumStepsToTerminate.go]
    cases hx : x.iterate n
    · simp
    · apply ih
      simp [hx]

/-- Iterating for the minimum steps to terminate does in fact yield a result -/
theorem iterate_minimumStepsToTerminate_isRight (x : CoroutineM α) (h : x.Terminates) :
    (x.iterate <| x.minimumStepsToTerminate h).isRight := by
  unfold CoroutineM.minimumStepsToTerminate
  have n_spec := h.choose_spec
  generalize h.choose = n at *
  induction n
  case zero => simp at n_spec
  case succ n ih =>
    simp [iterate_succ] at n_spec
    simp [minimumStepsToTerminate.go]
    cases h_iterate_n : x.iterate n
    case inr => simpa [h_iterate_n] using ih
    case inl => simpa [iterate_succ, h_iterate_n] using n_spec

/-- Iterating one step less than the minimum will yield a still-in-progress coroutine, i.e., the
function really does compute the *minimum* steps to terminate -/
theorem iterate_minimumStepsToTerminate_pred (x : CoroutineM α) (h : x.Terminates) :
    (x.iterate <| Nat.pred <| x.minimumStepsToTerminate h).isLeft := by
  unfold CoroutineM.minimumStepsToTerminate
  have n_spec := h.choose_spec
  generalize h.choose = n at *
  induction n
  case zero => simp at n_spec
  case succ n ih =>
    simp [minimumStepsToTerminate.go]
    cases hx : x.iterate n
    · simp [hx]
    · apply ih; simp [hx]

/-- If iterating `n+m` times is not enough to complete a coroutine, then in particular `n` steps
are not enough -/
theorem iterate_isLeft_of_add {x : CoroutineM α} {n} (m) :
    (x.iterate (n + m)).isLeft → (x.iterate n).isLeft := by
  intro h
  induction m
  case zero => exact h
  case succ m ih =>
    apply ih
    change Sum.isLeft (iterate x ((n+m) + 1)) at h
    rw [iterate_succ] at h
    cases hx : x.iterate (n+m)
    · simp
    · simp [hx] at h

/-- Iterating less than the minimum will yield a still-in-progress coroutine -/
theorem iterate_isLeft_of_le_minimumStepToTerminate {x : CoroutineM α} {h : x.Terminates} {n} :
    (n < x.minimumStepsToTerminate h) → (x.iterate n).isLeft := by
  intro h_lt
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h_lt
  apply iterate_isLeft_of_add k
  show (x.iterate <| Nat.pred <| n+k+1).isLeft
  rw [←hk]
  apply iterate_minimumStepsToTerminate_pred

/-- If `x'` is the successor state of `x`, then we know that `x` takes exactly one more step to
terminate than `x'` -/
theorem minimumStepsToTerminate_eq_succ_of_next {x : CoroutineM α} {state' : x.σ}
      (h_eq : x.next x.state = .inl state')
      (h_terminates : x.Terminates) (h_terminates' : {x with state := state'}.Terminates) :
    x.minimumStepsToTerminate h_terminates
    = {x with state := state'}.minimumStepsToTerminate h_terminates' + 1 := by
  have isLeft_pred_n := iterate_minimumStepsToTerminate_pred x h_terminates
  have isRight_iterate_x_n := iterate_minimumStepsToTerminate_isRight x h_terminates
  generalize h : x.minimumStepsToTerminate h_terminates = n at *


  have isLeft_pred_n' := iterate_minimumStepsToTerminate_pred _ h_terminates'
  have isRight_iterate_x'_n' := iterate_minimumStepsToTerminate_isRight _ h_terminates'
  generalize CoroutineM.minimumStepsToTerminate _ h_terminates' = n' at *

  cases n
  case zero => simp_all
  case succ n =>
  simp only [Nat.succ.injEq]

  rcases Nat.lt_trichotomy n n' with lt|eq|gt
  case inr.inl => exact eq
  · exfalso
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt lt
    simp only [Nat.pred_succ, iterate_succ_of_next_eq_inl h_eq] at *
    have := iterate_isLeft_of_add _ isLeft_pred_n'
    revert this isRight_iterate_x_n
    cases iterate ⟨⟨x.next⟩, state'⟩ n <;> simp
  · exfalso
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt gt
    have : n' + 1 + m = (n' + m) + 1 := by omega
    simp only [Nat.pred_succ, this, iterate_succ_of_next_eq_inl h_eq] at *
    have := iterate_isLeft_of_add _ isLeft_pred_n
    revert this isRight_iterate_x'_n'
    cases iterate ⟨⟨x.next⟩, state'⟩ n' <;> simp

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
            simp [iterate] at h
          case succ n =>
            simp [iterate, h_nextState] at h
            exact ⟨_, h⟩
        have : x'.minimumStepsToTerminate h_terminates'
                < x.minimumStepsToTerminate h_terminates := by
          simp [minimumStepsToTerminate_eq_succ_of_next h_nextState h_terminates h_terminates']
        x'.run h_terminates'

    | .inr a => a
termination_by x.minimumStepsToTerminate h_terminates

#print axioms run -- `sorry`-free, yay!

theorem iterate_minimumStepsToTerminate {x : CoroutineM α} (h) :
    x.iterate (x.minimumStepsToTerminate h) = .inr (x.run h) := by
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

/-- If we can show that iterating a coroutine for some number of steps yiels a result `a`, then
running that coroutine until completion yields that same result -/
theorem run_eq_of_iterate_eq_inr {x : CoroutineM α} {n} {a} (h : x.iterate n = .inr a)
    (x_terminates : x.Terminates := ⟨n, by simp [h]⟩) :
    x.run x_terminates = a := by
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

/-- `x.ReachableStates` is the set of all states that are reachable from the initial state of `x` -/
def ReachableStates (x : CoroutineM α) : Set x.σ :=
  { state | ∃ i, x.iterate i = .inl state }

@[simp] theorem state_mem_reachable (x : CoroutineM α) : x.state ∈ x.ReachableStates :=
  Exists.intro 0 rfl

end Reachable

end CoroutineM
