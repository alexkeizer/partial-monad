import PartialMonad.CoroutineM
import PartialMonad.CoroutineM.Bisim

/-!
# Extracting Values From Coroutines

* `CoroutineM.Terminates x` holds if the coroutine `x` terminates in finite time, and
* `CoroutineM.getOfTerminates x h`, which runs `x` until completion, given a proof `h` that this will
    happen in finite time
-/

namespace CoroutineM

/-- `x.iterate n` runs the coroutine for `n` steps -/
def iterate (x : CoroutineM α) : Nat → CoroutineM α ⊕ α
  | 0   => .inl x
  | n+1 => match x.nextState with
      | .inl x' => x'.iterate n
      | .inr a  => .inr a

theorem iterate_succ (x : CoroutineM α) (n : Nat) :
    x.iterate (n+1) = match (x.iterate n) with
      | .inl x => x.nextState
      | .inr a => .inr a := by
  induction n generalizing x
  case zero =>
    simp only [iterate]
    cases x.nextState <;> rfl
  case succ n ih =>
    rw [iterate]
    cases hx : x.nextState
    · simp only; rw [ih, iterate, hx]
    · simp [iterate, hx]

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

/-- If `x'` is the next state of `x`, then we know that `x` takes exactly one more step to terminate
than `x'` -/
theorem minimumStepsToTerminate_le_of_eq {x x' : CoroutineM α}
      (h_eq : x.nextState = .inl x') (h_terminates : x.Terminates) (h_terminates' : x'.Terminates) :
    x.minimumStepsToTerminate h_terminates = x'.minimumStepsToTerminate h_terminates' + 1 := by
  unfold CoroutineM.minimumStepsToTerminate
  have n_spec := h_terminates.choose_spec
  generalize h_terminates.choose = n at *
  have n'_spec := h_terminates'.choose_spec
  generalize h_terminates'.choose = n' at *

  cases n
  case zero => sorry
  case succ n =>
    simp [CoroutineM.minimumStepsToTerminate.go]
    sorry

def getOfTerminates (x : CoroutineM α) (h_terminates : x.Terminates) : α :=
  match h_nextState : x.nextState with
    | .inl x' =>
        have h_terminates' := by
          rcases h_terminates with ⟨n, h⟩
          cases n
          case zero =>
            simp [iterate] at h
          case succ n =>
            simp [iterate, h_nextState] at h
            exact ⟨_, h⟩
        have :  x'.minimumStepsToTerminate h_terminates'
                < x.minimumStepsToTerminate h_terminates := by
          simp [minimumStepsToTerminate_le_of_eq h_nextState h_terminates h_terminates']
        x'.getOfTerminates h_terminates'

    | .inr a => a
termination_by x.minimumStepsToTerminate h_terminates

theorem iterate_bisim_of_bisim {x y : CoroutineM α}

theorem getOfTerminates_eq_of_bisim {x y : CoroutineM α} (x_bisim_y : x ≈ y)
    (x_terminates : x.Terminates) (y_terminates : y.Terminates) :
    x.getOfTerminates x_terminates = y.getOfTerminates y_terminates := by
  unfold getOfTerminates nextState
  rcases x_bisim_y with ⟨R, is_bisim, state⟩
  have := is_bisim _ _ state
  stop
  split <;> split <;> (try simp_all)

theorem terminates_of_bisim {x y : CoroutineM α} (x_bisim_y : x ≈ y) :
    x.Terminates → y.Terminates := by
  rintro ⟨n, h⟩

end CoroutineM
