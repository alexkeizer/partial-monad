import PartialMonad.CoroutineM

/-!
# Extracting Values From Coroutines

* `CoroutineM.Terminates x` holds if the coroutine `x` terminates in finite time, and
* `CoroutineM.run x h`, which runs `x` until completion, given a proof `h` that this will
    happen in finite time
-/

namespace CoroutineM

/-- `x.iterate n` runs the coroutine for `n` steps -/
def iterate (x : CoroutineM α) : Nat → CoroutineM α ⊕ α
  | 0   => .inl x
  | n+1 => match x.nextState with
      | .inl x' => x'.iterate n
      | .inr a  => .inr a

@[simp] theorem iterate_zero (x : CoroutineM α) : x.iterate 0 = .inl x := rfl
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

theorem iterate_succ_of_nextState_eq_inl {x : CoroutineM α} (h : x.nextState = .inl y) :
    x.iterate (n+1) = y.iterate n := by
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
theorem iterate_minimumStepsToTerminate (x : CoroutineM α) (h : x.Terminates) :
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
theorem minimumStepsToTerminate_eq_succ_of_nextState {x x' : CoroutineM α}
      (h_eq : x.nextState = .inl x') (h_terminates : x.Terminates) (h_terminates' : x'.Terminates) :
    x.minimumStepsToTerminate h_terminates = x'.minimumStepsToTerminate h_terminates' + 1 := by
  have isLeft_pred_n := iterate_minimumStepsToTerminate_pred x h_terminates
  have isRight_iterate_x_n := iterate_minimumStepsToTerminate x h_terminates
  generalize x.minimumStepsToTerminate h_terminates = n at *

  have isLeft_pred_n' := iterate_minimumStepsToTerminate_pred x' h_terminates'
  have isRight_iterate_x'_n' := iterate_minimumStepsToTerminate x' h_terminates'
  generalize x'.minimumStepsToTerminate h_terminates' = n' at *

  cases n
  case zero => simp_all
  case succ n =>
  simp only [Nat.succ.injEq]

  rcases Nat.lt_trichotomy n n' with lt|eq|gt
  case inr.inl => exact eq
  · exfalso
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt lt
    simp only [Nat.pred_succ, iterate_succ_of_nextState_eq_inl h_eq] at *
    have := iterate_isLeft_of_add _ isLeft_pred_n'
    revert this isRight_iterate_x_n
    cases iterate x' n <;> simp
  · exfalso
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt gt
    have : n' + 1 + m = (n' + m) + 1 := by omega
    simp only [Nat.pred_succ, this, iterate_succ_of_nextState_eq_inl h_eq] at *
    have := iterate_isLeft_of_add _ isLeft_pred_n
    revert this isRight_iterate_x'_n'
    cases iterate x' n' <;> simp

/-- We can soundly run a coroutine until completion, given a proof that it will terminate in finite
time -/
def run (x : CoroutineM α) (h_terminates : x.Terminates) : α :=
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
          simp [minimumStepsToTerminate_eq_succ_of_nextState h_nextState h_terminates h_terminates']
        x'.run h_terminates'

    | .inr a => a
termination_by x.minimumStepsToTerminate h_terminates

#print axioms run -- `sorry`-free, yay!

end CoroutineM
