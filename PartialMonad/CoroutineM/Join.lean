import PartialMonad.CoroutineM.Get
import PartialMonad.LawfulCoroutineM

namespace CoroutineM

/-- `join x` collapses a nested coroutine `x : CoroutineM (CoroutineM σ)` into a single
coroutine `CoroutineM α`.
Operationally, `join x` first runs `x` until it yields the inner coroutine,
which is then run until completion as well -/
def join {α : Type u} (x : CoroutineM (CoroutineM α)) : CoroutineM (ULift.{u+1} α) where
  σ := {state : x.σ // ∃ n, x.iterate n = .inl {x with state}}
       ⊕ Σ' (h : x.Terminates),
          let σ' := (x.getOfTerminates h).σ
          σ' × (σ' → σ' ⊕ α)
  -- /-  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  -- | The state of `join x` is the sum of states of the outer state machine `x`, and
  -- | the states of the nested state machine that is yielded by `x`
  -- | However, we don't actually know the type of states that this inner machine has, a-priori.
  -- | So, read "the states of the nested state machine" as:
  -- |   the states of the state machine returned by `x`,
  -- |   assuming that `x` terminates in finite time.
  -- | Then, to actually be able to transition into one of these nested states,
  -- | we have to show that `x` indeed terminates,
  -- | so we track for the states of `x` (on the LHS of the sum)
  -- | that we only enter states which are reachable from `x`'s starting state
  state := .inl ⟨x.state, 0, rfl⟩
  next  := fun
    | .inl ⟨(s : x.σ), hs⟩ =>
      .inl <| match hs' : x.next s with
        | .inl s'    => .inl ⟨s', by
            rcases hs with ⟨n, hs⟩
            refine ⟨n+1, ?_⟩
            simp [iterate_succ, nextState, hs, hs']⟩
        -- ^^^^^^^^ If `x` is still running, continue with the next state of `x`
        | .inr inner =>
        -- ^^^^^^^^ Otherwise, if `x` has completed,
        --          go to the first state of the nested state machine
          have h_x_terminates := by
            rcases hs with ⟨n, hs⟩
            refine ⟨n+1, ?_⟩
            simp [Terminates, iterate_succ, hs, nextState, hs']
          have h_cast : inner.σ = (getOfTerminates x h_x_terminates).σ := by
            stop
            -- rw [hs'] at hs/
            unfold getOfTerminates
            split
            next => exfalso; sorry
            next h =>
              simp only [iterate_succ, hs, nextState, hs'] at h
              -- simp [Sum.map] at h
              change Sum.inr inner = _ at h
              injection h with h
              rw [h]
          .inr <| ⟨h_x_terminates, h_cast ▸ (inner.state, inner.next)⟩
    | .inr ⟨h, s, next⟩ => (next s).map (.inr ⟨h, ·, next⟩) ULift.up

    -- ^^^^^^^^^^^^^^^^^^^^^^ Finally, run `f` until completion, mapping its state into
    --                        the combined sum state each step

end CoroutineM
