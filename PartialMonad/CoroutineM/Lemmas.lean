import PartialMonad.CoroutineM
import PartialMonad.CoroutineM.Comp
import PartialMonad.CoroutineM.Equiv

namespace CoroutineM

section LawfulFunctor

@[simp] lemma map_id (x : CoroutineM α) : x.map id = x := by
  simp only [map]; congr; simp

theorem map_comp (f : α → β) (g : β → γ) (x : CoroutineM α) :
    x.map (g ∘ f) = (x.map f).map g := by
  simp [Functor.map, map]

instance : LawfulFunctor (CoroutineM) where
  map_const := by simp [Functor.mapConst, Functor.map]
  id_map    := map_id
  comp_map  := map_comp

end LawfulFunctor

/-! ## `next` -/
section NextLemmas

theorem iterate_next {x : CoroutineM α} {state} (h_next : x.next x.state = .inl state) :
    ∀ n, iterate {x with state} n = iterate x (n+1) := by
  simp [iterate, h_next]

theorem terminates_iff_of_next {x : CoroutineM α} {state} (h_next : x.next x.state = .inl state) :
    {x with state}.Terminates ↔ x.Terminates := by
  simp only [Terminates, iterate_next h_next]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n+1, hn⟩
  · rintro ⟨⟨⟩|n, hn⟩
    · simp_all
    · exact ⟨n, hn⟩

/-- If `state` is the next state of some coroutine `x`, then running `x` yields the same
result as running the state machine of `x` with `state` -/
theorem run_eq_of_next {x : CoroutineM α} {state} (h_next : x.next x.state = .inl state)
    (x_terminates : x.Terminates)
    (state_terminates : {x with state}.Terminates :=
      terminates_iff_of_next h_next |>.mpr x_terminates) :
    x.run x_terminates = {x with state}.run state_terminates := by
  rw [run]
  simp only
  split
  next state' h_state' =>
    obtain rfl : state' = state := by simpa only [h_state', Sum.inl.injEq] using h_next
    rfl
  next =>
    simp_all

theorem next_equiv {x : CoroutineM α} {state : x.σ} (h : x.next x.state = .inl state) :
    {x with state} ≈ x := by
  by_cases x.Terminates
  case pos x_terminates =>
    have state_terminates : Terminates {x with state} := by
      simp_all [terminates_iff_of_next]
    apply Equiv.terminates state_terminates x_terminates
    exact (run_eq_of_next h x_terminates state_terminates).symm
  case neg h_non_terminates =>
    apply Equiv.non_terminates _ h_non_terminates
    simp_all [terminates_iff_of_next]

end NextLemmas

section RunLemmas

/-- If a coroutine `x` terminates, yielding some value `a`, then `x` is equivalent to `pure a` -/
theorem pure_run_equiv (x : CoroutineM α) (h : x.Terminates) :
    pure (x.run h) ≈ x := by
  apply Equiv.terminates (pure_terminates _) h (run_pure _)

theorem terminates_of_equiv {x y : CoroutineM α} (h_eqv : x ≈ y) :
    x.Terminates → y.Terminates := by
  intro h_terminates
  cases h_eqv
  · assumption
  · contradiction

end RunLemmas

/-! ## Lemmas about `Equiv` -/
namespace Equiv


end Equiv


section LawfulApplicative
/-!
`CoroutineM` is not a lawful applicative. We can see this when trying to prove `pure_seq`, i.e.,
  `(pure f) <*> x = f <$> x`
In fact, the `pure` inserts a single new state, so after `simp`ing all definitions, we are left
with a proof obligation that `HEq (.inl ()) x.state`, which is clearly not true in general.

Instead, we will now show that the desired equalities hold up to `Equiv` -/

@[simp] lemma pure_comp (a : α) (y : StateMachine β) (f : α → y.σ) :
    comp (pure a) y f ≈ ⟨y, f a⟩ := by
  -- have : (comp (pure a) y f).next (comp (pure a) y f).state = .inl (.inr (f a)) :=
  --   rfl
  trans {(comp (pure a) y f) with state := .inr (f a)}
  · apply Equiv.symm
    apply next_equiv
    rfl
  · sorry

@[simp] lemma pure_seq (f : α → β) (x : CoroutineM α) :
    seq (pure f) x ≈ f <$> x := by
  simp [seq]
  apply Equiv.trans (pure_comp ..)
  sorry


-- instance : LawfulApplicative (CoroutineM) where
--   seqLeft_eq  := by simp [SeqLeft.seqLeft, Seq.seq]
--   seqRight_eq := by simp [SeqRight.seqRight, Seq.seq]
--   pure_seq  := by
--     intro α β f x
--     simp [Seq.seq, seq, Pure.pure, pure, comp, Functor.map, map]

--   map_pure  := sorry
--   seq_pure  := sorry
--   seq_assoc := sorry

end LawfulApplicative
