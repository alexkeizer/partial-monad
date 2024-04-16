import PartialMonad.CoroutineM
import PartialMonad.CoroutineM.Run

/-!
This file establishes a notion of bisimilarity on `CoroutineM`, and shows that is an equivalence
relation

> [!WARNING]
> This file is flawed: `Bisim` does **not** treat the computation steps as internal, instead
> it only treats computations that complete in the same number of steps as equal.
> This is not what we want.
>
> Although, by carefully making sure we never add computation steps, we might still be able to
> make this lawful? Regardless, I'm exploring an alternative equivalence in `Equiv` now.

-/

namespace CoroutineM

/-!
# Bisimilarity
We define what it means for two coroutine states to be bisimilar
-/
section BisimDef

/-- We say that two results `sa₁ : σ₁ ⊕ α` and `sa₂ : σ₂ ⊕ α` *immediately* agree up-to `R`, if
they are both `.inr a`, for the same `a : α`, or they are both `.inl _`, for two states `s₁` and
`s₂` which are related by `R` -/
inductive ImmediatelyAgreesUpTo (R : σ₁ → σ₂ → Prop) : σ₁ ⊕ α → σ₂ ⊕ α → Prop
  | inr {a} : ImmediatelyAgreesUpTo R (.inr a) (.inr a)
  | inl {s₁ s₂} : R s₁ s₂ → ImmediatelyAgreesUpTo R (.inl s₁) (.inl s₂)

/-
> [!NOTE]
> Turns out we can't really do `cases` on `h : ImmediatelyAgreesUpTo R ...`: we usually just
> get a dependent elimination failed error.
>
> I tried an alternative `match`-based `def`inition, in the hopes that `split` might be able to make
> sense of it. Alas, even with the following definition, `split` also failed:
> ```
> def ImmediatelyAgreesUpTo (R : σ₁ → σ₂ → Prop) : σ₁ ⊕ α → σ₂ ⊕ α → Prop
>   | .inr a  => (· = .inr a)
>   | .inl s₁ => fun
>       | .inr _  => False
>       | .inl s₂ => R s₁ s₂
> ```
-/

/-- We say that two *states* `s₁` and `s₂` agree up-to some relation `R`, when there exists
`n, m > 0`, such that iterating the coroutines for `n`, resp. `m`, steps yield a result which
immediately agrees up-to `R`. -/
abbrev AgreesUpTo {c₁ c₂ : StateMachine α} (R : c₁.σ → c₂.σ → Prop) (s₁) (s₂) :=
  ∃ n m, ImmediatelyAgreesUpTo R (c₁.iterate s₁ (n+1)) (c₂.iterate s₂ (m+1))

/-- A relation `R` is a bisimulation, if every related pair agrees up-to `R` -/
def IsBisimulation {c₁ c₂ : StateMachine α} (R : c₁.σ → c₂.σ → Prop) : Prop :=
  ∀ (s₁ : c₁.σ) (s₂ : c₂.σ), R s₁ s₂ → AgreesUpTo R s₁ s₂

def Bisimulation (c₁ c₂ : StateMachine α) : Type :=
  { R : c₁.σ → c₂.σ → Prop // IsBisimulation R }

/-- Ensure we can use `R : Bisimulation` as a relation, so that we can write `R s₁ s₂` -/
instance : CoeFun (Bisimulation c₁ c₂) (fun _ => c₁.σ → c₂.σ → Prop) where
  coe := fun ⟨R, _⟩ => R

/-- Two states are bisimilar, if there exists some bisimulation thet relates them -/
def StateMachine.Bisim {c₁ c₂ : StateMachine α} (s₁ : c₁.σ) (s₂ : c₂.σ) : Prop :=
  ∃ (R : Bisimulation c₁ c₂), R s₁ s₂

scoped infixl:70 " ~ₛ " => StateMachine.Bisim

/-- Two coroutines are bisimilar, if their current states are bisimilar -/
abbrev Bisim (x y : CoroutineM α) : Prop :=
  x.state ~ₛ y.state

scoped infixl:70 " ~ " => Bisim

/-- If two states are bisimlar, they in particular agree up to bisimilarity -/
def StateMachine.Bisim.agreesUpTo_bisim  {c₁ c₂ : StateMachine α} {s₁ : c₁.σ} {s₂ : c₂.σ} :
    s₁ ~ₛ s₂ → AgreesUpTo Bisim s₁ s₂ := by
  rintro ⟨⟨R, R_spec⟩, h_R⟩
  rcases R_spec _ _ h_R with ⟨n, m, h_agrees⟩
  use n, m
  revert h_agrees
  cases c₁.iterate s₁ (n+1) <;> cases c₂.iterate s₂ (m+1)
  <;> rintro ⟨⟩ <;> constructor
  use ⟨R, R_spec⟩

end BisimDef

/-! `Bisim` is an equivalence -/
section BisimIsEquiv

/-- If `R` is reflexive, then `ImmediatelyAgreesUpTo R` is also reflexive -/
lemma ImmediatelyAgreesUpTo.rfl {c : StateMachine α} {R} (h : ∀ a, R a a) (s : c.σ ⊕ α) :
    ImmediatelyAgreesUpTo R s s := by
  cases s <;> constructor
  exact h _
/-- If `R` is reflexive, then `AgreesUpTo R` is also reflexive -/
lemma AgreesUpTo.rfl {c : StateMachine α} {R} (h : ∀ a, R a a) (s : c.σ) : AgreesUpTo R s s := by
  exact ⟨0, 0, ImmediatelyAgreesUpTo.rfl h ..⟩

/-- If `Q` is implied by `R`, then `AgreesUpTo Q` is implied by `AgreesUpTo R`  -/
lemma AgreesUpTo.of_imp {c₁ c₂ : StateMachine α} {R Q : c₁.σ → c₂.σ → Prop} :
    (∀ s₁ s₂, R s₁ s₂ → Q s₁ s₂) → (∀ {s₁ s₂}, AgreesUpTo R s₁ s₂ → AgreesUpTo Q s₁ s₂) := by
  rintro h_imp s₁ s₂ ⟨n, m, h_agrees_R⟩
  use n, m
  revert h_agrees_R
  cases c₁.iterate s₁ (n+1) <;> cases c₂.iterate s₂ (m+1)
  <;> rintro ⟨⟩ <;> constructor
  apply h_imp; assumption

/-- `Eq` is a bisimulation -/
def Bisimulation.Eq (c : StateMachine σ) : Bisimulation c c :=
  ⟨(· = ·), by simp only [IsBisimulation, forall_eq', implies_true, AgreesUpTo.rfl]⟩

open StateMachine in
/-- The transitive closure of two bisimulations `R₁` and `R₂` is also a bisimulation -/
def Bisimulation.trans (R₁ : Bisimulation c₁ c₂) (R₂ : Bisimulation c₂ c₃) : Bisimulation c₁ c₃ :=
  let R := fun s₁ s₃ =>
    ∃ s₂ s₂' n,
      (c₂.iterate s₂ n = .inl s₂' ∨ c₂.iterate s₂' n = .inl s₂)
      ∧ R₁ s₁ s₂ ∧ R₂ s₂' s₃
  ⟨R, by
    intro s₁ s₃
    rcases R₁ with ⟨R₁, is_bisim₁⟩
    rcases R₂ with ⟨R₂, is_bisim₂⟩
    simp only [forall_exists_index, and_imp]
    rintro s₂ t₂ m_st s₂_eq_iter_s₂ hR₁ hR₂

    have ⟨n_s₁, n_s₂, agree₁⟩ := is_bisim₁ _ _ hR₁
    have ⟨n_t₂, n_s₃, agree₂⟩ := is_bisim₂ _ _ hR₂
    use n_s₁, n_s₃

    suffices
      (∃ a, c₁.iterate s₁ (n_s₁ + 1) = .inr a ∧ c₃.iterate s₃ (n_s₃ + 1) = .inr a)
      ∨ (∃ s₁' s₃', c₁.iterate s₁ (n_s₁ + 1) = .inl s₁' ∧ c₃.iterate s₃ (n_s₃ + 1) = .inl s₃')
    by
      rcases this with ⟨a, h₁, h₃⟩|⟨s₁', s₃', h₁, h₃⟩
      · simp only [h₁, h₃]; constructor
      · simp only [h₁, h₃] at *; constructor;
        rcases s₂_eq_iter_s₂ with h₂|h₂
        case' inl =>
          generalize n_s₂ + 1 = a at *
          generalize n_t₂ + 1 = b at *

        · have it_zero (s) : Sum.inl s = c₂.iterate s 0 := rfl
          have : c₂.iterate t₂ b = c₂.iterate t₂ (0 + b) := by ac_rfl
          conv_rhs at this =>
            rw [iterate_add, ←it_zero, ←h₂, ←iterate_add]
          simp [this] at *

          rcases h_iter_s₂_m₁ : c₂.iterate s₂ (a) with u₁|_
          <;> cases (h_iter_s₂_m₁ ▸ agree₁)
          rcases h_iter_s₂_n₂ : c₂.iterate s₂ (m_st + b) with u₂|_
          <;> cases (h_iter_s₂_n₂ ▸ agree₂)

          obtain ⟨m_tt, h_st'⟩ : ∃ n, c₂.iterate u₁ n = .inl u₂ ∨ c₂.iterate u₂ n = .inl u₁ := by
            rcases lt_or_le (a) (m_st + b) with lt|le
            · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt lt
              use k+1
              rw [hk, show a + k + 1 = (a) + _ by ac_rfl,
                iterate_add _ _ (a), h_iter_s₂_m₁] at h_iter_s₂_n₂
              exact Or.inl h_iter_s₂_n₂
            · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le le
              use k
              rw [hk, iterate_add _ _ (m_st + b), h_iter_s₂_n₂] at h_iter_s₂_m₁
              exact Or.inr h_iter_s₂_m₁

          exact ⟨u₁, u₂, m_tt, h_st', ‹R₁ _ u₁›, ‹R₂ u₂ _›⟩

        · have it_zero (s) : Sum.inl s = c₂.iterate s 0 := rfl
          have : c₂.iterate s₂ (n_s₂ + 1) = c₂.iterate s₂ (0 + (n_s₂ + 1)) := by ac_rfl
          conv_rhs at this =>
            rw [iterate_add, ←it_zero, ←h₂, ←iterate_add]
          simp [this] at *

          rcases h_iter_t₂_₁ : c₂.iterate t₂ _ with u₁|_
          <;> cases (h_iter_t₂_₁ ▸ agree₁)
          rcases h_iter_t₂_₂ : c₂.iterate t₂ _ with u₂|_
          <;> cases (h_iter_t₂_₂ ▸ agree₂)

          obtain ⟨m_tt, h_st'⟩ : ∃ n, c₂.iterate u₁ n = .inl u₂ ∨ c₂.iterate u₂ n = .inl u₁ := by
            rcases lt_or_le (n_t₂ + 1) (m_st + (n_s₂ + 1)) with lt|le
            · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt lt
              use k+1
              rw [hk, show n_t₂ + 1 + k + 1 = (n_t₂ + 1) + _ by ac_rfl,
                iterate_add _ _ (n_t₂ + 1), h_iter_t₂_₂] at h_iter_t₂_₁
              exact Or.inr h_iter_t₂_₁
            · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le le
              use k
              rw [hk, iterate_add _ _ (m_st + (n_s₂ + 1)), h_iter_t₂_₁] at h_iter_t₂_₂
              exact Or.inl h_iter_t₂_₂

          exact ⟨u₁, u₂, m_tt, h_st', ‹R₁ _ u₁›, ‹R₂ u₂ _›⟩

    rcases h_iter₁ : c₁.iterate s₁ (n_s₁ + 1) with s₁'|a₁
      <;> rcases h_iter₃ : c₃.iterate s₃ (n_s₃ + 1) with s₃'|a₃
      <;> simp [h_iter₁, h_iter₃] at agree₁ agree₂
      <;> (try rcases agree₁ with ⟨agree₁⟩)
      <;> (try rcases agree₂ with ⟨agree₂⟩)
      <;> simp

    stop

    rcases Nat.lt_trichotomy n₂ m₁ with h_lt|rfl|h_gt
    case' inl =>
      obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_lt h_lt; clear h_lt
      rw [show n₂ + l + 2  = (n₂ + 1) + (l + 1) by ac_rfl, iterate_add _ _ (n₂ + 1)] at agree₁
      rcases h_iter₂ : c₂.iterate s₂ (n₂ + 1) with s₂'|a₂
      <;> simp [h_iter₂] at agree₁ agree₂
    case' inr.inr =>
      obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_lt h_gt; clear h_gt
      rw [show m₁ + l + 2  = (m₁ + 1) + (l + 1) by ac_rfl, iterate_add _ _ (m₁ + 1)] at agree₂
      rcases h_iter₂ : c₂.iterate s₂' (m₁ + 1) with t₁|a₂
      <;> simp [h_iter₂] at agree₁ agree₂

    all_goals

      -- <;> (
      --   first
      --   | rcases h_iter₂ : c₂.iterate s₂ (n₂ + 1) with s₂'|a₂
      --     <;> simp [h_iter₂] at agree₁ agree₂
      --     <;> rcases agree₂ with ⟨hR⟩
      --     sorry
      --   | sorry
      -- )
    · rcases h_iter₂ : c₂.iterate s₂ (m₁ + 1) with s₂'|a₂
      <;> simp [h_iter₂] at agree₁ agree₂
      <;> rcases agree₂ with ⟨hR⟩
      rcases h_iter₂' : c₂.iterate t₁ (l+1) with t₂|a₂'
      <;> simp [h_iter₂'] at agree₂
      <;> cases agree₂
      apply Or.inr
      suffices R s₁' s₃' by simpa
      use s₂
      use t₁
      simp_all

    all_goals sorry
  ⟩


/-- The inverse `R⁻¹ := { (y, x) | x R y }` of a bisimulation `R` is still a bisimulation -/
def Bisimulation.inv (R : Bisimulation c₁ c₂) : Bisimulation c₂ c₁ :=
  ⟨fun x y => R y x, by
    intros s₂ s₁ hR
    have ⟨n, m, agrees⟩ := R.prop _ _ hR;
    rcases R with ⟨R, _⟩
    use m, n
    revert agrees
    simp only
    cases c₁.iterate s₁ (n+1) <;> cases c₂.iterate s₂ (m+1)
    <;> rintro ⟨bisim⟩
    <;> constructor
    assumption
  ⟩

namespace StateMachine.Bisim

variable {c c₁ c₂ c₃ : StateMachine α}

@[refl]
theorem rfl (s : c.σ) : s ~ₛ s :=
  ⟨.Eq _, by rfl⟩

@[trans]
theorem trans {x : c₁.σ} {y : c₂.σ} {z : c₃.σ}  :
    x ~ₛ y → y ~ₛ z → x ~ₛ z
  | ⟨R₁, state₁⟩, ⟨R₂, state₂⟩ => ⟨R₁.trans R₂, Exists.intro y ⟨state₁, state₂⟩⟩

@[symm]
theorem symm {x : c₁.σ} {y : c₂.σ} : Bisim x y → Bisim y x
  | ⟨R, state⟩ => ⟨R.inv, state⟩

end StateMachine.Bisim

namespace Bisim

open StateMachine.Bisim in
theorem is_equivalence : Equivalence (@Bisim α) where
  refl x := rfl x.state
  trans := trans
  symm := symm

end Bisim

/-- The canonical equality on coroutines is bisimilarity -/
instance setoid (α : Type _) : Setoid (CoroutineM α) where
  r := Bisim
  iseqv := Bisim.is_equivalence

end BisimIsEquiv

/-! Furthermore, two coroutines `x` and `y` are bisimilar iff:
  * Neither `x` nor `y` terminates, or
  * Both `x` and `y` terminate, yielding the same value `a : α` -/
section BisimIffEquiv

namespace StateMachine

variable {c c₁ c₂ : StateMachine α} {s : c.σ} {s₁ : c₁.σ} {s₂ : c₂.σ}

/-- All non-terminating states are bisimilar -/
theorem bisim_of_non_terminates (h₁ : ¬c₁.StateTerminates s₁) (h₂ : ¬c₂.StateTerminates s₂) :
    s₁ ~ₛ s₂ := by
  use ⟨fun t₁ t₂ => t₁ ∈ ReachableFrom s₁ ∧ t₂ ∈ ReachableFrom s₂, ?_⟩
  · simp
  · intro t₁ t₂ ⟨h_t₁, h_t₂⟩
    use 0, 0
    simp only [iterate]
    -- Now, our goal mentions `cᵢ.next tᵢ`.
    -- We know this term to be `.inl sᵢ'`, for some state `sᵢ'`; let's make that argument

    have ⟨i₁, h_iter₁⟩ := Set.mem_setOf.mp h_t₁
    have ⟨i₂, h_iter₂⟩ := Set.mem_setOf.mp h_t₂
    simp only [StateTerminates, not_exists, Bool.not_eq_true, Sum.isRight_eq_false] at h₁ h₂
    specialize h₁ (i₁ + 1)
    specialize h₂ (i₂ + 1)
    simp only [iterate_succ, h_iter₁, h_iter₂] at h₁ h₂

    -- Lets introduce new variables for these intermediate states `sᵢ'`
    cases' h_next₁ : c₁.next t₁ with u₁; case inr => simp [h_next₁] at h₁
    cases' h_next₂ : c₂.next t₂ with u₂; case inr => simp [h_next₂] at h₂
    simp only

    -- Then, we show that these new states are indeed reachable from our intial states
    constructor
    simp only [ReachableFrom, Set.mem_setOf_eq]
    refine ⟨⟨i₁+1, ?_⟩, ⟨i₂+1, ?_⟩⟩
    <;> simp [iterate_succ, *]
-- QED

/-- If two states result in the same final result, they are bisimilar -/
theorem bisim_of_iterate_eq_inr {n m}
    (h₁ : c₁.iterate s₁ n = .inr a) (h₂ : c₂.iterate s₂ m = .inr a) :
    s₁ ~ₛ s₂ := by
  use ⟨fun t₁ t₂ => s₁ = t₁ ∧ s₂ = t₂, ?_⟩
  rintro _ _ ⟨rfl, rfl⟩
  use n, m
  simpa [iterate_succ, h₁, h₂] using .inr

/-- Any states that agree up-to a bisimulation are in fact bisimilar -/
lemma bisim_of_agrees {R : Bisimulation c₁ c₂} :
    AgreesUpTo R s₁ s₂ → (s₁ ~ₛ s₂) := by
  rcases R with ⟨R, R_bisim⟩
  simp only
  intro h_agrees
  let Q := fun t₁ t₂ => R t₁ t₂ ∨ (s₁ = t₁ ∧ s₂ = t₂)
  use ⟨Q, ?_⟩
  · simp [Q]
  · intro t₁ t₂ hQ
    have R_imp_Q : ∀ t₁ t₂, R t₁ t₂ → Q t₁ t₂ := by
      intro _ _; exact Or.intro_left _
    apply AgreesUpTo.of_imp R_imp_Q
    rcases hQ with hR|⟨rfl, rfl⟩
    · exact R_bisim _ _ hR
    · exact h_agrees

/-- Every state is bisimilar to it's successor -/
lemma bisim_next (h_next : c s = .inl s') :
    s ~ₛ s' := by
  let R := fun (t t' : c.σ) => t = t' ∨ c t = .inl t'
  use ⟨R, ?_⟩
  · exact Or.inr h_next
  · rintro t t' (rfl|h_next)
    · apply AgreesUpTo.rfl
      simp [R]
    · use 1, 0
      rw [iterate, h_next]
      simpa using ImmediatelyAgreesUpTo.rfl (by simp [R]) _

lemma bisim_iterate (h_iterate : c.iterate s n = .inl s') :
    s ~ₛ s' := by
  induction n generalizing s'
  case zero => simp_all; rfl
  case succ n ih =>
    simp [iterate_succ] at h_iterate
    split at h_iterate
    case h_2 => contradiction
    case h_1 t h_iterate_eq_t =>
      apply Bisim.trans (y:=t)
      · exact ih h_iterate_eq_t
      · exact bisim_next h_iterate

/-- Any pair of states reachable from a pair of bisimilar states
(in a possibly different number of steps for either state machine)
is again bisimilar.
Therefore, bisimulation is preserved by (arbitrary!) iteration -/
lemma bisim_iterate_iterate_of_bisim (h_bisim : s₁ ~ₛ s₂) {n m : Nat}
    (h_iterate₁ : c₁.iterate s₁ n = .inl s₁') (h_iterate₂ : c₂.iterate s₂ m = .inl s₂') :
    s₁' ~ₛ s₂' := by
  apply Bisim.trans (y:=s₁)
  · symm; exact bisim_iterate h_iterate₁
  · apply Bisim.trans (y:=s₂)
    · exact h_bisim
    · exact bisim_iterate h_iterate₂

/-- If a state `s` terminates, yielding value `a`, then there must be some last state,
reachable from `s`, such that `c s` returns that same value `a` -/
lemma final_state {c : StateMachine α} {s n a} :
    c.iterate s n = .inr a → ∃ s' n', c.iterate s n' = .inl s' ∧ c s' = .inr a := by
  intro h_iter
  induction n
  case zero => contradiction
  case succ n ih =>
    cases h_iter' : c.iterate s n <;> simp only [iterate_succ, h_iter'] at h_iter
    case inl s' => exact ⟨s', n, h_iter', h_iter⟩
    case inr a' => simp_all only [exists_and_right, forall_true_left, Sum.inr.injEq]

/-- Any final result reachable from a pair of bisimlar states, must be equal -/
lemma eq_of_bisim_iterate_eq_inr (h_bisim : s₁ ~ₛ s₂) {n m : Nat} {a b : α}
    (h_iterate₁ : c₁.iterate s₁ n = .inr a) (h_iterate₂ : c₂.iterate s₂ m = .inr b) :
    a = b := by
  have ⟨s₁', n', h_iterate_n', h_s₁'⟩ := final_state h_iterate₁
  have ⟨s₂', m', h_iterate_m', h_s₂'⟩ := final_state h_iterate₂
  have ⟨k, l, h_agrees⟩ :=
    bisim_iterate_iterate_of_bisim h_bisim h_iterate_n' h_iterate_m' |>.agreesUpTo_bisim
  simp only [iterate, h_s₁', h_s₂'] at h_agrees
  cases h_agrees
  rfl

/-- Given bisimilar states `s₁` and `s₂`, if `s₁` returns some value `a` in finite time, then there
must be some number of steps `m` after which `s₂` returns that same value `a` -/
lemma of_bisim_iterate_eq_inr (h_bisim : s₁ ~ₛ s₂) {n : Nat} {a : α} :
    c₁.iterate s₁ n = .inr a → ∃ m, c₂.iterate s₂ m = .inr a := by
  intro h_iterate₁
  have ⟨s₁', n', h_iterate_n', h_s₁'⟩ := final_state h_iterate₁
  have h_iterate₂ : c₂.iterate s₂ 0 = .inl s₂ := rfl
  have ⟨k, l, h_agrees⟩ :=
    bisim_iterate_iterate_of_bisim h_bisim h_iterate_n' h_iterate₂ |>.agreesUpTo_bisim
  conv at h_agrees in (iterate ..) => simp only [iterate, h_s₁']
  revert h_agrees; cases h_iterate_l : c₂.iterate s₂ (l+1) <;> rintro ⟨⟩
  exact ⟨_, h_iterate_l⟩

/-- If two states `s₁` and `s₂` are bisimilar, then `s₁` terminates iff `s₂` terminates -/
lemma stateTerminates_iff_of_bisim (h_bisim : s₁ ~ₛ s₂) :
    c₁.StateTerminates s₁ ↔ c₂.StateTerminates s₂ :=
  ⟨aux h_bisim, aux h_bisim.symm⟩
where
  aux {c₁ c₂ : StateMachine α} {s₁ : c₁.σ} {s₂ : c₂.σ} (h_bisim : s₁ ~ₛ s₂) :
      c₁.StateTerminates s₁ → c₂.StateTerminates s₂ := by
    rintro ⟨n, s₁_terminates⟩
    rcases h_iter₁ : c₁.iterate s₁ n with _|a
    case inl => simp [h_iter₁] at s₁_terminates
    clear s₁_terminates

    have ⟨s₁', n', h_iter₁', h_next'⟩ := final_state h_iter₁
    --    ^^ `s₁'` is the final state before termination
    have h_bisim' : s₁' ~ₛ s₂ := by
      apply Bisim.trans (y:=s₁)
      · symm; apply bisim_iterate h_iter₁'
      · exact h_bisim
    have ⟨k, l, h⟩ := h_bisim'.agreesUpTo_bisim
    use l+1

    rw [iterate, h_next'] at h
    simp only at h
    revert h
    cases h_iter_l : c₂.iterate s₂ (l+1) <;> rintro ⟨h⟩
    rfl

theorem bisim_sound :
    (s₁ ~ₛ s₂) ↔ (
      (¬c₁.StateTerminates s₁ ∧ ¬c₂.StateTerminates s₂)
      ∨ (∃ n m a, c₁.iterate s₁ n = .inr a ∧ c₂.iterate s₂ m = .inr a)) := by
  constructor
  · intro h_bisim
    by_cases s₁_terminates : c₁.StateTerminates s₁
    <;> have s₂_terminates := by simpa [stateTerminates_iff_of_bisim h_bisim] using s₁_terminates
    case neg =>
      exact Or.inl ⟨s₁_terminates, s₂_terminates⟩
    case pos =>
      apply Or.inr
      simp only [StateTerminates, Sum.isRight_iff] at s₁_terminates s₂_terminates
      rcases s₁_terminates with ⟨n, a, h_iterate₁⟩
      rcases s₂_terminates with ⟨m, b, h_iterate₂⟩
      obtain rfl : a = b := eq_of_bisim_iterate_eq_inr h_bisim h_iterate₁ h_iterate₂
      exact ⟨n, m, a, h_iterate₁, h_iterate₂⟩
  · rintro (⟨s₁_non_terminates, s₂_non_terminates⟩|⟨n, m, a, h_iter₁, h_iter₂⟩)
    · exact bisim_of_non_terminates s₁_non_terminates s₂_non_terminates
    · exact bisim_of_iterate_eq_inr h_iter₁ h_iter₂

#print axioms bisim_sound

end StateMachine

-- /-- If `x ~ y`, then `x` terminates iff `y` terminates -/
-- theorem terminates_iff_of_bisim (h : x ~ y) : sorry := sorry


end BisimIffEquiv

end CoroutineM
