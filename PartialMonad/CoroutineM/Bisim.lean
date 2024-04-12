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
  ∃ n m, ImmediatelyAgreesUpTo R (iterate ⟨c₁, s₁⟩ (n+1)) (iterate ⟨c₂, s₂⟩ (m+1))

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

scoped infixl:70 " ~ " => StateMachine.Bisim

/-- Two coroutines are bisimilar, if their current states are bisimilar -/
abbrev Bisim (x y : CoroutineM α) : Prop :=
  x.state ~ y.state

scoped infixl:70 " ~ " => Bisim

end BisimDef

/-! `Bisim` is an equivalence -/
section BisimIsEquiv

/-- If `R` is reflexive, then `AgreesUpTo R` is also reflexive -/
theorem AgreesUpToR.rfl {c : StateMachine α} {R} (h : ∀ a, R a a) (s : c.σ) : AgreesUpTo R s s := by
  use 0, 0
  simp only [iterate, ImmediatelyAgreesUpTo]
  split <;> constructor
  exact h _

/-- `Eq` is a bisimulation -/
def Bisimulation.Eq (c : StateMachine σ) : Bisimulation c c :=
  ⟨(· = ·), by simp only [IsBisimulation, forall_eq', implies_true, AgreesUpToR.rfl]⟩

/-- The transitive closure of two bisimulations `R₁` and `R₂` is also a bisimulation -/
def Bisimulation.trans (R₁ : Bisimulation c₁ c₂) (R₂ : Bisimulation c₂ c₃) : Bisimulation c₁ c₃ :=
  ⟨fun s₁ s₃ => ∃ s₂, R₁ s₁ s₂ ∧ R₂ s₂ s₃, by
    intro s₁ s₃
    rcases R₁ with ⟨R₁, is_bisim₁⟩
    rcases R₂ with ⟨R₂, is_bisim₂⟩
    simp only [forall_exists_index, and_imp]
    intro s₂ hR₁ hR₂

    have ⟨n₁, m₁, agree₁⟩ := is_bisim₁ _ _ hR₁
    have ⟨n₂, m₂, agree₂⟩ := is_bisim₂ _ _ hR₂

    sorry
    -- rcases x.next s₁ with s₁'|a₁
    -- <;> rcases y.next s₂ with s₂'|a₂
    -- <;> rcases z.next s₃ with s₃'|a₃
    -- <;> rintro ⟨next₂⟩ ⟨next₁⟩
    -- <;> constructor
    -- exact ⟨_, next₁, next₂⟩
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
    cases iterate ⟨c₁, s₁⟩ (n+1) <;> cases iterate ⟨c₂, s₂⟩ (m+1)
    <;> rintro ⟨bisim⟩
    <;> constructor
    assumption
  ⟩

namespace StateMachine.Bisim

variable {c c₁ c₂ c₃ : StateMachine α}

theorem rfl (s : c.σ) : s ~ s :=
  ⟨.Eq _, by rfl⟩

theorem trans {x : c₁.σ} {y : c₂.σ} {z : c₃.σ}  :
    x ~ y → y ~ z → x ~ z
  | ⟨R₁, state₁⟩, ⟨R₂, state₂⟩ => ⟨R₁.trans R₂, Exists.intro y ⟨state₁, state₂⟩⟩

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

variable {c₁ c₂ : StateMachine α} (s₁ : c₁.σ) (s₂ : c₂.σ) (x y : CoroutineM α)

lemma mem_convergentStates_iff_of_bisim

/-- If `x ~ y`, then `x` terminates iff `y` terminates -/
theorem terminates_iff_of_bisim (h : x ~ y) : sorry := sorry


end BisimIffEquiv

end CoroutineM
