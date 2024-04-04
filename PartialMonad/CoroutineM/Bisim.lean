import PartialMonad.CoroutineM

/-!
This file establishes a notion of bisimilarity on `CoroutineM`, and shows that is an equivalence
relation
-/

namespace CoroutineM

inductive StepAgrees (R : σ₁ → σ₂ → Prop) : σ₁ ⊕ α → σ₂ ⊕ α → Prop
  | inl {s₁ s₂} : R s₁ s₂ → StepAgrees R (.inl s₁) (.inl s₂)
  | inr {a} : StepAgrees R (.inr a) (.inr a)

def IsBisimulation {x y : CoroutineM α} (R : x.σ → y.σ → Prop) : Prop :=
  ∀ (s₁ : x.σ) (s₂ : y.σ), R s₁ s₂ → StepAgrees R (x.next s₁) (y.next s₂)

inductive Bisim (x y : CoroutineM α) : Prop where
  | mk
    (R : x.σ → y.σ → Prop)
    (bisim : IsBisimulation R)
    (state : R x.state y.state)

/-! `Bisim` is an equivalence -/
section BisimIsEquiv

theorem StepAgrees.rfl (h : ∀ a, R a a) : StepAgrees R x x := by
  cases x <;> constructor
  exact h _

/-- `Eq` is a bisimulation -/
theorem isBisimulation_eq {x : CoroutineM α} : @IsBisimulation _ x x Eq := by
  simp only [IsBisimulation, forall_eq', implies_true, StepAgrees.rfl]

namespace Bisim

theorem rfl (x : CoroutineM α) : Bisim x x :=
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

/-- The canonical equality on coroutines is bisimilarity -/
instance setoid (α : Type _) : Setoid (CoroutineM α) where
  r := Bisim
  iseqv := Bisim.equivalence

end BisimIsEquiv

end CoroutineM
