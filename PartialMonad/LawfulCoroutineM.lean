import PartialMonad.CoroutineM
import PartialMonad.CoroutineM.Bisim
import PartialMonad.CoroutineM.Get

/-!
This file defines the `LawfulCoroutineM` monad.

As the name suggests, this is a lawful version of `CoroutineM`, it is constructed by quotienting
coroutines through the bisimilarity relation.
-/

#check ULift

def CoroutineM.bumpUniverse.{r, s} {α : Type s} (x : CoroutineM.{s} α) :
    CoroutineM.{r} (ULift.{r, s} α) where
  σ := ULift x.σ
  state := .up x.state
  next s := sorry

def LawfulCoroutineM (α : Type u) := Quotient (CoroutineM.setoid α)

namespace LawfulCoroutineM

/-- The canonical map from `CoroutineM` into the quotient -/
def ofCoroutine : CoroutineM α → LawfulCoroutineM α :=
  Quotient.mk _

/-- `pure a` gives a trivial coroutine, which completes in a single step, yielding the value `a` -/
def pure (a : α) : LawfulCoroutineM α :=
  ofCoroutine <| CoroutineM.pure a


/-
Now comes the tricky part, how are we going to define `bind`
-/

def bind {α β : Type u} (x : LawfulCoroutineM α) (f : α → LawfulCoroutineM β) :
    LawfulCoroutineM β :=
  let f_lift (x : CoroutineM α) : LawfulCoroutineM β :=
    let x' := x.map f
    sorry
  Quotient.liftOn x f_lift _


end LawfulCoroutineM
