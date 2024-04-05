import PartialMonad.LawfulCoroutineM
import PartialMonad.CoroutineM.Join

namespace LawfulCoroutineM

/-- Unwrap the VM representation of the `LawfulCoroutineM` quotient to access the underlying
`CoroutineM`. Computable, but unsound -/
unsafe def toCoroutineImpl : LawfulCoroutineM α → CoroutineM α :=
  cast lcProof

@[implemented_by toCoroutineImpl]
-- ^^^ Is it OK to implement the (noncomputable) `choose` version with the horibly unsound version?
--     The fact that mathlib has `Quotient.unquot` and `Quotient.out`, but does not do this
--     `implemented_by` trick makes me nervous there is something bad with it
def toCoroutine (x : LawfulCoroutineM α) : CoroutineM α :=
  Classical.choose (Quot.exists_rep x)

def bind {α β : Type u} (x : LawfulCoroutineM α) (f : α → LawfulCoroutineM β) :
    LawfulCoroutineM β :=
  ofCoroutine <| CoroutineM.bind (x.toCoroutine) (fun a => (f a).toCoroutine)

end LawfulCoroutineM
