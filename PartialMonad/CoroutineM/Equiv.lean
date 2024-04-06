import PartialMonad.CoroutineM.Get

namespace CoroutineM

/-- Two coroutines are considered equivalent if both terminate and yield the same result,
or if neither coroutine terminates -/
inductive Equiv : CoroutineM α → CoroutineM α → Prop
  | terminates {x y : CoroutineM α} :
      (hx : x.Terminates) → (hy : y.Terminates) → x.run hx = y.run hy
      → Equiv x y
  | non_terminates {x y : CoroutineM α} : ¬x.Terminates → ¬y.Terminates → Equiv x y



theorem pure_equiv (x : CoroutineM α) (∃ h, x.)

end CoroutineM
