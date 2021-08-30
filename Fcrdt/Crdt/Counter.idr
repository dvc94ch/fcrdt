module Fcrdt.Crdt.Counter

%default total

data State = MkState Int

data Op = Increment | Decrement

init : State
init = MkState 0

apply : Op -> State -> State
apply Increment (MkState s) = s + 1
apply Decrement (MkState s) = s - 1

happens_before : Op -> Op -> Type

concurrent : Op -> Op -> Type
concurrent a b = not (happens_before a b) && not (happens_before b a)-}
