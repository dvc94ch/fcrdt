
Vect p (Vect e (Either a (Fin p, Fin e)))

data History : (a : Type) -> Type  where
    Event : (v : a) -> History
    After :

a : Causal
a = Event 'a'

b : Causal
b = Event 'b'

c : Causal
c = Event 'c'

d : Causal
d = Event 'd'

Concurrent (HappensAfter b a) (HappensAfter c a)

Concurrent (HappensAfter c (HappensAfter b a)) (HappensAfter e (HappensAfter d a))

example : Causal 2
example = (HappensAfter 'd' (Concurrent 'c' (HappensAfter 'b' (Concurrent 'a' Empty))))

a = Causal 0
a = (Concurrent 'a' Empty

b = Causal 1
b = HappensAfter 'b' a

c = Causal 2
c = HappensAfter 'c' b

d = Causal 1
d = HappensAfter 'd' a

e = Causal 2
e = HappensAfter 'e' d

f = Causal 3
e

example2 : Causal 3
example2 = (HappensAfter 'c' (HappensAfter 'b' (Concurrent 'a' Empty)))




{-interface
happens_before : Dag a -> Dag a -> Bool

concurrent : Dag a -> Dag a -> Bool
concurrent a b = not (happens_before a b) && not (happens_before b a)-}
