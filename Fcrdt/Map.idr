module Fcrdt.Map

import Data.List
import Data.Maybe
import Data.Nat

%default total

iff : (p, q : Type) -> Type
iff p q = (p -> q, q -> p)

iff_sym : iff p q -> iff q p
iff_sym (x, y) = (y, x)

functional_extensionality : ((x : a) -> f x = g x) -> f = g
functional_extensionality = believe_me

public export
data Reflect : (p: Type) -> (b: Bool) -> Type where
    ReflectT : p -> (b=True) -> Reflect p b
    ReflectF : (Not p) -> (b=False) -> Reflect p b

iff_reflect : (b : Bool) -> iff p (b = True) -> Reflect p b
iff_reflect False (x, y) = ReflectF (uninhabited . x) Refl
iff_reflect True (x, y) = ReflectT (y Refl) Refl

reflect_iff : (b : Bool) -> Reflect p b -> iff p (b = True)
reflect_iff False (ReflectT _ Refl) impossible
reflect_iff False (ReflectF f prf) = (\p => void (f p), \p => void (uninhabited p))
reflect_iff True (ReflectT x prf) = (\p => prf, \Refl => x)
reflect_iff True (ReflectF _ Refl) impossible

beq_nat : (n: Nat) -> n == n = True
beq_nat 0 = Refl
beq_nat (S k) = beq_nat k

beq_implies_eq_nat : (n1, n2 : Nat) -> n1 == n2 = True -> n1 = n2
beq_implies_eq_nat 0 0 prf = Refl
beq_implies_eq_nat 0 (S _) Refl impossible
beq_implies_eq_nat (S _) 0 Refl impossible
beq_implies_eq_nat (S k) (S j) prf =
    let ind = beq_implies_eq_nat k j prf in
        rewrite ind in Refl

eq_implies_beq_nat : (n1, n2 : Nat) -> n1 = n2 -> n1 == n2 = True
eq_implies_beq_nat n1 n2 prf = rewrite prf in beq_nat n2

not_succ_implies_not : Not (S k = S j) -> Not (k = j)
not_succ_implies_not f prf = f $ cong S prf

neq_implies_bneq_nat : (n1, n2 : Nat) -> Not (n1 = n2) -> n1 == n2 = False
neq_implies_bneq_nat 0 0 prf = absurd $ prf Refl
neq_implies_bneq_nat 0 (S k) prf = Refl
neq_implies_bneq_nat (S k) 0 prf = Refl
neq_implies_bneq_nat (S k) (S j) prf =
    let
        prf = not_succ_implies_not prf
        ind = neq_implies_bneq_nat k j prf
    in rewrite ind in Refl

not_implies_not_succ : Not (k = j) -> Not (S k = S j)
not_implies_not_succ f prf = f $ cong pred prf

bneq_implies_neq_nat : (n1, n2 : Nat) -> n1 == n2 = False -> Not (n1 = n2)
bneq_implies_neq_nat 0 0 prf = absurd prf
bneq_implies_neq_nat 0 (S k) Refl = uninhabited
bneq_implies_neq_nat (S k) 0 Refl = uninhabited
bneq_implies_neq_nat (S k) (S j) prf =
    let ind = bneq_implies_neq_nat k j prf in
        not_implies_not_succ ind

beq_natP : (n, m : Nat) -> Reflect (n = m) (n == m)
beq_natP n m with (n == m) proof h
    beq_natP n m | False = ReflectF (bneq_implies_neq_nat n m h) Refl
    beq_natP n m | True = ReflectT (beq_implies_eq_nat n m h) Refl


In : (x : a) -> (l : List a) -> Type
In x [] = Void
In x (x' :: xs) = Either (x' = x) (In x xs)

InOnce : (x : a) -> (l : List a) -> Type
InOnce x [] = Void
InOnce x (x' :: xs) = Either ((x' = x, Not (In x xs))) (InOnce x xs)


public export
data Key : Type where
    MkKey : Nat -> Key

%name Key key, k, k1, k2

key_to_nat : Key -> Nat
key_to_nat (MkKey n) = n

public export
Eq Key where
    MkKey a == MkKey b = a == b

public export
Uninhabited (a = b) => Uninhabited (MkKey a = MkKey b) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl

public export
beq_key : (k: Key) -> k == k = True
beq_key (MkKey n) = beq_nat n

public export
beq_keyP : (n, m : Key) -> Reflect (n = m) (n == m)
beq_keyP (MkKey k) (MkKey j) with (beq_natP k j)
    beq_keyP (MkKey k) (MkKey j) | (ReflectT x prf) = ReflectT (cong MkKey x) prf
    beq_keyP (MkKey k) (MkKey j) | (ReflectF f prf) = ReflectF (\p => f (cong key_to_nat p)) prf


TotalMap : Type -> Type
TotalMap a = Key -> a

t_empty : (v : a) -> TotalMap a
t_empty = const

t_update : (x : Key) -> (v : a) -> (m : TotalMap a) -> TotalMap a
t_update x v m = \x' => if x == x' then v else m x'

t_apply_empty : t_empty v x = v
t_apply_empty = Refl

t_update_eq : (t_update x v m) x = v
t_update_eq = rewrite beq_key x in Refl

t_update_neq : {x1, x2 : Key} -> Not (x1 = x2) -> (t_update x1 v m) x2 = m x2
t_update_neq f with (beq_keyP x1 x2)
    t_update_neq f | (ReflectT x prf) = rewrite prf in void (f x)
    t_update_neq f | (ReflectF g prf) = rewrite prf in Refl

t_update_shadow : {x : Key} -> (t_update x v2 $ t_update x v1 m) = t_update x v2 m
t_update_shadow = functional_extensionality $ \y =>
    case beq_keyP x y of
        ReflectT z prf => rewrite prf in Refl
        ReflectF f prf => rewrite prf in rewrite prf in Refl

t_update_same : {x : Key} -> t_update x (m x) m = m
t_update_same = functional_extensionality $ \y =>
    case beq_keyP x y of
        ReflectT z prf => rewrite prf in rewrite z in Refl
        ReflectF f prf => rewrite prf in Refl

t_update_permute : {x1, x2 : Key} -> Not (x2 = x1) -> (t_update x1 v1 $ t_update x2 v2 m) = (t_update x2 v2 $ t_update x1 v1 m)
t_update_permute f = functional_extensionality $ \y =>
    case (beq_keyP x1 y, beq_keyP x2 y) of
        (ReflectT x prf, ReflectT z prf1) =>
            rewrite prf in rewrite prf1 in
                void $ f $ rewrite x in rewrite z in Refl
        (ReflectT x prf, (ReflectF g prf1)) =>
            rewrite prf in rewrite prf1 in rewrite prf in Refl
        (ReflectF g prf, ReflectT x prf1) =>
            rewrite prf in rewrite prf1 in Refl
        (ReflectF g prf, ReflectF f1 prf1) =>
            rewrite prf in rewrite prf1 in rewrite prf in Refl


PartialMap : Type -> Type
PartialMap a = TotalMap (Maybe a)

p_empty : PartialMap a
p_empty = t_empty Nothing

p_update : (x : Key) -> (v : a) -> (m : PartialMap a) -> PartialMap a
p_update x v m = t_update x (Just v) m

p_apply_empty : p_empty x = Nothing
p_apply_empty = Refl

p_update_eq : (p_update x v m) x = Just v
p_update_eq = t_update_eq

p_update_neq : {x1, x2 : Key} -> Not (x1 = x2) -> (p_update x1 v m) x2 = m x2
p_update_neq f = t_update_neq f

p_update_shadow : {x : Key} -> (p_update x v2 $ p_update x v1 m) = p_update x v2 m
p_update_shadow = t_update_shadow

p_update_same : {x : Key} -> m x = Just v -> p_update x v m = m
p_update_same prf = rewrite sym prf in t_update_same

p_update_permute : {x1, x2 : Key} -> Not (x2 = x1) -> (p_update x1 v1 $ p_update x2 v2 m) = (p_update x2 v2 $ p_update x1 v1 m)
p_update_permute = t_update_permute


Bag : Type
Bag = List Key

b_count : (k : Key) -> (s : Bag) -> Nat
b_count k [] = 0
b_count k (x :: xs) with (k == x)
    b_count k (x :: xs) | False = b_count k xs
    b_count k (x :: xs) | True = 1 + b_count k xs

b_sum : Bag -> Bag -> Bag
b_sum xs ys = xs ++ ys

b_add : (k : Key) -> (s : Bag) -> Bag
b_add k s = k :: s

b_member : (k : Key) -> (s : Bag) -> Bool
b_member k s = not (b_count k s == 0)

b_remove_one : (k : Key) -> (s : Bag) -> Bag
b_remove_one k [] = []
b_remove_one k (x :: xs) with (k == x)
    b_remove_one k (x :: xs) | False = x :: b_remove_one k xs
    b_remove_one k (x :: xs) | True = xs

b_remove_all : (k : Key) -> (s : Bag) -> Bag
b_remove_all k [] = []
b_remove_all k (x :: xs) with (k == x)
    b_remove_all k (x :: xs) | False = x :: b_remove_all k xs
    b_remove_all k (x :: xs) | True = b_remove_all k xs

b_add_eq : (s : Bag) -> (k : Key) -> b_count k (b_add k s) = S (b_count k s)
b_add_eq s k = rewrite beq_key k in Refl

b_add_neq : (s : Bag) -> (k1, k2 : Key) -> Not (k1 = k2) -> b_count k1 (b_add k2 s) = b_count k1 s
b_add_neq s k1 k2 f with (beq_keyP k1 k2)
    b_add_neq s k1 k2 f | (ReflectT x prf) = void (f x)
    b_add_neq s k1 k2 f | (ReflectF g prf) = rewrite prf in Refl

b_remove_all_eq : (s : Bag) -> (k : Key) -> b_count k (b_remove_all k s) = 0
b_remove_all_eq [] k = Refl
b_remove_all_eq (x :: xs) k with (beq_keyP k x)
    b_remove_all_eq (x :: xs) k | (ReflectT y prf) = rewrite prf in b_remove_all_eq xs k
    b_remove_all_eq (x :: xs) k | (ReflectF f prf) = rewrite prf in rewrite prf in b_remove_all_eq xs k


mutual
    data Set : Type where
        Empty : Set
        Entry : (k : Key) -> (s : Set) -> NotInSet k s -> Set

    data NotInSet : (k : Key) -> (s : Set) -> Type where
        IsEmpty : NotInSet k Empty
        HasEntry : Not (k2 = k) -> NotInSet k s -> NotInSet k (Entry k2 s p)

Uninhabited (NotInSet key (Entry key s x)) where
    uninhabited (HasEntry f y) = f Refl

empty_set : Set
empty_set = Empty

set_one_elem : Set
set_one_elem = Entry (MkKey 0) empty_set IsEmpty

set_two_elem : Set
set_two_elem = Entry (MkKey 1) (Entry (MkKey 0) Empty IsEmpty) (HasEntry uninhabited IsEmpty)

set_three_elem : Set
set_three_elem = Entry (MkKey 2) set_two_elem (HasEntry uninhabited (HasEntry uninhabited IsEmpty))

s_member : (k : Key) -> (s : Set) -> Bool
s_member k Empty = False
s_member k (Entry key s x) = if k == key then True else s_member k s

InSet : (k : Key) -> (s : Set) -> Type
InSet k Empty = Void
InSet k (Entry k' s _) = Either (k' = k) (InSet k s)

s_memberP : (set : Set) -> (key : Key) -> Reflect (InSet key set) (s_member key set)
s_memberP Empty _ = ReflectF id Refl
s_memberP (Entry k s p) key with (beq_keyP key k)
    s_memberP (Entry k s p) key | (ReflectT x prf) =
        rewrite prf in ReflectT (Left (sym x)) Refl
    s_memberP (Entry k s p) key | (ReflectF f prf) with (s_memberP s key)
        s_memberP (Entry k s p) key | ReflectF f prf | (ReflectT x prf1) =
            rewrite prf in rewrite prf1 in ReflectT (Right x) Refl
        s_memberP (Entry k s p) key | ReflectF f prf | (ReflectF g prf1) =
            rewrite prf in rewrite prf1 in ReflectF (
                \e => case e of
                    Left a => f (sym a)
                    Right b => g b) Refl

neg_not_in : (s : Set) -> (k : Key) -> Not (NotInSet k s) -> InSet k s
neg_not_in Empty _ f = f IsEmpty
neg_not_in (Entry k s x) key f with (beq_keyP k key)
    neg_not_in (Entry k s x) key f | (ReflectT y prf) = Left y
    neg_not_in (Entry k s x) key f | (ReflectF g prf) with (s_memberP s key)
        neg_not_in (Entry k s x) key f | (ReflectF g prf) | (ReflectT y prf1) = Right y
        neg_not_in (Entry k s x) key f | (ReflectF g prf) | (ReflectF f1 prf1) =
            let h = \x => f (HasEntry g x)
                ind = neg_not_in s key h in Right ind

neg_in : (s : Set) -> (k : Key) -> Not (InSet k s) -> NotInSet k s
neg_in Empty _ _ = IsEmpty
neg_in (Entry key s x) k f with (s_memberP s k)
    neg_in (Entry key s x) k f | (ReflectT y prf) = void (f (Right y))
    neg_in (Entry key s x) k f | (ReflectF g prf) with (beq_keyP key k)
        neg_in (Entry key s x) k f | (ReflectF g prf) | (ReflectT y prf1) = void (f (Left y))
        neg_in (Entry key s x) k f | (ReflectF g prf) | (ReflectF f1 prf1) =
            let ind = neg_in s k (\x => f (Right x)) in
                case ind of
                    IsEmpty => HasEntry f1 ind
                    HasEntry a b => HasEntry f1 ind

mutual
    s_update_f : (k : Key) -> (s : Set)  -> Set
    s_update_f k s with (s_memberP s k)
        s_update_f k s | (ReflectT y prf) = case s of
            Entry k' s' p' => case y of
                Left a => s'
                Right b => Entry k' (s_update_f k s') (s_update_f_lemma s' k' k p')
        s_update_f k s | (ReflectF f prf) = s

    s_update_f_lemma : (s : Set) -> (k1, k2 : Key) -> NotInSet k1 s -> NotInSet k1 (s_update_f k2 s)
    s_update_f_lemma Empty k1 k2 IsEmpty = IsEmpty
    s_update_f_lemma (Entry k s y) k1 k2 (HasEntry f x) with (s_memberP s k)
        s_update_f_lemma (Entry k s y) k1 k2 (HasEntry f x) | (ReflectT z prf) =
            let ind = s_update_f_lemma s k1 k2 x in ?s_update_f_lemma_rhs_4
        s_update_f_lemma (Entry k s y) k1 k2 (HasEntry f x) | (ReflectF g prf) = ?s_update_f_lemma_rhs_5

    {-    s_update_f k (Entry x s p) | (ReflectT y prf) = s
        s_update_f k (Entry x s p) | (ReflectF f prf) =
            let a = s_update_f_lemma s k f p in Entry x (s_update_f k s) a
            -- ?h --(s_update_f_lemma s ?h f p)
    {-s_update k True s with (s_memberP s k)
        s_update k True s | (ReflectT x prf) = s
        s_update k True s | (ReflectF f prf) = Entry k s (neg_in s k f)-}

    s_update_f_lemma : (s : Set) -> (x : Key) -> Not (k = x) -> NotInSet k s -> NotInSet k (s_update_f x s)
    s_update_f_lemma Empty _ _ _ = IsEmpty
    s_update_f_lemma (Entry key s z) x f (HasEntry g y) with (beq_keyP key x)
        s_update_f_lemma (Entry key s z) x f (HasEntry g y) | (ReflectT w prf) = y
        s_update_f_lemma (Entry key s z) x f (HasEntry g y) | (ReflectF f1 prf) =
            let ind = s_update_f_lemma s x f y in ?s_update_lemma_rhs_3
    {-s_update_lemma s f IsEmpty = IsEmpty
    s_update_lemma s f (HasEntry g IsEmpty) = ?h_1
    s_update_lemma s f (HasEntry g (HasEntry f1 y)) = ?h_2-}
        --let ind = s_update_lemma f y in ?h --with (beq_keyP k2 x)
        --s_update_lemma f (HasEntry g y) | r = ?s_update_lemma_rhs_2-}-}

{-s_add : (k : Key) -> (s : Set) -> Set
s_add k s = s_update k True s

s_remove : (k : Key) -> (s : Set) -> Set
s_remove k s = s_update k False s-}

{-s_update_eq : (s : Set) -> (k : Key) -> (b : Bool) -> s_member k (s_update k b s) = b
s_update_eq Empty k False = Refl
s_update_eq Empty k True = rewrite beq_key k in Refl
s_update_eq (Entry x xs _) k False with (beq_keyP k x)
    s_update_eq (Entry x xs _) k False | (ReflectT y prf) = rewrite prf in s_update_eq xs k False
    s_update_eq (Entry x xs _) k False | (ReflectF f prf) = rewrite prf in rewrite prf in s_update_eq xs k False
s_update_eq (Entry x xs _) k True with (beq_keyP k x)
    s_update_eq (Entry x xs _) k True | (ReflectT y prf) = rewrite prf in Refl
    s_update_eq (Entry x xs _) k True | (ReflectF f prf) with (s_memberP xs k)
        s_update_eq (Entry x xs _) k True | (ReflectF f prf) | (ReflectT y prf1) =
            rewrite prf in rewrite prf1 in Refl
        s_update_eq (Entry x xs _) k True | (ReflectF f prf) | (ReflectF g prf1) =
            rewrite beq_key k in Refl-}

{-s_update_shadow : (s : Set) -> (k : Key) -> (b1, b2 : Bool) -> (s_update k b2 $ s_update k b1 s) = s_update k b2 s
s_update_shadow Empty k False b2 = Refl
s_update_shadow Empty k True False = rewrite beq_key k in Refl
s_update_shadow Empty k True True with (beq_keyP k k)
    s_update_shadow Empty k True True | (ReflectT x prf) = Refl
    s_update_shadow Empty k True True | (ReflectF f prf) = void (f Refl)
s_update_shadow (Entry key s x) k False False with (beq_keyP k key)
    s_update_shadow (Entry key s x) k False False | (ReflectT y prf) =
        rewrite prf in s_update_shadow s k False False
    s_update_shadow (Entry key s x) k False False | (ReflectF f prf) =
        rewrite prf in rewrite prf in let ind = s_update_shadow s k False False in
            rewrite ind in ?h_3
s_update_shadow (Entry key s x) k False True = ?h_4
s_update_shadow (Entry key s x) k True b2 = ?h_2-}

{-s_update_same : (s : Set) -> (k : Key) -> (b1, b2 : Bool) -> (s_member k s) = b -> s_update k b s = s
s_update_same m k v prf = ?update_same_rhs2
-- update_same (MkMap xs f) prf = rewrite beq_key x in Refl

s_update_permute : (s : Set) -> (k1, k2 : Key) -> (b1, b2 : Bool) -> Not (k1 = k2) ->
    (s_update k1 v1 $ s_update k2 v2 m) = (s_update k2 v2 $ s_update k1 v1 m)
s_update_permute m k1 k2 f = ?update_permute_rhs2

export
data Map a = MkMap Set (TotalMap (Maybe a))

%name Map map, m, m1, m2

public export
empty : Map a
empty = MkMap [] (const Nothing)

public export
isEmpty : Map a -> Bool
isEmpty (MkMap [] _) = True
isEmpty (MkMap (x :: xs) f) =
    case f x of
        Nothing => assert_total (isEmpty (MkMap xs f))
        _ => False

public export
keys : Map a -> List Key
keys (MkMap ks _) = ks

public export
get : Key -> Map a -> Maybe a
get key (MkMap _ f) = f key

public export
update : Key -> Maybe a -> Map a -> Map a
update k v (MkMap ks f) =  MkMap (s_update k (isJust v) ks) (t_update k v f)

public export
insert : Key -> a -> Map a -> Map a
insert key val map = update key (Just val) map

public export
delete : Key -> Map a -> Map a
delete key map = update key Nothing map

forall_keys_eq : Eq a => List Key -> (x, y : Map a) -> Bool
forall_keys_eq [] x y = ?t_eq'_rhs_1
forall_keys_eq (k :: ks) x y = get k x == get k y && forall_keys_eq ks x y

public export
Eq a => Eq (Map a) where
    x == y = forall_keys_eq (keys x ++ keys y) x y

public export
update_eq : (m : Map a) -> (k : Key) -> (v : Maybe a) -> get k (update k v m) = v
update_eq (MkMap xs f) k v = rewrite beq_key k in Refl

-- update_eqP : (m : Map a) -> (k : Key) -> (v : Maybe a) -> Reflect (

public export
update_neq : {x1, x2 : Key} -> (m : Map a) -> Not (x1 = x2) -> (get x2 $ update x1 v m) = get x2 m
update_neq (MkMap xs f) prf = t_update_neq prf

public export
update_shadow : (m : Map a) -> (k : Key) -> (v1, v2 : Maybe a) -> (update k v2 $ update k v1 m) = update k v2 m
update_shadow (MkMap xs f) k v1 v2 = ?hole345 --rewrite beq_key k in Refl

{-public export
update_shadow : (m : Map a) -> (k : Key) -> (get k $ update k v2 $ update k v1 m) = (get k $ update k v2 m)
update_shadow (MkMap xs f) k = rewrite beq_key k in Refl-}

public export
update_same : (m : Map a) -> (k : Key) -> (v : Maybe a) -> (get k m) = v -> update k v m = m
update_same m k v prf = ?update_same_rhs
-- update_same (MkMap xs f) prf = rewrite beq_key x in Refl

public export
update_permute : (m : Map a) -> (k1, k2 : Key) -> (v1, v2 : Maybe a) -> Not (k1 = k2) ->
    (update k1 v1 $ update k2 v2 m) = (update k2 v2 $ update k1 v1 m)
update_permute m k1 k2 f = ?update_permute_rhs

{-public export
update_permute : (m : Map a) -> (k : Key) -> (k1 : Key) -> (k2 : Key) -> Not (k1 = k2) ->
    (get k $ update k1 v1 $ update k2 v2 m) = (get k $ update k2 v2 $ update k1 v1 m)
update_permute (MkMap xs f) k k1 k2 prf with ((beq_keyP k1 k), (beq_keyP k2 k))
    update_permute (MkMap xs f) k k1 k2 prf | ((ReflectT x prf1), (ReflectT y prf2)) =
        void (prf (rewrite x in rewrite y in Refl))
    update_permute (MkMap xs f) k k1 k2 prf | ((ReflectT x prf1), (ReflectF g prf2)) =
        rewrite prf1 in rewrite prf2 in rewrite prf1 in Refl
    update_permute (MkMap xs f) k k1 k2 prf | ((ReflectF g prf1), (ReflectT x prf2)) =
        rewrite prf1 in rewrite prf2 in Refl
    update_permute (MkMap xs f) k k1 k2 prf | ((ReflectF g prf1), (ReflectF f1 prf2)) =
        rewrite prf1 in rewrite prf2 in rewrite prf1 in Refl-}

public export
get_neq : Not (get a m = get b m) -> Not (a = b)
get_neq f prf = f (cong (\k => get k m) prf)

public export
tuple_eq : (a, b) = (c, d) -> Not (c = d) -> Not (a = b)
tuple_eq prf f prf1 =
    let
        ac = cong fst prf
        bd = cong snd prf
    in f (rewrite sym ac in rewrite sym bd in prf1)

public export
it_is_just : (a : Maybe b) -> (a = Just c) -> IsJust a
it_is_just Nothing Refl impossible
it_is_just (Just x) prf = ItIsJust
-}
