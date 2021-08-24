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

public export
beq_bool : (b : Bool) -> b == b = True
beq_bool False = Refl
beq_bool True = Refl

public export
eq_bool : (b1, b2 : Bool) -> b1 == b2 = True -> b1 = b2
eq_bool False False _ = Refl
eq_bool False True Refl impossible
eq_bool True False Refl impossible
eq_bool True True _ = Refl

public export
inv_bool : (b1, b2 : Bool) -> b1 = (not b2) -> b2 = (not b1)
inv_bool False False Refl impossible
inv_bool False True _ = Refl
inv_bool True False _ = Refl
inv_bool True True Refl impossible

public export
and_split : (a : Bool) -> (b : Lazy Bool) -> (a && b = True) -> (a = True, b = True)
and_split False (Delay False) Refl impossible
and_split False (Delay True) Refl impossible
and_split True (Delay False) Refl impossible
and_split True (Delay True) _ = (Refl, Refl)

public export
tuple_eq : (a, b) = (c, d) -> Not (c = d) -> Not (a = b)
tuple_eq prf f prf1 =
    let
        ac = cong fst prf
        bd = cong snd prf
    in f (rewrite sym ac in rewrite sym bd in prf1)

-- Maybe utils
public export
it_is_just : (a : Maybe b) -> (a = Just c) -> IsJust a
it_is_just Nothing Refl impossible
it_is_just (Just x) prf = ItIsJust

public export
contra : IsJust a -> a = Nothing -> Void
contra ItIsJust Refl impossible


-- Nat utils
public export
beq_nat : (n : Nat) -> n == n = True
beq_nat 0 = Refl
beq_nat (S k) = beq_nat k

public export
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


-- String utils
public export
beq_str : (s : String) -> s == s = True
beq_str s = believe_me s

public export
eq_str : (s1, s2 : String) -> s1 == s2 = True -> s1 = s2
eq_str s1 s2 prf = believe_me prf


-- Key
public export
data Key : Type where
    MkKey : Nat -> Key

%name Key k, k1, k2

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
bne_key : (k1, k2 : Key) -> k1 == k2 = False -> Not (k1 = k2)
bne_key (MkKey k) (MkKey j) prf prf1 =
    bneq_implies_neq_nat k j prf (cong key_to_nat prf1)

public export
ne_key : (k1, k2 : Key) -> Not (k1 = k2) -> k1 == k2 = False
ne_key (MkKey k) (MkKey j) prf =
    neq_implies_bneq_nat k j (\p => prf $ rewrite p in Refl)

public export
beq_keyP : (n, m : Key) -> Reflect (n = m) (n == m)
beq_keyP (MkKey k) (MkKey j) with (beq_natP k j)
    beq_keyP (MkKey k) (MkKey j) | (ReflectT x prf) = ReflectT (cong MkKey x) prf
    beq_keyP (MkKey k) (MkKey j) | (ReflectF f prf) = ReflectF (\p => f (cong key_to_nat p)) prf


-- Map
mutual
    public export
    data Map : Type -> Type where
        Empty : Map a
        Entry : (k : Key) -> (v : a) -> (m : Map a) -> NotInMap k m -> Map a

    data NotInMap : (k : Key) -> (m : Map a) -> Type where
        IsEmpty : NotInMap k Empty
        HasEntry : Not (k = k2) -> NotInMap k m -> NotInMap k (Entry k2 v m p)

%name Map m, m1, m2
%name NotInMap p, p1, p2

Uninhabited (NotInMap k (Entry k v s p)) where
    uninhabited (HasEntry f y) = f Refl

empty : Map a
empty = Empty

test_one_elem : Map Nat
test_one_elem = Entry (MkKey 0) 42 empty IsEmpty

test_two_elem : Map Nat
test_two_elem = Entry (MkKey 1) 43 test_one_elem (HasEntry uninhabited IsEmpty)

test_three_elem : Map Nat
test_three_elem = Entry (MkKey 2) 44 test_two_elem (HasEntry uninhabited (HasEntry uninhabited IsEmpty))

contains : (k : Key) -> (m : Map a) -> Bool
contains _ Empty = False
contains k' (Entry k _ m _) = if k == k' then True else contains k' m

public export
get : (k : Key) -> (m : Map a) -> Maybe a
get _ Empty = Nothing
get k' (Entry k v m p) = if k == k' then Just v else get k' m

forall_keys_eq : Eq a => Map a -> Map a -> Bool
forall_keys_eq Empty _ = True
forall_keys_eq (Entry k v m1 _) m2 = get k m2 == Just v && forall_keys_eq m1 m2

public export
Eq a => Eq (Map a) where
    x == y = forall_keys_eq x y && forall_keys_eq y x

InMap : (k : Key) -> (m : Map a) -> Type
InMap k' Empty = Void
InMap k' (Entry k _ m _) = Either (k' = k) (InMap k' m)

containsP : (k : Key) -> (m : Map a) -> Reflect (InMap k m) (contains k m)
containsP k' Empty = ReflectF id Refl
containsP k' (Entry k _ m p) with (beq_keyP k k')
    containsP k' (Entry k _ m p) | (ReflectT x prf) =
        rewrite prf in ReflectT (Left (sym x)) Refl
    containsP k' (Entry k _ m p) | (ReflectF f prf) with (containsP k' m)
        containsP k' (Entry k _ m p) | ReflectF f prf | (ReflectT x prf1) =
            rewrite prf in rewrite prf1 in ReflectT (Right x) Refl
        containsP k' (Entry k _ m p) | ReflectF f prf | (ReflectF g prf1) =
            rewrite prf in rewrite prf1 in ReflectF (
                \e => case e of
                    Left a => f (sym a)
                    Right b => g b) Refl

neg_not_in : (m : Map a) -> (k : Key) -> Not (NotInMap k m) -> InMap k m
neg_not_in Empty _ f = f IsEmpty
neg_not_in (Entry k _ m p) k' f with (beq_keyP k' k)
    neg_not_in (Entry k _ m p) k' f | (ReflectT y prf) = Left y
    neg_not_in (Entry k _ m p) k' f | (ReflectF g prf) with (containsP k' m)
        neg_not_in (Entry k _ m p) k' f | (ReflectF g prf) | (ReflectT y prf1) = Right y
        neg_not_in (Entry k _ m p) k' f | (ReflectF g prf) | (ReflectF f1 prf1) =
            let h = \x => f (HasEntry g x)
                ind = neg_not_in m k' h in Right ind

neg_in : (m : Map a) -> (k : Key) -> Not (InMap k m) -> NotInMap k m
neg_in Empty _ _ = IsEmpty
neg_in (Entry k _ m p) k' f with (containsP k' m)
    neg_in (Entry k _ m p) k' f | (ReflectT y prf) = void (f (Right y))
    neg_in (Entry k _ m p) k' f | (ReflectF g prf) with (beq_keyP k' k)
        neg_in (Entry k _ m p) k' f | (ReflectF g prf) | (ReflectT y prf1) = void (f (Left y))
        neg_in (Entry k _ m p) k' f | (ReflectF g prf) | (ReflectF f1 prf1) =
            let ind = neg_in m k' (\x => f (Right x)) in
                case ind of
                    IsEmpty => HasEntry f1 ind
                    HasEntry a b => HasEntry f1 ind

insert' : Key -> (v : a) -> Map a -> Map a
insert' k v m with (containsP k m)
    insert' k v m | (ReflectT x prf) = m
    insert' k v m | (ReflectF f prf) = Entry k v m (neg_in m k f)

mutual
    remove' : Key -> Map a -> Map a
    remove' k m with (containsP k m)
        remove' k m | (ReflectT y prf) = case m of
            Entry k' v' m' p' => case y of
                Left a => m'
                Right b => Entry k' v' (remove' k m') (remove_lemma m' k' k p')
        remove' k m | (ReflectF f prf) = m

    remove_lemma : (m : Map a) -> (k1, k2 : Key) -> NotInMap k1 m -> NotInMap k1 (remove' k2 m)
    remove_lemma Empty k1 k2 IsEmpty = IsEmpty
    remove_lemma (Entry k _ m y) k1 k2 (HasEntry f x) with (containsP k m)
        remove_lemma (Entry k _ m y) k1 k2 (HasEntry f x) | (ReflectT z prf) =
            let ind = remove_lemma m k1 k2 x in ?s_update_f_lemma_rhs_4
        remove_lemma (Entry k _ m y) k1 k2 (HasEntry f x) | (ReflectF g prf) = ?s_update_f_lemma_rhs_5

public export
update : Key -> Maybe a -> Map a -> Map a
update k Nothing m = ?h -- remove' k m
update k (Just v) m = insert' k v m

public export
insert : Key -> (v : a) -> Map a -> Map a
insert k v m = update k (Just v) m

public export
remove : Key -> Map a -> Map a
remove k m = update k Nothing m

public export
update_eq : (m : Map a) -> (k : Key) -> (v : Maybe a) -> get k (update k v m) = v
{-s_update_eq Empty k False = Refl
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

public export
update_shadow : (m : Map a) -> (k : Key) -> (v1, v2 : Maybe a) -> (update k v2 $ update k v1 m) = update k v2 m
{-s_update_shadow Empty k False b2 = Refl
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

public export
update_same : (m : Map a) -> (k : Key) -> (v : Maybe a) -> update k (get k s) m = m

public export
update_permute : (m : Map a) -> (k1, k2 : Key) -> (v1, v2 : Maybe a) -> Not (k1 = k2) ->
    (update k1 v1 $ update k2 v2 m) = (update k2 v2 $ update k1 v1 m)

public export
get_neq : Not (get a m = get b m) -> Not (a = b)
get_neq f prf = f (cong (\k => get k m) prf)
