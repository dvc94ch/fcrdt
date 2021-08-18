module Fcrdt.Map

import Data.List
import Data.Nat

iff : (p, q : Type) -> Type
iff p q = (p -> q, q -> p)

iff_sym : iff p q -> iff q p
iff_sym (x, y) = (y, x)

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


public export
data Key : Type where
    MkKey : Nat -> Key

%name Key key, k, k1, k2

public export
Eq Key where
    MkKey a == MkKey b = a == b

key_to_nat : Key -> Nat
key_to_nat (MkKey n) = n

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

t_update_shadow : (t_update x v2 $ t_update x v1 m) = t_update x v2 m
t_update_shadow = ?t_update_shadow_rhs

t_update_same : t_update x (m x) m = m

t_update_permute : Not (x2 = x1) -> (t_update x1 v1 $ t_update x2 v2 m) = (t_update x2 v2 $ t_update x1 v1 m)

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

p_update_shadow : (p_update x v2 $ p_update x v1 m) = p_update x v2 m
p_update_shadow = t_update_shadow

p_update_same : m x = Just v -> p_update x v m = m
p_update_same prf = rewrite sym prf in t_update_same

p_update_permute : Not (x2 = x1) -> (p_update x1 v1 $ p_update x2 v2 m) = (p_update x2 v2 $ p_update x1 v1 m)
p_update_permute = t_update_permute

export
data Map a = MkMap (List Key) (TotalMap (Maybe a))

%name Map map, m, m1, m2

empty : Map a
empty = MkMap [] (const Nothing)

keys : Map a -> List Key
keys (MkMap ks _) = ks

public export
get : Key -> Map a -> Maybe a
get key (MkMap _ f) = f key

public export
update : Key -> Maybe a -> Map a -> Map a
update k v (MkMap ks f) =  MkMap (k :: ks) (t_update k v f)

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

update_eq : (m : Map a) -> get k (update k v m) = v
update_eq (MkMap xs f) = rewrite beq_key k in Refl

update_neq : {x1, x2 : Key} -> (m : Map a) -> Not (x1 = x2) -> (get x2 $ update x1 v m) = get x2 m
update_neq (MkMap xs f) prf = t_update_neq prf

update_shadow : (m : Map a) -> (get x $ update x v2 $ update x v1 m) = (get x $ update x v2 m)
update_shadow (MkMap xs f) = rewrite beq_key x in Refl

update_same : (m : Map a) -> (get x m) = v -> (get x $ update x v m) = v
update_same (MkMap xs f) prf = rewrite beq_key x in Refl

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
        rewrite prf1 in rewrite prf2 in rewrite prf1 in Refl
