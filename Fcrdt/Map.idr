module Fcrdt.Map

public export
data Key : Type where
    MkKey : Nat -> Key

%name Key key, k, k1, k2

public export
Eq Key where
    MkKey a == MkKey b = a == b

beq_nat : (n: Nat) -> n == n = True
beq_nat 0 = Refl
beq_nat (S k) = beq_nat k

public export
beq_key : (k: Key) -> k == k = True
beq_key (MkKey n) = beq_nat n

public export
data Map : Type -> Type where
    Empty : Map a
    Entry : Key -> a -> Map a -> Map a

%name Map map, m, m1, m2

public export
get : Map a -> Key -> Maybe a
get Empty _ = Nothing
get (Entry k v obj) key = if k == key then Just v else get obj key

public export
insert : Map a -> Key -> a -> Map a
insert Empty key val = Entry key val Empty
insert (Entry k v obj) key val = if k == key then (Entry key val obj) else (Entry k v (insert obj key val))

public export
delete : Map a -> Key -> Map a
delete Empty key = Empty
delete (Entry k v obj) key = if k == key then obj else Entry k v (delete obj key)

every_key_is_eq : Eq a => Map a -> Map a -> Bool
every_key_is_eq Empty _ = True
every_key_is_eq (Entry key x map) m =
    case get map key of
        Just y => x == y
        Nothing => False

public export
Eq a => Eq (Map a) where
    m1 == m2 = every_key_is_eq m1 m2 && every_key_is_eq m2 m1

-- lemmaUniqueKey : (map: Map a) -> (key: Key) -> (value: a)

public export
lemmaGetInsert : (map: Map a) -> (key: Key) -> (value: a) -> get (insert map key value) key = Just value
lemmaGetInsert Empty key _ = rewrite beq_key key in Refl
lemmaGetInsert (Entry k x map) key value with (k == key)
    lemmaGetInsert (Entry k x map) key value | False =
        let ind = lemmaGetInsert map key value in
            ?h --rewrite ind in Refl
    lemmaGetInsert (Entry k x map) key value | True =
        rewrite beq_key key in Refl

public export
lemmaDeleteInsert : (map: Map a) -> (key: Key) -> (value: a) -> get map key = Nothing -> delete (insert map key value) key = map
{-lemmaDeleteInsert Empty key value = rewrite beq_key key in Refl
lemmaDeleteInsert (Entry k x map) key value with (k == key)
    lemmaDeleteInsert (Entry k x map) key value | False =
        let ind = lemmaDeleteInsert map key value in
            ?lemmaDeleteInsert_rhs_3
    lemmaDeleteInsert (Entry k x map) key value | True = ?lemmaDeleteInsert_rhs_4-}

public export
lemmaGetDelete : (map: Map a) -> (key: Key) -> get (delete map key) key = Nothing
lemmaGetDelete map key = ?lemmaGetDelete_rhs

public export
lemmaInsertDelete : (map: Map a) -> (key: Key) -> (value: a) -> insert (delete map key) key value = insert map key value
lemmaInsertDelete map key value = ?lemmaInsertDelete_rhs


TotalMap : Type -> Type
TotalMap a = Key -> a
