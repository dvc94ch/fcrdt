module Fcrdt.Register

import Data.List
import Data.Maybe
import Fcrdt.Lens
import Fcrdt.Map

%default total

record OpId where
    constructor MkOpId
    uop_id, op_id, replica_id : Nat

%name OpId id, id', id''

Eq OpId where
    a == b = a.uop_id == b.uop_id && a.op_id == b.op_id && a.replica_id == b.replica_id

Ord OpId where
    compare a b = case compare a.op_id b.op_id of
        EQ => case compare a.uop_id b.uop_id of
            EQ => compare a.replica_id b.replica_id
            cmp => cmp
        cmp => cmp

record Op a where
    constructor MkOp
    replica_id : Nat
    deps : List OpId
    mut : a

%name Op op, op', op''

max : List OpId -> Nat
max [] = 0
max (x :: xs) =
    let m = max xs in
        if x.op_id > m then x.op_id else m

lamport : Op a -> Nat
lamport op = max op.deps + 1

lamport' : List (Op a) -> Nat
lamport' [] = 0
lamport' (x :: xs) = lamport x

op_id : Op a -> OpId
op_id op = MkOpId 0 (lamport op) op.replica_id

not_happened_before : Op a -> Op a -> Bool
not_happened_before a b = lamport a >= lamport b

happened_before : Op a -> Op a -> Bool
happened_before a b = isJust (find (== op_id a) b.deps)

concurrent : Op a -> Op a -> Bool
concurrent a b = not (happened_before a b) && not (happened_before b a)

data Causal : List (Op a) -> Type where
    CNil : Causal []
    CCons : (op : Op a) -> lamport op >= lamport' xs = True -> Causal (op :: xs)

data History : List (Op a) -> List (Op a) -> Type where
    HNil : History [] []
    HSkip : (op : Op a) -> lamport op >= lamport' xs = True -> History xs ys -> History (op :: xs) (op :: ys)
    HSwap : (op, op' : Op a) -> lamport op = lamport op' -> lamport op >= lamport' xs = True ->
        History xs xs -> History (op :: op' :: xs) (op' :: op :: xs)
    HTrans : {ys : List (Op a)} -> History xs ys -> History ys zs -> History xs zs

%name History h, h', h''

history_trans : History a b -> History b a

history_length : History a b -> length a = length b

--history_contains : (op : OpId) -> (a, b : List Op) -> History a b ->
--    isJust (find ((op ==) . op_id) a) = True -> isJust (find ((op ==) . op_id) b) = True
-- history_not_contains :
-- history_lamport
-- history_causal

lamport_invariant : (op, op' : Op a) -> lamport op = lamport op' -> Not (op.replica_id = op'.replica_id)
lamport_invariant op op' prf = believe_me

op_id_invariant : (op, op' : Op a) -> lamport op = lamport op' -> Not (op_id op = op_id op')
op_id_invariant op op' prf prf1 =
    let replica_id_eq = cong (\op => op.replica_id) prf1 in
        lamport_invariant op op' prf replica_id_eq


-- Multi value register

Reg : Type -> Type
Reg a = Map OpId a


-- Multi value register query
reg_values'' : List OpId -> Reg a -> List (OpId, a)
reg_values'' [] r = []
reg_values'' (x :: xs) r with (get x r)
    reg_values'' (x :: xs) r | Nothing = reg_values'' xs r
    reg_values'' (x :: xs) r | Just v = (x, v) :: reg_values'' xs r

reg_values' : Reg a -> List (OpId, a)
reg_values' r = reg_values'' (keys r) r

reg_values : Reg a -> List a
reg_values r = map snd (reg_values' r)

reg_value'' : List (OpId, a) -> Maybe (OpId, a)
reg_value'' [] = Nothing
reg_value'' (x :: xs) with (reg_value'' xs)
    reg_value'' (x :: xs) | Nothing = Just x
    reg_value'' ((id, v) :: xs) | Just (id', v') =
        if id > id' then Just (id, v) else Just (id', v')

reg_value' : Reg a -> Maybe (OpId, a)
reg_value' r = reg_value'' (reg_values' r)

reg_value : Reg a -> Maybe a
reg_value r = map snd (reg_value' r)


-- Multi value register ops
data RegOp a =
      RegAssign a
    | RegRemove

%name RegOp op, op', op''

reg_mk_assign : a -> RegOp a
reg_mk_assign v = RegAssign v

reg_mk_remove : RegOp a
reg_mk_remove = RegRemove


-- Multi value register apply op
reg_apply_op' : OpId -> RegOp a -> Reg a -> Reg a
reg_apply_op' id (RegAssign v) r = insert id v r
reg_apply_op' id RegRemove r = r

reg_apply_op : Op (RegOp a) -> Reg a -> Reg a
reg_apply_op op@(MkOp _ deps op') r = reg_apply_op' (op_id op) op' $ remove_all deps r

reg_apply_ops : List (Op (RegOp a)) -> Reg a
reg_apply_ops [] = Empty
reg_apply_ops (x :: xs) = reg_apply_op x $ reg_apply_ops xs


-- Rga

record RgaElem a where
    constructor MkRgaElem
    op_id : OpId
    value : a
    deleted : Bool

data Rga : (a : Type) -> Type where
    Nil : Rga a
    Cons : RgaElem a -> Rga a -> Rga a

-- Rga query
rga_idx' : Nat -> Rga a -> Maybe (OpId, a)
rga_idx' k [] = Nothing
rga_idx' n (Cons x xs) with (x.deleted)
    rga_idx' n (Cons x xs) | True = rga_idx' n xs
    rga_idx' 0 (Cons x xs) | False = Just (x.op_id, x.value)
    rga_idx' (S k) (Cons x xs) | False = rga_idx' k xs

rga_idx : Nat -> Rga a -> Maybe a
rga_idx n r = map snd (rga_idx' n r)

rga_id : Nat -> Rga a -> Maybe OpId
rga_id n r = map fst (rga_idx' n r)

rga_get : OpId -> Rga a ->  Maybe a
rga_get id [] = Nothing
rga_get id (Cons x xs) with (x.op_id == id)
    rga_get id (Cons x xs) | True = Just x.value
    rga_get id (Cons x xs) | False = rga_get id xs

rga_length : Rga a -> Nat
rga_length [] = 0
rga_length (Cons x xs) = (if x.deleted then 0 else 1) + rga_length xs

rga_to_list : Rga a -> List a
rga_to_list [] = []
rga_to_list (Cons x xs) with (x.deleted)
    rga_to_list (Cons x xs) | True = rga_to_list xs
    rga_to_list (Cons x xs) | False = x.value :: rga_to_list xs

rga_from_list : OpId -> List a -> Rga a
rga_from_list id [] = []
rga_from_list id (x :: xs) = Cons (MkRgaElem id x False) (rga_from_list (record { uop_id $= (1+) } id) xs)

-- Rga ops

data RgaOp : (a : Type) -> Type where
    RgaInsert : a -> Maybe OpId -> RgaOp a
    RgaRemove : OpId -> RgaOp a

rga_mk_insert : a -> Maybe Nat -> Rga a -> Maybe (RgaOp a)
rga_mk_insert v Nothing r = Just (RgaInsert v Nothing)
rga_mk_insert v (Just idx) r with (rga_idx' idx r)
    rga_mk_insert v (Just idx) r | Nothing = Nothing
    rga_mk_insert v (Just idx) r | Just (id, _) = Just (RgaInsert v (Just id))

rga_mk_remove : Nat -> Rga a -> Maybe (RgaOp a)
rga_mk_remove idx r with (rga_idx' idx r)
    rga_mk_remove idx r | Nothing = Nothing
    rga_mk_remove idx r | Just (id, _) = Just (RgaRemove id)


-- Rga apply ops
rga_insert_body : RgaElem a -> Rga a -> Rga a
rga_insert_body e Nil = Cons e Nil
rga_insert_body e (Cons x xs) =
    if x.op_id < e.op_id
    then (Cons e (Cons x xs))
    else (Cons x (rga_insert_body e xs))

rga_insert : RgaElem a -> Maybe OpId -> Rga a -> Maybe (Rga a)
rga_insert e Nothing rga = Just (rga_insert_body e rga)
rga_insert e (Just id) [] = Nothing
rga_insert e (Just id) (Cons x xs) =
    if x.op_id == id
    then Just (Cons x (rga_insert_body e xs))
    else case rga_insert e (Just id) xs of
        Just xs => Just (Cons x xs)
        Nothing => Nothing

rga_update : OpId -> a -> Rga a -> Maybe (Rga a)
rga_update id v [] = Nothing
rga_update id v (Cons elem rga) with (elem.op_id == id)
    rga_update id v (Cons elem rga) | True = Just (Cons (record { value = v } elem) rga)
    rga_update id v (Cons elem rga) | False =
        case rga_update id v rga of
            Just rga => Just (Cons elem rga)
            Nothing => Nothing

rga_remove : OpId -> Rga a -> Maybe (Rga a)
rga_remove id [] = Nothing
rga_remove id (Cons x xs) =
    if x.op_id == id
    then Just (Cons (record { deleted = True } x) xs)
    else case rga_remove id xs of
        Just xs => Just (Cons x xs)
        Nothing => Nothing

rga_apply_op : Op (RgaOp a) -> Rga a -> Maybe (Rga a)
rga_apply_op op@(MkOp _ _ (RgaInsert v after)) r =
    rga_insert (MkRgaElem (op_id op) v False) after r
rga_apply_op (MkOp _ _ (RgaRemove id)) r = rga_remove id r

rga_apply_ops : List (Op (RgaOp a)) -> Maybe (Rga a)
rga_apply_ops [] = Just Nil
rga_apply_ops (x :: xs) with (rga_apply_ops xs)
    rga_apply_ops (x :: xs) | Nothing = Nothing
    rga_apply_ops (x :: xs) | Just r = rga_apply_op x r


-- Map crdt

-- JSON crdt
crdt_of : Schema -> Type
crdt_of SNull = Reg Unit
crdt_of SBoolean = Reg Bool
crdt_of SNumber = Reg Nat
crdt_of SText = Reg (List Char)
crdt_of (SArray e s) = Rga (s : Schema ** assert_total (crdt_of s)) -- where s = s
crdt_of (SObject m) = Map Key (s : Schema ** assert_total (crdt_of s)) -- where get k m = Just s

Crdt : Type
Crdt = (s : Schema ** crdt_of s)

get : Key -> Crdt -> Maybe Crdt
get k (MkDPair (SObject _) crdt) = get k crdt
get _ _ = Nothing

idx : Nat -> Crdt -> Maybe Crdt
idx n (MkDPair (SArray e s) rga) = rga_idx n rga
idx _ _ = Nothing

boolean : Crdt -> Maybe Bool
boolean (MkDPair SBoolean reg) = reg_value reg
boolean _ = Nothing

booleans : Crdt -> Maybe (List Bool)
booleans (MkDPair SBoolean reg) = Just (reg_values reg)
booleans _ = Nothing

number : Crdt -> Maybe Nat
number (MkDPair SNumber reg) = reg_value reg
number _ = Nothing

numbers : Crdt -> Maybe (List Nat)
numbers (MkDPair SNumber reg) = Just (reg_values reg)
numbers _ = Nothing

text : Crdt -> Maybe (List Char)
text (MkDPair SText reg) = reg_value reg
text _ = Nothing

texts : Crdt -> Maybe (List (List Char))
texts (MkDPair SText reg) = Just (reg_values reg)
texts _ = Nothing

length : Crdt -> Maybe Nat
length (MkDPair (SArray e s) rga) = Just (rga_length rga)
length _ = Nothing

keys : Crdt -> Maybe (List Key)
keys (MkDPair (SObject m) _) = Just (keys m)
keys _ = Nothing

data Command : Type where
    Assign : PrimitiveValue -> Command
    InsertAt : Maybe Nat -> Value -> Command
    UpdateAt : Nat -> Command -> Command
    RemoveAt : Nat -> Command
    Update : Key -> Command -> Command

data CrdtOp : Type where
    MkAssign : PrimitiveValue -> CrdtOp
    MkInsertAt : Maybe OpId -> Value -> CrdtOp
    MkUpdateAt : OpId -> CrdtOp -> CrdtOp
    MkRemoveAt : OpId -> CrdtOp
    MkUpdate : Key -> CrdtOp -> CrdtOp

make_op : Command -> Crdt -> Maybe CrdtOp
make_op (Assign (Boolean b)) (MkDPair SBoolean reg) = Just (MkAssign (Boolean b))
make_op (Assign (Number n)) (MkDPair SNumber reg) = Just (MkAssign (Number n))
make_op (Assign (Text s)) (MkDPair SText reg) = Just (MkAssign (Text s))
make_op (InsertAt Nothing v) (MkDPair (SArray e s) rga) =
    if validate s v then Just (MkInsertAt Nothing v) else Nothing
make_op (InsertAt (Just n) v) (MkDPair (SArray e s) rga) =
    case (rga_id n rga, validate s v) of
        (Just id, True) => Just (MkInsertAt (Just id) v)
        _ => Nothing
make_op (UpdateAt n cmd) (MkDPair (SArray e s) rga) =
    case rga_idx' n rga of
        Nothing => Nothing
        Just (id, crdt) =>
            case make_op cmd crdt of
                Nothing => Nothing
                Just op => Just (MkUpdateAt id op)
make_op (RemoveAt n) (MkDPair (SArray False s) rga) =
    if rga_length rga > 1
    then assert_total (make_op (RemoveAt n) (MkDPair (SArray True s) rga))
    else Nothing
make_op (RemoveAt n) (MkDPair (SArray True s) rga) =
    case rga_idx' n rga of
        Nothing => Nothing
        Just (id, _) => Just (MkRemoveAt id)
make_op (Update k cmd) (MkDPair (SObject m) crdt) =
    case get k crdt of
        Nothing => Nothing
        Just crdt => make_op cmd crdt
make_op _ _ = Nothing


to_value : (s : Schema ** crdt_of s) -> Value
to_value (MkDPair SNull _) = Null
to_value (MkDPair SBoolean reg) = Primitive (Boolean (fromMaybe False (reg_value reg)))
to_value (MkDPair SNumber reg) = Primitive (Number (fromMaybe 0 (reg_value reg)))
to_value (MkDPair SText reg) = Primitive (Text (fromMaybe [] (reg_value reg)))
to_value (MkDPair (SArray e s) rga) = Array (map (assert_total to_value) (rga_to_list rga))
to_value (MkDPair (SObject m) crdt) = Object (map (assert_total to_value) crdt)

from_value' : (id : OpId) -> (e : Bool) -> (s : Schema) -> (v : List Value) -> Maybe (Rga (crdt_of s))

from_value : (id : OpId) -> (s : Schema) -> (v : Value) -> Maybe Crdt
{-from_value' id e s [] = Just (SArray True s ** [])
from_value' id e s (v :: []) =
    case from_value id s v of
        Nothing => Nothing
        Just crdt => Just (Cons (MkRgaElem id crdt False) [])
from_value' id e s (x :: xs) =
    let id' = record { uop_id $= (1+) } id
    in case (from_value id' s x, from_value id (SArray e s) (Array xs)) of
        (Just crdt, Just (_ ** rga)) => Just (SArray e s ** (Cons (MkRgaElem id' crdt False) ?rga))
        _ => Nothing
from_value : (id : OpId) -> (s : Schema) -> (v : Value) -> Maybe Crdt
from_value id SNull Null = Just (SNull ** (insert id () Empty))
from_value id SBoolean (Primitive (Boolean b)) = Just (SBoolean ** (insert id b Empty))
from_value id SNumber (Primitive (Number n)) = Just (SNumber ** (insert id n Empty))
from_value id SText (Primitive (Text s)) = Just (SText ** (insert id s Empty))
from_value id (SArray True s) (Array []) = Just (SArray True s ** [])
from_value id (SArray False s) (Array (v :: [])) =
    case from_value id s v of
        Nothing => Nothing
        Just crdt => Just (SArray False s ** (Cons (MkRgaElem id crdt False) []))
from_value id (SArray e s) (Array (x :: xs)) =
    let id' = record { uop_id $= (1+) } id
    in case (from_value id' s x, from_value id (SArray e s) (Array xs)) of
        (Just crdt, Just (_ ** rga)) => Just (SArray e s ** (Cons (MkRgaElem id' crdt False) ?rga))
        _ => Nothing
from_value id (SObject m) v = ?from_value_rhs_6
from_value _ _ _ = Nothing-}


apply_op : Op CrdtOp -> (s : Schema ** crdt_of s) -> Maybe (s : Schema ** crdt_of s)
apply_op (MkOp rid deps (MkAssign (Boolean b))) (MkDPair SBoolean crdt) =
    Just (SBoolean ** reg_apply_op (MkOp rid deps (RegAssign b)) crdt)
apply_op (MkOp rid deps (MkAssign (Number n))) (MkDPair SNumber crdt) =
    Just (SNumber ** reg_apply_op (MkOp rid deps (RegAssign n)) crdt)
apply_op (MkOp rid deps (MkAssign (Text s))) (MkDPair SText crdt) =
    Just (SText ** reg_apply_op (MkOp rid deps (RegAssign s)) crdt)
apply_op op@(MkOp rid deps (MkInsertAt id v)) (MkDPair (SArray e s) crdt) with (validate s v)
    apply_op op@(MkOp rid deps (MkInsertAt id v)) (MkDPair (SArray e s) crdt) | False = Nothing
    apply_op op@(MkOp rid deps (MkInsertAt id v)) (MkDPair (SArray e s) crdt) | True =
        case from_value (op_id op) s v of
            Nothing => Nothing
            Just rga =>
                case rga_apply_op (MkOp rid deps (RgaInsert rga id)) crdt of
                    Just crdt => Just (SArray e s ** crdt)
                    Nothing => Nothing
apply_op (MkOp rid deps (MkUpdateAt id op)) (MkDPair (SArray e s) crdt) =
    case rga_get id crdt of
        Nothing => Nothing
        Just crdt' =>
            case apply_op (MkOp rid deps op) crdt' of
                Nothing => Nothing
                Just crdt' =>
                    case rga_update id crdt' crdt of
                        Nothing => Nothing
                        Just crdt => Just (SArray e s ** crdt)
apply_op (MkOp rid deps (MkRemoveAt id)) (MkDPair (SArray e s) crdt) =
    -- TODO don't violate e constraint
    case rga_remove id crdt of
        Just crdt => Just (SArray e s ** crdt)
        Nothing => Nothing
apply_op (MkOp rid deps (MkUpdate k op)) (SObject m ** crdt) =
    case get k crdt of
        Nothing => Nothing
        Just crdt' =>
            case apply_op (MkOp rid deps op) crdt' of
                Nothing => Nothing
                Just crdt' => Just (SObject m ** insert k crdt' crdt)
apply_op _ _ = Nothing

apply_ops : (s : Schema) -> List (Op CrdtOp) -> Maybe Crdt
apply_ops s xs = ?apply_ops_rhs



transform_op : Lens -> Op CrdtOp -> Op CrdtOp

preserves_schema : (op : Op CrdtOp) -> (s, s' : Schema) -> (crdt : crdt_of s) -> (crdt' : crdt_of s') ->
    apply_op op (s ** crdt) = Just (s' ** crdt') -> s = s'

preserves_validity : (op : Op CrdtOp) -> (crdt, crdt' : Crdt) ->
    validate s (to_value crdt) = True -> apply_op op crdt = Just crdt' ->
    validate s (to_value crdt') = True

convergence : (s : Schema) -> (a, b : List (Op CrdtOp)) ->
    History a b -> apply_ops s a = apply_ops s b

{-equivalence : (l : Lens) -> (s, s' : Schema) -> (v, v' : Value) -> (ops, ops' : List (Op CrdtOp)) ->
    (transform_schema l s = Just s') -> (transform_value l v = v') -> (transform_op l op = op') ->
    (crdt : crdt_of s) -> (to_value' s crdt = v) -> (validate s v = True) ->
    (apply_op op (s ** crdt) = Just (s ** crdt') -> (to_value' s' crdt' = v')-}

{-
remove_all_commutes : Eq k => (m : Map k v) -> (ks, ks' : List k) ->
    (remove_all ks $ remove_all ks' m) = (remove_all ks' $ remove_all ks m)

reg_mut_commutes : (k : PrimitiveKind) -> (id, id' : OpId) -> (op, op' : RegOp) ->
    (m : Register k) -> Not (id = id') ->
    (reg_mut {k} id op $ reg_mut {k} id' op' m) = (reg_mut {k} id' op' $ reg_mut {k} id op m)
reg_mut_commutes k id id' (Assign val) op' m f = ?reg_mut_commutes_rhs_1
reg_mut_commutes k id id' Remove (Assign val) m f = ?reg_mut_commutes_rhs_3
reg_mut_commutes k id id' Remove Remove m f = ?reg_mut_commutes_rhs_4

remove_all_reg_mut_commutes : (k : PrimitiveKind) -> (m : Register k) -> (op, op' : Op RegOp) ->
    lamport op = lamport op' ->
    (remove_all op.deps $ reg_mut {k} (op_id op') op'.mut m) = (reg_mut {k} (op_id op') op'.mut $ remove_all op.deps m)

reg_update_commutes : (k : PrimitiveKind) -> (op, op' : Op RegOp) -> (m : Register k) -> lamport op = lamport op' ->
    (reg_update {k} op $ reg_update {k} op' m) = (reg_update {k} op' $ reg_update {k} op m)
reg_update_commutes k op op' m prf with (reg_op_valid {k} op, reg_op_valid {k} op') proof prf1
    reg_update_commutes k (MkOp _ _ _) (MkOp _ _ _) m prf | (False, False) =
        rewrite cong fst prf1 in rewrite cong snd prf1 in Refl
    reg_update_commutes k (MkOp _ _ _) (MkOp _ _ _) m prf | (False, True) =
        rewrite cong fst prf1 in rewrite cong snd prf1 in Refl
    reg_update_commutes k (MkOp _ _ _) (MkOp _ _ _) m prf | (True, False) =
        rewrite cong fst prf1 in rewrite cong snd prf1 in Refl
    reg_update_commutes k op@(MkOp r1 d1 m1) op'@(MkOp r2 d2 m2) m prf | (True, True) =
        rewrite cong fst prf1 in rewrite cong snd prf1 in
        rewrite remove_all_reg_mut_commutes k (remove_all d2 m) op op' prf in
        rewrite remove_all_reg_mut_commutes k (remove_all d1 m) op' op (sym prf) in
        rewrite remove_all_commutes m d2 d1 in
        let inv = op_id_invariant op' op (sym prf) in
        rewrite reg_mut_commutes k (op_id op') (op_id op) m2 m1 (remove_all d1 (remove_all d2 m)) inv in Refl

convergence : (k : PrimitiveKind) -> (a, b : List (Op RegOp)) ->
    History a b -> reg_apply {k} a = reg_apply {k} b
convergence k [] [] HNil = Refl
convergence k (op :: xs) (op :: ys) (HSkip op prf h) =
    rewrite convergence k xs ys h in Refl
convergence k (op :: (op' :: xs)) (op' :: (op :: xs)) (HSwap op op' prf prf1 h) =
    reg_update_commutes k op op' (reg_apply xs) prf
convergence k a b (HTrans {ys} h h') =
    let c1 = convergence k a ys h
        c2 = convergence k ys b h'
    in rewrite c1 in rewrite c2 in Refl
-}
