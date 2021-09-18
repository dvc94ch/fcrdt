module Fcrdt.Delta

import Data.Nat
import Data.List
import Data.Maybe
import Fcrdt.Map

%default total

-- convergence follows from associativity, commutativity and idempotence
-- preserving causality means precondition needs to be met and advances to post condition

public export
Dot : Type
Dot = (Nat, Nat)

||| Clock
public export
Clock : Type -- called CausalContext in the delta crdt paper
Clock = Map Nat Nat

%name Clock c, c', c''

max : Nat -> Clock -> Nat
max i c = get_or 0 i c

next : Nat -> Clock -> Dot
next i c = (i, max i c + 1)

after : Dot -> Clock -> Bool
after (i, n) c = n > max i c

to_clock : Dot -> Clock
to_clock (k, v) = insert k v Empty

union : Clock -> Clock -> Clock
union c1 c2 = union' (pairs c1) c2 where
    union' : List (Nat, Nat) -> Clock -> Clock
    union' [] m = m
    union' ((k, v) :: xs) m =
        let m' = union' xs m in
            if v > max k m then insert k v m' else m'

infixr 9 `union`

intersect : Clock -> Clock -> Clock
intersect m1 m2 = from_pairs $
    map (\k => (k, (min (max k m1) (max k m2)))) $
    intersect (keys m1) (keys m2)

remove : Clock -> Clock -> Clock
remove c1 c2 = remove_all (keys c2) c1


||| Lattice
public export
interface Lattice a where
    join : a -> a -> a

infixr 9 `join`

public export
Lattice a => Lattice (Maybe a) where
    join Nothing b = b
    join (Just a) Nothing = Just a
    join (Just a) (Just b) = Just (a `join` b)

public export
Lattice Unit where
    join () () = ()

public export
Lattice Bool where
    join a b = a || b

public export
Lattice Nat where
    join = max

public export
Lattice Char where
    join a b = max (cast a) (cast b)

public export
Causal : (a : Type) -> Type
Causal a = (a, Clock)

public export
interface DotStore a where
    empty : a
    dots : a -> Clock

public export
DeltaMutator : (a : Type) -> Type
DeltaMutator a = Nat -> a -> a

public export
mut : DotStore v => DeltaMutator v -> DeltaMutator (Causal v)
mut f i (s, c) = (f i s, c)

public export
acc : (v -> v') -> Causal v -> v'
acc f (s, c) = f s


||| DotSet
public export
DotSet : Type
DotSet = Clock

%name DotSet s, s', s''

public export
DotStore DotSet where
    empty = empty
    dots s = s

public export
Lattice (Causal DotSet) where
    join (s, c) (s', c') = (intersect s s' `union` remove s c' `union` remove s' c, c `union` c')


||| DotFun
public export
DotFun : (a : Type) -> Type
DotFun a = Map Dot a

%name DotFun s, s', s''

public export
Lattice a => DotStore (DotFun a) where
    empty = empty
    dots s = from_pairs $ keys s

public export
Lattice a => Lattice (Causal (DotFun a)) where
    join (m, c) (m', c') =
        let ks = intersect (keys m) (keys m')
            int = mapMaybe (\k => (map (\v => (k, v)) (get k m `join` get k m'))) ks
            rm1 = filter (\(d, v) => after d c') $ pairs m
            rm2 = filter (\(d, v) => after d c) $ pairs m'
        in (from_pairs $ int ++ rm1 ++ rm2, c `union` c')
        -- works because sets are disjoint


||| DotMap
public export
DotMap : (k : Type) -> (v : Type) -> Type
DotMap k v = Map k v

%name DotMap s, s', s''

public export
Eq k => DotStore v => DotStore (DotMap k v) where
    empty = empty
    dots m = foldr union Empty $ map dots $ values m

public export
Eq k => DotStore v => Lattice (Causal v) => Lattice (Causal (DotMap k v)) where
    join (m, c) (m', c') =
        let ks = keys m ++ keys m'
            mm' = mapMaybe (\k => (map (\v => (k, v)) (f k))) ks
        in (from_pairs mm', c `union` c')
        where
            f : k -> Maybe v
            f k = map fst (map (\v => (v, c)) (get k m) `join` map (\v => (v, c')) (get k m'))


||| Grow only counter
public export
GCounter : Type
GCounter = DotSet

public export
gc_empty : GCounter
gc_empty = Empty

public export
gc_inc : Nat -> DeltaMutator GCounter
gc_inc n i m = insert i ((get_or 0 i m) + n) m

public export
gc_value : GCounter -> Nat
gc_value m = sum (values m)

public export
Lattice GCounter where
    join = union

test_gc_inc' : GCounter
test_gc_inc' = gc_inc 1 0 (gc_inc 1 1 (gc_inc 1 0 Delta.gc_empty))

test_gc_inc : IO ()
test_gc_inc = putStrLn $ show $ 3 == gc_value test_gc_inc'

test_gc_join' : GCounter
test_gc_join' = gc_inc 1 0 (gc_inc 1 1 (gc_inc 1 0 Delta.gc_empty)) `join` gc_inc 1 2 Delta.gc_empty

test_gc_join : IO ()
test_gc_join = putStrLn $ show $ 4 == gc_value test_gc_join'

||| Positive negative counter
public export
PNCounter : Type
PNCounter = (GCounter, GCounter)

public export
pnc_empty : PNCounter
pnc_empty = (Empty, Empty)

public export
pnc_inc : Nat -> DeltaMutator PNCounter
pnc_inc k i (p, _) = (gc_inc k i p, Empty)

public export
pnc_dec : Nat -> DeltaMutator PNCounter
pnc_dec k i (_, n) = (Empty, gc_inc k i n)

public export
pnc_value : PNCounter -> Int
pnc_value (p, n) = cast (gc_value p) - cast (gc_value n)

||| Enable wins flag
public export
EWFlag : Type
EWFlag = Causal DotSet

public export
ewf_empty : EWFlag
ewf_empty = (Empty, Empty)

public export
ewf_enable : DeltaMutator EWFlag
ewf_enable i (s, c) = let d = to_clock (next i c) in (d, d `union` s)

public export
ewf_disable : DeltaMutator EWFlag
ewf_disable _ (s, _) = (Empty, s)

public export
ewf_read : EWFlag -> Bool
ewf_read (Empty, _) = False
ewf_read ((Update _ _ _), _) = True

test_read_empty : ewf_read Delta.ewf_empty = False
test_read_empty = Refl

test_read_enabled : ewf_read (ewf_enable 0 Delta.ewf_empty) = True
test_read_enabled = Refl

test_read_disabled : ewf_read (ewf_disable 0 (ewf_enable 0 Delta.ewf_empty)) = False
test_read_disabled = Refl

test_enable_wins' : EWFlag
test_enable_wins' = join (ewf_disable 0 (ewf_enable 0 Delta.ewf_empty)) (ewf_enable 1 Delta.ewf_empty)

test_enable_wins : IO ()
test_enable_wins = putStrLn $ show $ True == ewf_read test_enable_wins'

||| Disable wins flag
public export
DWFlag : Type
DWFlag = EWFlag

public export
dwf_empty : DWFlag
dwf_empty = ewf_empty

public export
dwf_enable : DeltaMutator DWFlag
dwf_enable = ewf_disable

public export
dwf_disable : DeltaMutator DWFlag
dwf_disable = ewf_enable

public export
dwf_read : DWFlag -> Bool
dwf_read f = not (ewf_read f)

||| Multi value register
public export
MVReg : (a : Type) -> Type
MVReg a = Causal (DotFun a)

public export
mvr_empty : MVReg a
mvr_empty = (Empty, Empty)

public export
mvr_write : a -> DeltaMutator (MVReg a)
mvr_write v i (m, c) =
    let d = next i c
    in (insert d v empty, to_clock d `union` from_pairs (keys m))

public export
mvr_clear : DeltaMutator (MVReg a)
mvr_clear i (m, c) = (Empty, from_pairs $ keys m)

public export
mvr_read : MVReg a -> List a
mvr_read (m, c) = values m

test_mvr_write_seq' : MVReg Nat
test_mvr_write_seq' = mvr_write 1 0 $ mvr_write 0 0 mvr_empty

test_mvr_write_seq : IO ()
test_mvr_write_seq = putStrLn $ show $ mvr_read test_mvr_write_seq'

test_mvr_write_conc' : MVReg Nat
test_mvr_write_conc' = mvr_write 0 0 mvr_empty `join` mvr_write 1 1 mvr_empty

test_mvr_write_conc : IO ()
test_mvr_write_conc = putStrLn $ show $ mvr_read test_mvr_write_conc'


||| Add wins set
public export
AWSet : (a : Type) -> Type
AWSet a = Causal (DotMap a DotSet)

public export
aws_empty : AWSet a
aws_empty = (Empty, Empty)

public export
aws_add : Eq a => a -> DeltaMutator (AWSet a)
aws_add e i (m, c) =
    let d = to_clock $ next i c
    in (insert e d m, d `union` get_or d e m)

public export
aws_remove : Eq a => a -> DeltaMutator (AWSet a)
aws_remove e i (m, c) = (remove e m, get_or c e m)

public export
aws_clear : Eq a => DeltaMutator (AWSet a)
aws_clear i (m, c) = (empty, dots m)

public export
aws_elements : Eq a => AWSet a -> List a
aws_elements (m, c) = keys m

test_aws_seq' : AWSet Nat
test_aws_seq' = aws_remove 2 0 $ aws_add 0 0 $ aws_add 1 0 $ aws_add 0 0 $ aws_add 2 0 aws_empty

test_aws_seq : IO ()
test_aws_seq = putStrLn $ show $ aws_elements test_aws_seq'

test_aws_conc' : AWSet Nat
test_aws_conc' = aws_remove 2 0 aws_empty `join` aws_add 2 0 aws_empty

test_aws_conc : IO ()
test_aws_conc = putStrLn $ show $ aws_elements test_aws_conc'

||| Observe remove map
public export
ORMap : (k : Type) -> (v : Type) -> Type
ORMap k v = Causal (DotMap k v)

public export
orm_empty : ORMap k v
orm_empty = (Empty, Empty)

public export
orm_apply : Eq k => DotStore v => k -> (DeltaMutator (Causal v)) -> DeltaMutator (ORMap k v)
orm_apply k f i (m, c) =
    let v = get_or empty k m
        r = f i (v, c)
    in (insert k (fst r) empty, snd r)

public export
orm_remove : Eq k => DotStore v => k -> DeltaMutator (ORMap k v)
orm_remove k i (m, c) = (empty, fromMaybe empty $ map dots (get k m))

public export
orm_clear : Eq k => DotStore v => DeltaMutator (ORMap k v)
orm_clear i (m, c) = (empty, dots m)

public export
orm_get : Eq k => k -> ORMap k v -> Maybe (Causal v)
orm_get k (m, c) = map (\v => (v, c)) $ get k m

test_orm' : ORMap Nat (DotFun Nat)
test_orm' = orm_apply 1 (mvr_write 1) 0 orm_empty `join` orm_apply 0 (mvr_write 0) 0 orm_empty

test_orm : IO ()
test_orm = putStrLn $ show $ map mvr_read $ orm_get 0 test_orm'

test_orm2' : ORMap Nat GCounter
test_orm2' =
    let inc = \k => orm_apply k (mut (gc_inc 2)) 0
    in inc 0 $ inc 0 orm_empty

test_orm2 : IO ()
test_orm2 = putStrLn $ show $ map (acc gc_value) $ orm_get 0 test_orm2'

||| YATA (doubly linked list)
record Block v where
    constructor MkBlock
    dot : Dot
    left : Maybe Dot
    right : Maybe Dot
    value : Maybe v

%name Block blk, blk', blk''

public export
Yata : (v : Type) -> Type
Yata v = Causal (List (Block v))

yata_empty : Yata v
yata_empty = ([], Empty)

yata_deleted : Block v -> Bool
yata_deleted blk = isNothing blk.value

yata_dots : DotStore v => Block v -> Clock
yata_dots blk =
    let vdots = fromMaybe empty $ map dots blk.value
    in to_clock blk.dot `union` vdots

public export
DotStore Char where
    empty = 'a'
    dots s = empty

public export
Lattice (Causal Char) where
    join (a, c) (b, c') = (join a b, c `union` c')

public export
DotStore v => DotStore (List (Block v)) where
    empty = []
    dots s = foldr (\b, acc => yata_dots b `union` acc) empty s

YataReduce : (v : Type) -> Type
YataReduce v = Clock -> Block v -> Yata v -> Maybe (Yata v)

yata_reduce_same : Lattice (Causal v) => YataReduce v
yata_reduce_same c x ([], c') = Nothing
yata_reduce_same c x (x' :: xs', c') with (x.dot == x'.dot)
    yata_reduce_same c x (x' :: xs', c') | True =
        let v'' =
                case (x.value, x'.value) of
                    (Just v, Just v') => Just $ fst $ join (v, c) (v', c')
                    _ => Nothing
        in Just ((record { value = v'' } x') :: xs', c')
    yata_reduce_same c x (x' :: xs', c') | False =
        case yata_reduce_same c x (xs', c') of
            Nothing => Nothing
            Just (xs', c') => Just (x' :: xs', c')

yata_split_left : Maybe Dot -> List (Block v) -> Maybe (List (Block v), List (Block v))
yata_split_left Nothing xs = Just ([], xs)
yata_split_left (Just d) [] = Nothing
yata_split_left (Just d) (x :: xs) with (d == x.dot)
    yata_split_left (Just d) (x :: xs) | True = Just ([x], xs)
    yata_split_left (Just d) (x :: xs) | False with (yata_split_left (Just d) xs)
        yata_split_left (Just d) (x :: xs) | False | Nothing = Nothing
        yata_split_left (Just d) (x :: xs) | False | Just (l, xs') = Just (x :: l, xs')

yata_split_right : Maybe Dot -> List (Block v) -> Maybe (List (Block v), List (Block v))
yata_split_right Nothing xs = Just (xs, [])
yata_split_right (Just d) [] = Nothing
yata_split_right (Just d) (x :: xs) with (d == x.dot)
    yata_split_right (Just d) (x :: xs) | True = Just ([], x :: xs)
    yata_split_right (Just d) (x :: xs) | False with (yata_split_right (Just d) xs)
        yata_split_right (Just d) (x :: xs) | False | Nothing = Nothing
        yata_split_right (Just d) (x :: xs) | False | Just (xs', r) = Just (x :: xs, r)

yata_insert_sorted : Block v -> List (Block v) -> List (Block v)
yata_insert_sorted x [] = [x]
yata_insert_sorted x (x' :: xs') =
    if x.dot < x'.dot
    then x :: x' :: xs'
    else x' :: yata_insert_sorted x xs'

yata_reduce_insert : Lattice (Causal v) => YataReduce v
yata_reduce_insert c x (xs', c') = do
    (l, xs') <- yata_split_left x.left xs'
    (xs', r) <- yata_split_right x.right xs'
    Just $ (l ++ yata_insert_sorted x xs' ++ r, c')

yata_reduce : Lattice (Causal v) => YataReduce v -> Clock -> List (Block v) -> Yata v -> (List (Block v), Yata v)
yata_reduce f c [] y = ([], y)
yata_reduce f c (x :: xs) y =
    let (xs, y') = yata_reduce f c xs y
    in case f c x y' of
        Just y'' => (xs, y'')
        Nothing => (x :: xs, y')

yata_rec : Lattice (Causal v) => YataReduce v -> Clock -> List (Block v) -> Yata v -> Yata v
yata_rec f c xs y with (yata_reduce f c xs y)
    yata_rec f c xs y | ([], y') = y'
    yata_rec f c xs y | (xs', y') = assert_total $ yata_rec f c xs' y'

public export
Lattice (Causal v) => Lattice (Yata v) where
    join (xs, c) y =
        let (xs, y) = yata_reduce yata_reduce_same c xs y
            (xs', c') = yata_rec yata_reduce_insert c xs y
        in (xs', c `union` c')

public export
yata_insert : DotStore v => Nat -> v -> DeltaMutator (Yata v)
yata_insert 0 v i ([], c) =
    let d = next i c
    in ([MkBlock d Nothing Nothing (Just v)], to_clock d `union` c)
yata_insert 0 v i (r :: xs, c) =
    let d = next i c
    in ([MkBlock d Nothing (Just r.dot) (Just v)], to_clock d `union` c)
yata_insert (S 0) v i (l :: [], c) =
    let d = next i c
    in ([MkBlock d (Just l.dot) Nothing (Just v)], to_clock d `union` c)
yata_insert (S 0) v i (l :: r :: xs, c) =
    let d = next i c
    in ([MkBlock d (Just l.dot) (Just r.dot) (Just v)], to_clock d `union` c)
yata_insert (S n) v i (x :: xs, c) = yata_insert n v i (xs, c)
yata_insert n v i ([], c) = ([], empty)

public export
yata_remove : DotStore v => Nat -> DeltaMutator (Yata v)
yata_remove n i ([], c) = ([], empty)
yata_remove n i (x :: xs, c) with (yata_deleted x)
    yata_remove n i (x :: xs, c) | True = assert_total $ yata_remove n i (xs, c)
    yata_remove (S n) i (x :: xs, c) | False = assert_total $ yata_remove n i (xs, c)
    yata_remove 0 i (x :: xs, c) | False = ([record { value = Nothing } x], yata_dots x)

public export
yata_update : DotStore v => Nat -> DeltaMutator (Causal v) -> DeltaMutator (Yata v)
yata_update n f i ([], c) = ([], empty)
yata_update n f i (x :: xs, c) with (x.value)
    yata_update n f i (x :: xs, c) | Nothing = assert_total $ yata_update n f i (xs, c)
    yata_update (S n) f i (x :: xs, c) | Just _ = assert_total $ yata_update n f i (xs, c)
    yata_update 0 f i (x :: xs, c) | Just vv =
        let r = f i (vv, c)
        in ([record { value = Just (fst r) } x], snd r)

yata_values : List (Block v) -> List v
yata_values xs = mapMaybe (\b => b.value) xs

public export
yata_idx : DotStore v => Nat -> Yata v -> Maybe (Causal v)
yata_idx n (xs, c) = map (\x => (x, c)) $ getAt n $ yata_values xs

public export
yata_map : DotStore v => Yata v -> List (Causal v)
yata_map (xs, c) = map (\x => (x, c)) $ yata_values xs

public export
yata_length : DotStore v => Yata v -> Nat
yata_length (xs, c) = length $ yata_values xs


test_yata' : Yata Char
test_yata' =
    let a = yata_insert 0 'a' 0 yata_empty
        b = yata_insert 1 'c' 0 a
        bs = join a b
        c = yata_insert 1 'b' 0 bs
        cs = join c bs
        d = yata_insert 3 'd' 0 cs
        ds = join d cs
        d' = yata_remove 1 0 ds
        ds' = join d' ds
        e = yata_insert 0 'e' 1 yata_empty
        f = yata_insert 0 'f' 1 e
        efs = join e f
        fs = join efs ds'
    in efs

test_yata : IO ()
test_yata = putStrLn $ show $ map fst $ yata_map test_yata'
