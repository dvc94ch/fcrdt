module Fcrdt.DeltaLens

import Data.List
import Fcrdt.Delta
import Fcrdt.Lens
import Fcrdt.Map

%default total

data Crdt =
      Null
    | Boolean (MVReg Bool)
    | Number GCounter
    | Text (Yata Char)
    | Array (Yata Crdt)
    | Object (ORMap Key Crdt)

DotStore Crdt where
    empty = Null
    dots Null = Empty
    dots (Boolean (s, c)) = assert_total (dots s)
    dots (Number m) = assert_total (dots m)
    dots (Text (s, c)) = assert_total (dots s)
    dots (Array (s, c)) = assert_total (dots s)
    dots (Object (s, c)) = assert_total (dots s)

mutual
    join' : Crdt -> Crdt -> Crdt
    join' (Boolean x) (Boolean y) = Boolean (assert_total (join x y))
    join' (Number x) (Number y) = Number (assert_total (join x y))
    join' (Text x) (Text y) = Text (assert_total (join x y))
    join' (Array x) (Array y) = Array (assert_total (join x y))
    join' (Object x) (Object y) = Object (assert_total (join x y))
    join' _ _ = Null

    Lattice Crdt where
        join = join'

    Lattice (Causal Crdt) where
        join (s, _) (s', _) = (join' s s', empty)


-- Accessors
null : Crdt -> Maybe Unit
null Null = Just ()
null _ = Nothing

bool : Crdt -> Maybe Bool
bool (Boolean b) = head' $ mvr_read b
bool _ = Nothing

number : Crdt -> Maybe Nat
number (Number n) = Just (gc_value n)
number _ = Nothing

idx : Nat -> Crdt -> Maybe Crdt
idx n (Array x) = map fst $ yata_idx n x
idx _ _ = Nothing

length : Crdt -> Maybe Nat
length (Text x) = Just $ yata_length x
length (Array x) = Just $ yata_length x
length _ = Nothing

text : Crdt -> Maybe (List Char)
text (Text x) = Just $ map fst $ yata_map x
text _ = Nothing

get : Key -> Crdt -> Maybe Crdt
get k (Object orm) = map fst $ orm_get k orm
get _ _ = Nothing

keys : Crdt -> Maybe (List Key)
keys (Object (m, c)) = Just (keys m)
keys _ = Nothing

-- Mutators
assign : Bool -> DeltaMutator Crdt
assign b i (Boolean mvr) = Boolean (mvr_write b i mvr)
assign _ _ _ = Null

inc : Nat -> DeltaMutator Crdt
inc n i (Number gc) = Number (gc_inc n i gc)
inc _ _ _ = Null

insert_char_at : Nat -> Char -> DeltaMutator Crdt
insert_char_at n v i (Text x) = Text $ yata_insert n v i x
insert_char_at _ _ _ _ = Null

insert_at : Nat -> Crdt -> DeltaMutator Crdt
insert_at n v i (Array x) = Array $ yata_insert n v i x
insert_at _ _ _ _ = Null

update_at : Nat -> DeltaMutator Crdt -> DeltaMutator Crdt
update_at n f i (Array x) = Array $ yata_update n (mut f) i x
update_at _ _ _ _ = Null

remove_at : Nat -> DeltaMutator Crdt
remove_at n i (Text x) = Text $ yata_remove n i x
remove_at n i (Array x) = Array $ yata_remove n i x
remove_at _ _ _ = Null

update : Key -> DeltaMutator Crdt -> DeltaMutator Crdt
update k f i (Object orm) = Object (orm_apply k (mut f) i orm)
update _ _ _ _ = Null


{-
||| Cambria transform
validate : Schema -> Crdt -> Bool

-- idempotence, associativity, commutativity of operations

-- reversible
transform_schema : Lens -> Schema -> Maybe Schema

-- preserves validity
transform_crdt : Lens -> Crdt -> Crdt
transform_crdt lens s = ?transform_rhs
-}
