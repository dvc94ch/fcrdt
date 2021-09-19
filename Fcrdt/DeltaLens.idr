module Fcrdt.DeltaLens

import Data.List
import Data.Maybe
import Fcrdt.Delta
import Fcrdt.Lens
import Fcrdt.Map

%default total

data CrdtDots =
      Null
    | Boolean DotSet
    | Counter DotSet
    | Number (DotFun Nat)
    | Text (DotList Char)
    | Array (DotList CrdtDots)
    | Object (DotMap Key CrdtDots)

DotStore CrdtDots where
    empty = Null
    dots Null = Empty
    dots (Boolean s) = assert_total $ dots s
    dots (Counter s) = assert_total $ dots s
    dots (Number s) = assert_total $ dots s
    dots (Text s) = assert_total $ dots s
    dots (Array s) = assert_total $ dots s
    dots (Object s) = assert_total $ dots s

Crdt : Type
Crdt = Causal CrdtDots

Lattice Crdt where
    join (Boolean x, c) (Boolean x', c') = (Boolean $ fst $ assert_total $ join (x, c) (x', c'), c `union` c')
    join (Counter x, c) (Counter x', c') = (Counter $ assert_total $ join x x', c `union` c')
    join (Number x, c) (Number x', c') = (Number $ fst $ assert_total $ join (x, c) (x', c'), c `union` c')
    join (Text x, c) (Text x', c') = (Text $ fst $ assert_total $ join (x, c) (x', c'), c `union` c')
    join (Array x, c) (Array x', c') = (Array $ fst $ assert_total $ join (x, c) (x', c'), c `union` c')
    join (Object x, c) (Object x', c') = (Object $ fst $ assert_total $ join (x, c) (x', c'), c `union` c')
    join (_, c) (_, c') = (Null, c `union` c')


-- Accessors
null : Crdt -> Maybe Unit
null (Null, _) = Just ()
null _ = Nothing

bool : Crdt -> Maybe Bool
bool (Boolean ewf, c) = Just $ ewf_read (ewf, c)
bool _ = Nothing

number : Crdt -> Maybe Nat
number (Counter gc, _) = Just $ gc_value gc
number (Number mvr, c) = Just $ fromMaybe 0 $ head' $ mvr_read (mvr, c)
number _ = Nothing

idx : Nat -> Crdt -> Maybe Crdt
idx n (Array y, c) = yata_idx n (y, c)
idx _ _ = Nothing

length : Crdt -> Maybe Nat
length (Text y, c) = Just $ yata_length (y, c)
length (Array y, c) = Just $ yata_length (y, c)
length _ = Nothing

text : Crdt -> Maybe (List Char)
text (Text y, c) = Just $ map fst $ yata_map (y, c)
text _ = Nothing

get : Key -> Crdt -> Maybe Crdt
get k (Object orm, c) = orm_get k (orm, c)
get _ _ = Nothing

keys : Crdt -> Maybe (List Key)
keys (Object orm, c) = Just (keys orm)
keys _ = Nothing

-- Mutators
enable : DeltaMutator Crdt
enable i (Boolean ewf, c) =
    let (ewf, c) = ewf_enable i (ewf, c)
    in (Boolean ewf, c)
enable _ (_, c) = (Null, c)

disable : DeltaMutator Crdt
disable i (Boolean ewf, c) =
    let (ewf, c) = ewf_disable i (ewf, c)
    in (Boolean ewf, c)
disable _ (_, c) = (Null, c)

inc : Nat -> DeltaMutator Crdt
inc n i (Counter gc, c) = (Counter (gc_inc n i gc), c)
inc _ _ (_, c) = (Null, c)

assign : Nat -> DeltaMutator Crdt
assign n i (Number mvr, c) =
    let (mvr, c) = mvr_write n i (mvr, c)
    in (Number mvr, c)
assign _ _ (_, c) = (Null, c)

insert_char_at : Nat -> Char -> DeltaMutator Crdt
insert_char_at n v i (Text y, c) =
    let (y, c) = yata_insert n v i (y, c)
    in (Text y, c)
insert_char_at _ _ _ (_, c) = (Null, c)

insert_at : Nat -> Crdt -> DeltaMutator Crdt
insert_at n (v, c') i (Array y, c) =
    let (y, c) = yata_insert n v i (y, c)
    in (Array y, c `union` c')
insert_at _ _ _ (_, c) = (Null, c)

update_at : Nat -> DeltaMutator Crdt -> DeltaMutator Crdt
update_at n f i (Array y, c) =
    let (y, c) = yata_update n f i (y, c)
    in (Array y, c)
update_at _ _ _ (_, c) = (Null, c)

remove_at : Nat -> DeltaMutator Crdt
remove_at n i (Text y, c) =
    let (y, c) = yata_remove n i (y, c)
    in (Text y, c)
remove_at n i (Array y, c) =
    let (y, c) = yata_remove n i (y, c)
    in (Array y, c)
remove_at _ _ (_, c) = (Null, c)

update : Key -> DeltaMutator Crdt -> DeltaMutator Crdt
update k f i (Object orm, c) =
    let (orm, c) = orm_apply k f i (orm, c)
    in (Object orm, c)
update _ _ _ (_, c) = (Null, c)


-- cambria
mutual
    public export
    validate_properties : List Key -> ORMap Key CrdtDots -> Map Key Schema -> Bool
    validate_properties [] _ _ = True
    validate_properties (k :: ks) (orm, c) sm with (get k orm, get k sm)
        validate_properties (k :: ks) (orm, c) sm | (Just v, Just s) =
             assert_total (validate s (v, c)) && validate_properties ks (orm, c) sm
        validate_properties (k :: ks) (orm, c) sm | (_, _) = False

    public export
    validate : Schema -> Crdt -> Bool
    validate SNull (Null, _) = True
    validate SBoolean (Boolean _, _) = True
    validate SCounter (Counter _, _) = True
    validate SNumber (Number _, _) = True
    validate SText (Text _, _) = True
    validate (SArray False s) (Array y, c) =
        if yata_length (y, c) > 0
        then assert_total $ validate (SArray True s) (Array y, c)
        else False
    validate (SArray True s) (Array y, c) =
        foldr (\a, b => a && b) True $ map (\x => assert_total $ validate s x) $ yata_map (y, c)
    -- not all keys have to be present in the ormap
    validate (SObject sm) (Object orm, c) = validate_properties (keys orm) (orm, c) sm
    validate _ _ = False

transform_crdt : Lens -> Crdt -> Crdt
transform_crdt (Make KNull) (_, c) = (Null, c)
transform_crdt (Make (KPrimitive KBoolean)) (_, c) = (Boolean $ fst ewf_empty, c)
transform_crdt (Make (KPrimitive KCounter)) (_, c) = (Counter gc_empty, c)
transform_crdt (Make (KPrimitive KNumber)) (_, c) = (Number $ fst mvr_empty, c)
transform_crdt (Make (KPrimitive KText)) (_, c) = (Text $ fst yata_empty, c)
transform_crdt (Make KArray) (_, c) = (Array $ fst yata_empty, c)
transform_crdt (Make KObject) (_, c) = (Object $ fst orm_empty, c)
transform_crdt (Destroy _) (_, c) = (Null, c)
transform_crdt (AddProperty k) (orm, c) =  (orm, c)
transform_crdt (RemoveProperty k) (Object orm, c) = (Object $ remove k orm, c)
transform_crdt (RenameProperty k1 k2) (Object orm, c) =
    case get k1 orm of
        Just v => (Object $ insert k2 v $ remove k1 orm, c)
        Nothing => (Object orm, c)
transform_crdt (HoistProperty h t) (Object m, c) =
    case get h m of
        Just (Object hm) =>
            case get t hm of
                Just v => (Object $ insert h (Object $ remove t hm) $ insert t v m, c)
                Nothing => (Object m, c)
        _ => (Object m, c)
transform_crdt (PlungeProperty h t) (Object m, c) =
    case (get h m, get t m) of
        (Just (Object hm), Just v) => (Object $ insert h (Object $ insert t v hm) $ remove t m, c)
        _ => (Object m, c)
transform_crdt (LensIn k l) (Object m, c) =
    case get k m of
        Just v => (Object $ insert k (fst $ transform_crdt l (v, c)) m, c)
        Nothing => (Object m, c)
transform_crdt Wrap (v, c) = (Array [MkBlock (0, (max 0 c)) Nothing Nothing (Just v)], c)
transform_crdt Head (Array y, c) =
    case yata_idx 0 (y, c) of
        Just v => v
        Nothing => (Array y, c)
transform_crdt (LensMap l) (Array y, c) =
    (Array $ map (\b => record { value $= map $ (\x => fst $ transform_crdt l (x, c)) } b) y, c)
{-transform_crdt (Convert _ b m) (Primitive v) =
    case convert_prim v m of
        Just v => (Primitive v)
        Nothing => case b of
            KBoolean => Primitive (Boolean False)
            KNumber => Primitive (Number 0)
            KText => Primitive (Text [])-}
transform_crdt _ v = v

-- convergence properties
join_idempotence : (a : Crdt) -> join a a = a

join_associativity : (a, b, c : Crdt) -> join (join a b) c = join a (join b c)

join_commutativity : (a, b : Crdt) -> join a b = join b a

-- cambria properties
join_preserves_validity : (s : Schema) -> (a, b : Crdt) ->
    validate s a = True -> validate s b = True -> validate s (join a b) = True

lens_preserves_validity : (l : Lens) -> (s, s' : Schema) -> (c, c' : Crdt) ->
    transform_schema l s = Just s' -> transform_crdt l c = c' ->
    validate s c = True -> validate s' c' = True
