module Fcrdt.Lens

import Data.List
import Data.Maybe

%default total

data PrimitiveValue =
      Boolean Bool
    | Number Int
    | Text String

Eq PrimitiveValue where
    Boolean b1 == Boolean b2 = b1 == b2
    Number n1 == Number n2 = n1 == n2
    Text t1 == Text t2 = t1 == t2
    _ == _ = False

data PrimitiveKind =
      KBoolean
    | KNumber
    | KText

Eq PrimitiveKind where
    KBoolean == KBoolean = True
    KNumber == KNumber = True
    KText == KText = True
    _ == _ = False

data Key : Type where
    MkKey : Nat -> Key

%name Key key, k, k1, k2

Eq Key where
    MkKey a == MkKey b = a == b

beq_nat : (n: Nat) -> n == n = True
beq_nat 0 = Refl
beq_nat (S k) = beq_nat k

beq_key : (k: Key) -> k == k = True
beq_key (MkKey n) = beq_nat n

mutual
    data Value =
          Primitive PrimitiveValue
        | Array (List Value)
        | Object (Map Value)

    data Map : Type -> Type where
        Empty : Map a
        Entry : Key -> a -> Map a -> Map a

%name Value val, v, v1, v2

%name Map map, m, m1, m2

get : Map a -> Key -> Maybe a
get Empty _ = Nothing
get (Entry k v obj) key = if k == key then Just v else get obj key

insert : Map a -> Key -> a -> Map a
insert Empty key val = Entry key val Empty
insert (Entry k v obj) key val = if k == key then (Entry key val obj) else insert obj key val

delete : Map a -> Key -> Map a
delete Empty key = Empty
delete (Entry k val obj) key = if k == key then obj else delete obj key

every_key_is_eq : Eq a => Map a -> Map a -> Bool
every_key_is_eq Empty _ = True
every_key_is_eq (Entry key x map) m =
    case get map key of
        Just y => x == y
        Nothing => False

Eq a => Eq (Map a) where
    m1 == m2 = every_key_is_eq m1 m2 && every_key_is_eq m2 m1

Eq Value where
    Primitive v1 == Primitive v2 = v1 == v2
    Array vs1 == Array vs2 = assert_total (vs1 == vs2)
    Object ps1 == Object ps2 = assert_total (ps1 == ps2)
    _ == _ = False

data Kind =
      KPrimitive PrimitiveKind
    | KArray
    | KObject

Eq Kind where
    KPrimitive k1 == KPrimitive k2 = k1 == k2
    KArray == KArray = True
    KObject == KObject = True
    _ == _ = False

primitiveKindOf : PrimitiveValue -> PrimitiveKind
primitiveKindOf (Boolean x) = KBoolean
primitiveKindOf (Number x) = KNumber
primitiveKindOf (Text x) = KText

data Schema =
      SFalse
    | SBoolean Bool
    | SNumber Int
    | SText String
    | SArray Bool Schema
    | SObject (Map (Bool, Schema))

validate : Schema -> Value -> Bool
validate SFalse _ = False
validate (SBoolean _) (Primitive (Boolean _)) = True
validate (SBoolean _) _ = False
validate (SNumber _) (Primitive (Number _)) = True
validate (SNumber _) _ = False
validate (SText _) (Primitive (Text _)) = True
validate (SText _) _ = False
validate (SArray allowEmpty schema) (Array []) = allowEmpty
validate (SArray _ schema) (Array (x :: xs)) =
    assert_total (validate schema) x && assert_total (validate (SArray True schema) (Array xs))
validate (SArray _ _) _ = False
validate (SObject smap) (Object vmap) = validateProperties vmap smap && validateRequired smap vmap where
    validateProperties : Map Value -> Map (Bool, Schema) -> Bool
    validateProperties Empty _ = True
    validateProperties (Entry key value vmap) smap with (get smap key)
        validateProperties (Entry key value vmap) _ | Just (_, schema) =
            assert_total (validate schema value) && validateProperties vmap smap
        validateProperties (Entry _ _ _) _ | Nothing = False
    validateRequired : Map (Bool, Schema) -> Map Value -> Bool
    validateRequired Empty _ = True
    validateRequired (Entry _ (False, _) smap) vmap = validateRequired smap vmap
    validateRequired (Entry key (True, _) smap) vmap with (get vmap key)
        validateRequired (Entry _ (True, _) smap) vmap | Just _ = validateRequired smap vmap
        validateRequired (Entry _ (True, _) _) _ | Nothing = False
validate (SObject _) _ = False

data Lens =
      Make Kind
    | Destroy Kind
    | AddProperty Key
    | RemoveProperty Key
    | RenameProperty Key Key
    | HoistProperty Key Key
    | PlungeProperty Key Key
    | WrapProperty
    | HeadProperty
    | AllowEmpty Bool Value
    | LensIn Key Lens
    | LensMap Lens
    | Require Key Bool
    | Default PrimitiveValue PrimitiveValue
    | Convert PrimitiveKind PrimitiveKind (List (PrimitiveValue, PrimitiveValue))

convertIsValid : PrimitiveKind -> PrimitiveKind -> List (PrimitiveValue, PrimitiveValue) -> Bool
convertIsValid _ _ [] = True
convertIsValid kx ky ((x, y) :: map) =
    primitiveKindOf x == kx && primitiveKindOf y == ky && convertIsValid kx ky map

Eq Lens where
    Make k1 == Make k2 = k1 == k2
    Destroy k1 == Destroy k2 = k1 == k2
    AddProperty p1 == AddProperty p2 = p1 == p2
    RemoveProperty p1 == RemoveProperty p2 = p1 == p2
    RenameProperty a1 b1 == RenameProperty a2 b2 = a1 == a2 && b1 == b2
    HoistProperty h1 p1 == HoistProperty h2 p2 = h1 == h2 && p1 == p2
    PlungeProperty h1 p1 == PlungeProperty h2 p2 = h1 == h2 && p1 == p2
    WrapProperty == WrapProperty = True
    HeadProperty == HeadProperty = True
    AllowEmpty b1 v1 == AllowEmpty b2 v2 = b1 == b2 && v1 == v2
    LensIn p1 l1 == LensIn p2 l2 = p1 == p2 && l1 == l2
    LensMap l1 == LensMap l2 = l1 == l2
    Require k1 b1 == Require k2 b2 = k1 == k2 && b1 == b2
    Default v11 v21 == Default v12 v22 = v11 == v12 && v21 == v22
    Convert k11 k21 f1 == Convert k12 k22 f2 = k11 == k12 && k22 == k22 && f1 == f2
    _ == _ = False

reverseLens : Lens -> Lens
reverseLens (Make k) = Destroy k
reverseLens (Destroy k) = Make k
reverseLens (AddProperty x) = RemoveProperty x
reverseLens (RemoveProperty x) = AddProperty x
reverseLens (RenameProperty x y) = RenameProperty y x
reverseLens (HoistProperty x y) = PlungeProperty x y
reverseLens (PlungeProperty x y) = HoistProperty x y
reverseLens WrapProperty = HeadProperty
reverseLens HeadProperty = WrapProperty
reverseLens (AllowEmpty b v) = AllowEmpty (not b) v
reverseLens (LensIn x y) = LensIn x (reverseLens y)
reverseLens (LensMap x) = LensMap (reverseLens x)
reverseLens (Require k b) = Require k (not b)
reverseLens (Default v1 v2) = Default v2 v1
reverseLens (Convert a b m) = Convert b a (map (\(a, b) => (b, a)) m)

applyLensSchema : Lens -> Schema -> Maybe Schema
applyLensSchema (Make (KPrimitive KBoolean)) SFalse = Just (SBoolean False)
applyLensSchema (Make (KPrimitive KNumber)) SFalse = Just (SNumber 0)
applyLensSchema (Make (KPrimitive KText)) SFalse = Just (SText "")
applyLensSchema (Make KArray) SFalse = Just (SArray True SFalse)
applyLensSchema (Make KObject) SFalse = Just (SObject Empty)
applyLensSchema (Make _) _ = Nothing
applyLensSchema (Destroy (KPrimitive KBoolean)) (SBoolean False) = Just SFalse
applyLensSchema (Destroy (KPrimitive KNumber)) (SNumber 0) = Just SFalse
applyLensSchema (Destroy (KPrimitive KText)) (SText "") = Just SFalse
applyLensSchema (Destroy KArray) (SArray True SFalse) = Just SFalse
applyLensSchema (Destroy KObject) (SObject Empty) = Just SFalse
applyLensSchema (Destroy _) _ = Nothing
applyLensSchema (AddProperty key) (SObject smap) =
    case get smap key of
        Just _ => Nothing
        Nothing => Just (SObject (insert smap key (False, SFalse)))
applyLensSchema (AddProperty _) _ = Nothing
applyLensSchema (RemoveProperty key) (SObject smap) =
    case get smap key of
        Just _ => Just (SObject (delete smap key))
        Nothing => Nothing
applyLensSchema (RemoveProperty _) _ = Nothing
applyLensSchema (RenameProperty x y) (SObject smap) =
    case (get smap x, get smap y) of
        (Just p, Nothing) =>
            let
                smap = (delete smap x)
                smap = (insert smap y p)
            in Just (SObject smap)
        _ => Nothing
applyLensSchema (RenameProperty _ _) _ = Nothing
applyLensSchema (HoistProperty host target) (SObject smap) =
    case get smap host of
        Just (required, SObject host_smap) =>
            (case get host_smap target of
                Just p =>
                    let
                        host_smap = delete host_smap target
                        smap = insert smap host (required, SObject host_smap)
                        smap = insert smap target p
                     in Just (SObject smap)
                Nothing => Nothing)
        _ => Nothing
applyLensSchema (HoistProperty _ _) _ = Nothing
applyLensSchema (PlungeProperty host target) (SObject smap) =
    case (get smap target, get smap host) of
        (Just (required, schema), Nothing) =>
            let
                host_smap = insert Empty target (required, schema)
                smap = delete smap target
                smap = insert smap host (required, SObject host_smap)
            in Just (SObject smap)
        _ => Nothing
applyLensSchema (PlungeProperty _ _) _ = Nothing
applyLensSchema WrapProperty schema = Just (SArray False schema)
applyLensSchema HeadProperty (SArray False schema) = Just schema
applyLensSchema HeadProperty _ = Nothing
applyLensSchema (AllowEmpty b v) s = ?hole3
applyLensSchema (LensIn key lens) (SObject smap) =
    case get smap key of
        Just (_, schema) => applyLensSchema lens schema
        Nothing => Nothing
applyLensSchema (LensIn _ _) _ = Nothing
applyLensSchema (LensMap lens) (SArray allowEmpty schema) =
    map (SArray allowEmpty) (applyLensSchema lens schema)
applyLensSchema (LensMap _) _ = Nothing
applyLensSchema (Require key r) (SObject smap) =
    case get smap key of
        Just (required, schema) =>
            if r == not required
            then Just (SObject (insert smap key (r, schema)))
            else Nothing
        Nothing => Nothing
applyLensSchema (Require _ _) _ = Nothing
applyLensSchema (Default (Boolean x) (Boolean y)) (SBoolean x2) =
    if x == x2 then Just (SBoolean y) else Nothing
applyLensSchema (Default (Number x) (Number y)) (SNumber x2) =
    if x == x2 then Just (SNumber y) else Nothing
applyLensSchema (Default (Text x) (Text y)) (SText x2) =
    if x == x2 then Just (SText y) else Nothing
applyLensSchema (Default _ _) _ = Nothing
-- TODO convert default values
applyLensSchema (Convert a b map) s with (convertIsValid a b map)
    applyLensSchema (Convert KBoolean KBoolean _) (SBoolean _) | True = Just (SBoolean False)
    applyLensSchema (Convert KBoolean KNumber _) (SBoolean _) | True = Just (SNumber 0)
    applyLensSchema (Convert KBoolean KText _) (SBoolean _) | True = Just (SText "")
    applyLensSchema (Convert KNumber KBoolean _) (SNumber _) | True = Just (SBoolean False)
    applyLensSchema (Convert KNumber KNumber _) (SNumber _) | True = Just (SNumber 0)
    applyLensSchema (Convert KNumber KText _) (SNumber _) | True = Just (SText "")
    applyLensSchema (Convert KText KBoolean _) (SText _) | True = Just (SBoolean False)
    applyLensSchema (Convert KText KNumber _) (SText _) | True = Just (SNumber 0)
    applyLensSchema (Convert KText KText _) (SText _) | True = Just (SText "")
    applyLensSchema (Convert _ _ _) _ | _ = Nothing

lensToSchema : List Lens -> Maybe Schema
lensToSchema [] = Just SFalse
lensToSchema (l::ls) =
    case lensToSchema ls of
        Just s => applyLensSchema l s
        Nothing => Nothing
