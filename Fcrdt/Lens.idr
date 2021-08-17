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

data Schema =
      SFalse
    | SBoolean
    | SNumber
    | SText
    | SArray Bool Schema
    | SObject (Map (Bool, Schema))

schemaOf : Value -> Schema
schemaOf (Primitive (Boolean x)) = SBoolean
schemaOf (Primitive (Number x)) = SNumber
schemaOf (Primitive (Text x)) = SText
schemaOf (Array x) = SArray True SFalse
schemaOf (Object x) = SObject Empty

validate : Schema -> Value -> Bool
validate SFalse _ = False
validate SBoolean (Primitive (Boolean _)) = True
validate SBoolean _ = False
validate SNumber (Primitive (Number _)) = True
validate SNumber _ = False
validate SText (Primitive (Text _)) = True
validate SText _ = False
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
    | AddProperty Nat
    | RemoveProperty Nat
    | RenameProperty Nat Nat
    | HoistProperty Nat Nat
    | PlungeProperty Nat Nat
    | WrapProperty
    | HeadProperty
    | AllowEmpty Bool Value
    | LensIn Nat Lens
    | LensMap Lens
    | Require Bool
    | Default Value Value
    | Convert PrimitiveKind PrimitiveKind (List (PrimitiveValue, PrimitiveValue))

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
    Require b1 == Require b2 = b1 == b2
    Convert k11 k21 f1 == Convert k12 k22 f2 = k11 == k12 && k22 == k22 && f1 == f2
    _ == _ = False
