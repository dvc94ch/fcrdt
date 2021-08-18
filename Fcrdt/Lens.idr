module Fcrdt.Lens

import Data.List
import Data.Maybe
import Fcrdt.Map

%default total

data PrimitiveValue =
      Boolean Bool
    | Number Nat
    | Text (List Char)

%name PrimitiveValue val, v, v1, v2

Eq PrimitiveValue where
    Boolean b1 == Boolean b2 = b1 == b2
    Number n1 == Number n2 = n1 == n2
    Text t1 == Text t2 = t1 == t2
    _ == _ = False

data PrimitiveKind =
      KBoolean
    | KNumber
    | KText

%name PrimitiveKind k, k1, k2

Eq PrimitiveKind where
    KBoolean == KBoolean = True
    KNumber == KNumber = True
    KText == KText = True
    _ == _ = False

data Value =
      Primitive PrimitiveValue
    | Array (List Value)
    | Object (Map Value)

%name Value val, v, v1, v2

Eq Value where
    Primitive v1 == Primitive v2 = v1 == v2
    Array vs1 == Array vs2 = assert_total (vs1 == vs2)
    Object ps1 == Object ps2 = assert_total (ps1 == ps2)
    _ == _ = False

data Kind =
      KPrimitive PrimitiveKind
    | KArray
    | KObject

%name Kind k, k1, k2

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
    | SNumber Nat
    | SText (List Char)
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
    | LensIn Key Lens
    | LensMap Lens
    | Require Key Bool
    | Default PrimitiveValue PrimitiveValue
    | Convert PrimitiveKind PrimitiveKind (List (PrimitiveValue, PrimitiveValue))

%name Lens lens, l, l1, l2

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
reverseLens (LensIn x y) = LensIn x (reverseLens y)
reverseLens (LensMap x) = LensMap (reverseLens x)
reverseLens (Require k b) = Require k (not b)
reverseLens (Default v1 v2) = Default v2 v1
reverseLens (Convert a b m) = Convert b a (map (\(a, b) => (b, a)) m)

applyLensSchema : Lens -> Schema -> Maybe Schema
applyLensSchema (Make (KPrimitive KBoolean)) SFalse = Just (SBoolean False)
applyLensSchema (Make (KPrimitive KNumber)) SFalse = Just (SNumber 0)
applyLensSchema (Make (KPrimitive KText)) SFalse = Just (SText [])
applyLensSchema (Make KArray) SFalse = Just (SArray True SFalse)
applyLensSchema (Make KObject) SFalse = Just (SObject Empty)
applyLensSchema (Make _) _ = Nothing
applyLensSchema (Destroy (KPrimitive KBoolean)) (SBoolean False) = Just SFalse
applyLensSchema (Destroy (KPrimitive KNumber)) (SNumber 0) = Just SFalse
applyLensSchema (Destroy (KPrimitive KText)) (SText []) = Just SFalse
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
        Just (False, SFalse) => Just (SObject (delete smap key))
        _ => Nothing
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
    applyLensSchema (Convert KBoolean KText _) (SBoolean _) | True = Just (SText [])
    applyLensSchema (Convert KNumber KBoolean _) (SNumber _) | True = Just (SBoolean False)
    applyLensSchema (Convert KNumber KNumber _) (SNumber _) | True = Just (SNumber 0)
    applyLensSchema (Convert KNumber KText _) (SNumber _) | True = Just (SText [])
    applyLensSchema (Convert KText KBoolean _) (SText _) | True = Just (SBoolean False)
    applyLensSchema (Convert KText KNumber _) (SText _) | True = Just (SNumber 0)
    applyLensSchema (Convert KText KText _) (SText _) | True = Just (SText [])
    applyLensSchema (Convert _ _ _) _ | _ = Nothing

lensToSchema : List Lens -> Maybe Schema
lensToSchema [] = Just SFalse
lensToSchema (l::ls) =
    case lensToSchema ls of
        Just s => applyLensSchema l s
        Nothing => Nothing

applyTwoLenses : Lens -> Lens -> Schema -> Maybe Schema
applyTwoLenses a b s =
    case applyLensSchema a s of
        Just s => applyLensSchema b s
        Nothing => Nothing


reverseSchema : Lens -> Schema -> Maybe Schema
reverseSchema l s = applyTwoLenses l (reverseLens l) s

||| Forwards and backwards compatibility requires schema transformations to be reversible
assertReverseSchema :
    (lens: Lens) ->
    (schema: Schema) ->
    (IsJust (applyLensSchema lens schema)) ->
    (reverseSchema lens schema = Just schema)
assertReverseSchema (Make (KPrimitive KBoolean)) SFalse _ = Refl
assertReverseSchema (Make (KPrimitive KBoolean)) (SBoolean _) ItIsJust impossible
assertReverseSchema (Make (KPrimitive KBoolean)) (SNumber _) ItIsJust impossible
assertReverseSchema (Make (KPrimitive KBoolean)) (SText _) ItIsJust impossible
assertReverseSchema (Make (KPrimitive KBoolean)) (SArray _ _) ItIsJust impossible
assertReverseSchema (Make (KPrimitive KBoolean)) (SObject _) ItIsJust impossible
assertReverseSchema (Make (KPrimitive KNumber)) SFalse _ = Refl
assertReverseSchema (Make (KPrimitive KNumber)) (SBoolean _) ItIsJust impossible
assertReverseSchema (Make (KPrimitive KNumber)) (SNumber _) ItIsJust impossible
assertReverseSchema (Make (KPrimitive KNumber)) (SText _) ItIsJust impossible
assertReverseSchema (Make (KPrimitive KNumber)) (SArray _ _) ItIsJust impossible
assertReverseSchema (Make (KPrimitive KNumber)) (SObject _) ItIsJust impossible
assertReverseSchema (Make (KPrimitive KText)) SFalse _ = Refl
assertReverseSchema (Make (KPrimitive KText)) (SBoolean _) ItIsJust impossible
assertReverseSchema (Make (KPrimitive KText)) (SNumber _) ItIsJust impossible
assertReverseSchema (Make (KPrimitive KText)) (SText _) ItIsJust impossible
assertReverseSchema (Make (KPrimitive KText)) (SArray _ _) ItIsJust impossible
assertReverseSchema (Make (KPrimitive KText)) (SObject _) ItIsJust impossible
assertReverseSchema (Make KArray) SFalse _ = Refl
assertReverseSchema (Make KArray) (SBoolean _) ItIsJust impossible
assertReverseSchema (Make KArray) (SNumber _) ItIsJust impossible
assertReverseSchema (Make KArray) (SText _) ItIsJust impossible
assertReverseSchema (Make KArray) (SArray _ _) ItIsJust impossible
assertReverseSchema (Make KArray) (SObject _) ItIsJust impossible
assertReverseSchema (Make KObject) SFalse _ = Refl
assertReverseSchema (Make KObject) (SBoolean _) ItIsJust impossible
assertReverseSchema (Make KObject) (SNumber _) ItIsJust impossible
assertReverseSchema (Make KObject) (SText _) ItIsJust impossible
assertReverseSchema (Make KObject) (SArray _ _) ItIsJust impossible
assertReverseSchema (Make KObject) (SObject _) ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KBoolean)) SFalse ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KBoolean)) (SBoolean False) _ = Refl
assertReverseSchema (Destroy (KPrimitive KBoolean)) (SBoolean True) ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KBoolean)) (SNumber _) ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KBoolean)) (SText _) ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KBoolean)) (SArray _ _) ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KBoolean)) (SObject _) ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KNumber)) SFalse ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KNumber)) (SBoolean _) ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KNumber)) (SNumber 0) _ = Refl
assertReverseSchema (Destroy (KPrimitive KNumber)) (SNumber (S _)) ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KNumber)) (SText _) ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KNumber)) (SArray _ _) ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KNumber)) (SObject _) ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KText)) SFalse ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KText)) (SBoolean _) ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KText)) (SNumber _) ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KText)) (SText []) _ = Refl
assertReverseSchema (Destroy (KPrimitive KText)) (SText (_ :: _)) ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KText)) (SArray _ _) ItIsJust impossible
assertReverseSchema (Destroy (KPrimitive KText)) (SObject _) ItIsJust impossible
assertReverseSchema (Destroy KArray) SFalse ItIsJust impossible
assertReverseSchema (Destroy KArray) (SBoolean _) ItIsJust impossible
assertReverseSchema (Destroy KArray) (SNumber _) ItIsJust impossible
assertReverseSchema (Destroy KArray) (SText _) ItIsJust impossible
assertReverseSchema (Destroy KArray) (SArray False _) ItIsJust impossible
assertReverseSchema (Destroy KArray) (SArray True SFalse) _ = Refl
assertReverseSchema (Destroy KArray) (SArray True (SBoolean _)) ItIsJust impossible
assertReverseSchema (Destroy KArray) (SArray True (SNumber _)) ItIsJust impossible
assertReverseSchema (Destroy KArray) (SArray True (SText _)) ItIsJust impossible
assertReverseSchema (Destroy KArray) (SArray True (SArray _ _)) ItIsJust impossible
assertReverseSchema (Destroy KArray) (SArray True (SObject _)) ItIsJust impossible
assertReverseSchema (Destroy KArray) (SObject _) ItIsJust impossible
assertReverseSchema (Destroy KObject) SFalse ItIsJust impossible
assertReverseSchema (Destroy KObject) (SBoolean _) ItIsJust impossible
assertReverseSchema (Destroy KObject) (SNumber _) ItIsJust impossible
assertReverseSchema (Destroy KObject) (SText _) ItIsJust impossible
assertReverseSchema (Destroy KObject) (SArray _ _) ItIsJust impossible
assertReverseSchema (Destroy KObject) (SObject Empty) _ = Refl
assertReverseSchema (Destroy KObject) (SObject (Entry _ _ _)) ItIsJust impossible
assertReverseSchema (AddProperty _) SFalse ItIsJust impossible
assertReverseSchema (AddProperty _) (SBoolean _) ItIsJust impossible
assertReverseSchema (AddProperty _) (SNumber _) ItIsJust impossible
assertReverseSchema (AddProperty _) (SText _) ItIsJust impossible
assertReverseSchema (AddProperty _) (SArray _ _) ItIsJust impossible
assertReverseSchema (AddProperty key) (SObject map) x with (get map key)
    assertReverseSchema (AddProperty key) (SObject map) x | Nothing =
        rewrite lemmaGetInsert map key (False, SFalse) in
            let ldi = lemmaDeleteInsert map key (False, SFalse) in ?missing
    assertReverseSchema (AddProperty key) (SObject map) x | (Just y) = absurd $ x
assertReverseSchema (RemoveProperty _) SFalse ItIsJust impossible
assertReverseSchema (RemoveProperty _) (SBoolean _) ItIsJust impossible
assertReverseSchema (RemoveProperty _) (SNumber _) ItIsJust impossible
assertReverseSchema (RemoveProperty _) (SText _) ItIsJust impossible
assertReverseSchema (RemoveProperty _) (SArray _ _) ItIsJust impossible
assertReverseSchema (RemoveProperty key) (SObject map) x with (get map key)
    assertReverseSchema (RemoveProperty key) (SObject map) x | Nothing = absurd $ x
    assertReverseSchema (RemoveProperty key) (SObject map) x | (Just (False, SFalse)) =
        rewrite lemmaGetDelete map key in
            rewrite lemmaInsertDelete map key (False, SFalse) in ?hole_2
    assertReverseSchema (RemoveProperty key) (SObject map) x | (Just (False, (SBoolean _))) = absurd $ x
    assertReverseSchema (RemoveProperty key) (SObject map) x | (Just (False, (SNumber _))) = absurd $ x
    assertReverseSchema (RemoveProperty key) (SObject map) x | (Just (False, (SText _))) = absurd $ x
    assertReverseSchema (RemoveProperty key) (SObject map) x | (Just (False, (SArray _ _))) = absurd $ x
    assertReverseSchema (RemoveProperty key) (SObject map) x | (Just (False, (SObject _))) = absurd $ x
    assertReverseSchema (RemoveProperty key) (SObject map) x | (Just (True, _)) = absurd $ x
assertReverseSchema (RenameProperty _ _) SFalse ItIsJust impossible
assertReverseSchema (RenameProperty _ _) (SBoolean _) ItIsJust impossible
assertReverseSchema (RenameProperty _ _) (SNumber _) ItIsJust impossible
assertReverseSchema (RenameProperty _ _) (SText _) ItIsJust impossible
assertReverseSchema (RenameProperty _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (RenameProperty a b) (SObject map) x = ?assertReverseSchema_rhs_23
assertReverseSchema (HoistProperty _ _) SFalse ItIsJust impossible
assertReverseSchema (HoistProperty _ _) (SBoolean _) ItIsJust impossible
assertReverseSchema (HoistProperty _ _) (SNumber _) ItIsJust impossible
assertReverseSchema (HoistProperty _ _) (SText _) ItIsJust impossible
assertReverseSchema (HoistProperty _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (HoistProperty key k) (SObject map) x = ?assertReverseSchema_rhs_24
assertReverseSchema (PlungeProperty _ _) SFalse ItIsJust impossible
assertReverseSchema (PlungeProperty _ _) (SBoolean _) ItIsJust impossible
assertReverseSchema (PlungeProperty _ _) (SNumber _) ItIsJust impossible
assertReverseSchema (PlungeProperty _ _) (SText _) ItIsJust impossible
assertReverseSchema (PlungeProperty _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (PlungeProperty key k) (SObject map) x = ?assertReverseSchema_rhs_25
assertReverseSchema WrapProperty SFalse _ = Refl
assertReverseSchema WrapProperty (SBoolean _) _ = Refl
assertReverseSchema WrapProperty (SNumber _) _ = Refl
assertReverseSchema WrapProperty (SText _) _ = Refl
assertReverseSchema WrapProperty (SArray _ _) _ = Refl
assertReverseSchema WrapProperty (SObject _) _ = Refl
assertReverseSchema HeadProperty SFalse ItIsJust impossible
assertReverseSchema HeadProperty (SBoolean _) ItIsJust impossible
assertReverseSchema HeadProperty (SNumber _) ItIsJust impossible
assertReverseSchema HeadProperty (SText _) ItIsJust impossible
assertReverseSchema HeadProperty (SArray False _) _ = Refl
assertReverseSchema HeadProperty (SArray True _) ItIsJust impossible
assertReverseSchema HeadProperty (SObject _) ItIsJust impossible
assertReverseSchema (LensIn key lens) schema x = ?assertReverseSchema_rhs_11
assertReverseSchema (LensMap lens) schema x = ?assertReverseSchema_rhs_12
assertReverseSchema (Require key val) schema x = ?assertReverseSchema_rhs_13
assertReverseSchema (Default v1 v2) schema x = ?assertReverseSchema_rhs_14
assertReverseSchema (Convert k1 k2 xs) schema x = ?assertReverseSchema_rhs_15
