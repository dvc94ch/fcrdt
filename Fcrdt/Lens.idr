module Fcrdt.Lens

import Data.List
import Data.Maybe

-- %default total

||| TODO
||| Implement convert transform
||| Support combining schemas (and/or)

||| Modeling keys as nats as idris seems to be able to
||| reason better about equality
data Value =
      Boolean Bool
    | Number Int
    | Text String
    | Array (List Value)
    | Object (List (Nat, Value))

Eq Value where
    Boolean b1 == Boolean b2 = b1 == b2
    Number n1 == Number n2 = n1 == n2
    Text t1 == Text t2 = t1 == t2
    Array vs1 == Array vs2 = assert_total (vs1 == vs2)
    Object ps1 == Object ps2 = assert_total (ps1 == ps2)
    _ == _ = False

get : Eq a => a -> List (a, b) -> Maybe b
get _ [] = Nothing
get key ((k, v) :: xs) = if key == k then Just v else get key xs

insert : Eq a => a -> b -> List (a, b) -> List (a, b)
insert key value [] = [(key, value)]
insert key value ((k, v) :: xs) =
    if key == k
    then (key, value) :: xs
    else (k, v) :: (insert key value xs)

delete : Eq a => a -> List (a, b) -> List (a, b)
delete key [] = []
delete key ((k, v) :: xs) = if key == k then xs else (k, v) :: xs

lemmaNatEquality : (n: Nat) -> n == n = True
lemmaNatEquality 0 = Refl
lemmaNatEquality (S k) = rewrite lemmaNatEquality k in Refl

lemmaDeleteAfterInsert :
    (key: Nat) ->
    (value: b) ->
    (map: List (Nat, b)) ->
    (get key map = Nothing) ->
    (delete key (insert key value map)) = map
lemmaDeleteAfterInsert key value [] prf = rewrite lemmaNatEquality key in Refl
lemmaDeleteAfterInsert key value ((k, v) :: xs) prf =
    -- rewrite lemmaDeleteAfterInsert in
    ?lemmaDeleteAfterInsert2 --value k v xs key prf

data Kind =
      BooleanKind
    | NumberKind
    | TextKind
    | ArrayKind
    | ObjectKind

Eq Kind where
    BooleanKind == BooleanKind = True
    NumberKind == NumberKind = True
    TextKind == TextKind = True
    ArrayKind == ArrayKind = True
    ObjectKind == ObjectKind = True
    _ == _ = False

kindOf : Value -> Kind
kindOf (Boolean _) = BooleanKind
kindOf (Number _) = NumberKind
kindOf (Text _) = TextKind
kindOf (Array _) = ArrayKind
kindOf (Object _) = ObjectKind

data Schema =
      SFalse
    | SBoolean
    | SNumber
    | SText
    | SArray Bool Schema
    | SObject (List (Nat, (Bool, Schema)))

schemaOf : Value -> Schema
schemaOf (Boolean x) = SBoolean
schemaOf (Number x) = SNumber
schemaOf (Text x) = SText
schemaOf (Array x) = SArray True SFalse
schemaOf (Object x) = SObject empty

validate : Schema -> Value -> Bool
validate SFalse _ = False
validate SBoolean (Boolean _) = True
validate SBoolean _ = False
validate SNumber (Number _) = True
validate SNumber _ = False
validate SText (Text _) = True
validate SText _ = False
validate (SArray allowEmpty schema) (Array []) = allowEmpty
validate (SArray _ schema) (Array (x :: xs)) = validate schema x && validate (SArray True schema) (Array xs)
validate (SArray _ _) _ = False
validate (SObject ss) (Object ps) = validateProperties ps ss && validateRequired ss ps where
    validateProperties : List (Nat, Value) -> List (Nat, (Bool, Schema)) -> Bool
    validateProperties [] _ = True
    validateProperties ((key, value) :: xs) ss with (get key ss)
        validateProperties ((_, value) :: xs) _ | Just (_, schema) =
            assert_total (validate schema value) && validateProperties xs ss
        validateProperties ((_, _) :: _) _ | Nothing = False
    validateRequired : List (Nat, (Bool, Schema)) -> List (Nat, Value) -> Bool
    validateRequired [] _ = True
    validateRequired ((_, (False, _)) :: xs) ps = validateRequired xs ps
    validateRequired ((key, (True, _)) :: xs) ps with (get key ps)
        validateRequired ((key, (True, _)) :: xs) ps | Just _ = validateRequired xs ps
        validateRequired ((key, (True, _)) :: xs) ps | Nothing = False
validate (SObject _) _ = False

data Lens =
      AddProperty Nat Bool Value
    | RemoveProperty Nat Bool Value
    | RenameProperty Nat Nat
    | HoistProperty Nat Nat
    | PlungeProperty Nat Nat
    | WrapProperty
    | HeadProperty
    | LensIn Nat Lens
    | LensMap Lens

Eq Lens where
    AddProperty p1 r1 v1 == AddProperty p2 r2 v2 = p1 == p2 && r1 == r2 && v1 == v2
    RemoveProperty p1 r1 v1 == RemoveProperty p2 r2 v2 = p1 == p2 && r1 == r2 && v1 == v2
    RenameProperty a1 b1 == RenameProperty a2 b2 = a1 == a2 && b1 == b2
    HoistProperty h1 p1 == HoistProperty h2 p2 = h1 == h2 && p1 == p2
    PlungeProperty h1 p1 == PlungeProperty h2 p2 = h1 == h2 && p1 == p2
    WrapProperty == WrapProperty = True
    HeadProperty == HeadProperty = True
    LensIn p1 l1 == LensIn p2 l2 = p1 == p2 && l1 == l2
    LensMap l1 == LensMap l2 = l1 == l2
    _ == _ = False

applyLensSchema : Lens -> Schema -> Maybe Schema
applyLensSchema (AddProperty key required value) SFalse =
    Just (SObject (insert key (required, schemaOf value) empty))
applyLensSchema (AddProperty key required value) (SObject ps) =
    case get key ps of
        Just p => Nothing
        Nothing => Just (SObject (insert key (required, schemaOf value) ps))
applyLensSchema (AddProperty _ _ _) _ = Nothing
applyLensSchema (RemoveProperty key _ _) (SObject ps) =
    case get key ps of
        Just p => Just (SObject (delete key ps))
        Nothing => Nothing
applyLensSchema (RemoveProperty _ _ _) _ = Nothing
applyLensSchema (RenameProperty x y) (SObject ps) =
    case (get x ps, get y ps) of
        (Just p, Nothing) => Just (SObject (insert y p (delete x ps)))
        _ => Nothing
applyLensSchema (RenameProperty _ _) _ = Nothing
applyLensSchema (HoistProperty h p) (SObject ps) =
    case get h ps of
        Just (required, SObject hps) =>
            (case get p hps of
                Just v =>
                    let
                        hps = delete p hps
                        ps = delete h ps
                     in
                        Just (SObject (insert p v (insert h (required, SObject hps) ps)))
                Nothing => Nothing)
        _ => Nothing
applyLensSchema (HoistProperty _ _) _ = Nothing
applyLensSchema (PlungeProperty h n) (SObject ps) =
    case (get n ps, get h ps) of
        (Just (required, schema), Nothing) =>
            let
                hps = insert n (required, schema) empty
            in
                Just (SObject (insert h (required, (SObject hps)) (delete n ps)))
        _ => Nothing
applyLensSchema (PlungeProperty _ _) _ = Nothing
applyLensSchema WrapProperty schema = Just (SArray False schema)
applyLensSchema HeadProperty (SArray False schema) = Just schema
applyLensSchema HeadProperty _ = Nothing
applyLensSchema (LensIn key lens) (SObject ps) =
    case get key ps of
        Just (_, schema) => applyLensSchema lens schema
        Nothing => Nothing
applyLensSchema (LensIn _ _) _ = Nothing
-- applyLensSchema (LensMap lens) SFalse =
--    applyLensSchema (LensMap lens) (SArray True SFalse)
applyLensSchema (LensMap lens) (SArray allowEmpty schema) =
    map (SArray allowEmpty) (applyLensSchema lens schema)
applyLensSchema (LensMap _) _ = Nothing

lensToSchema : List Lens -> Maybe Schema
lensToSchema [] = Just SFalse
lensToSchema (l::ls) =
    case lensToSchema ls of
        Just s => applyLensSchema l s
        Nothing => Nothing

applyLensValue : Lens -> Value -> Maybe Value
applyLensValue (AddProperty n required d) (Object ps) =
    if isNothing (get n ps)
    then Just (Object (if required then insert n d ps else ps))
    else Nothing
applyLensValue (AddProperty _ _ _) _ = Nothing
applyLensValue (RemoveProperty n required d) (Object ps) =
    if isJust (get n ps)
    then Just (Object (delete n ps))
    else if required then Nothing else Just (Object ps)
applyLensValue (RemoveProperty _ _ _) _ = Nothing
applyLensValue (RenameProperty x y) (Object ps) =
    case (get x ps, get y ps) of
        (Just v, Nothing) => Just (Object (insert y v (delete x ps)))
        (x, y) => Nothing
applyLensValue (RenameProperty _ _) _ = Nothing
applyLensValue (HoistProperty hp p) (Object ps) =
    case get hp ps of
        Just (Object hps) =>
            (case (get p hps, get p ps) of
                ((Just v), Nothing) =>
                    (let
                        hps = (delete p hps)
                        ps = (delete hp ps)
                    in
                        Just (Object (insert p v (insert hp (Object hps) ps))))
                _ => Nothing)
        _ => Nothing
applyLensValue (HoistProperty _ _) _ = Nothing
applyLensValue (PlungeProperty hp p) (Object ps) =
    case (get p ps, get hp ps) of
        (Just v, Nothing) =>
            (let
                ps = (delete p ps)
            in
                Just (Object (insert hp (Object (insert hp v empty)) ps)))
        _ => Nothing
applyLensValue (PlungeProperty _ _) _ = Nothing
applyLensValue WrapProperty v = Just (Array [v])
applyLensValue HeadProperty (Array (x :: xs)) = Just x
applyLensValue HeadProperty _ = Nothing
applyLensValue (LensIn x l) (Object ps) =
    case get x ps of
        Just v => case applyLensValue l v of
            Just v => Just (Object (insert x v ps))
            Nothing => Nothing
        Nothing => Nothing
applyLensValue (LensIn x y) value = Nothing
applyLensValue (LensMap x) (Array vs) = foldl
    (\acc, v => case acc of
        Just (Array vs) => case (applyLensValue x v) of
            Just v => Just (Array (v :: vs))
            Nothing => Nothing
        n => Nothing)
    (Just (Array Nil))
    vs
applyLensValue (LensMap x) value = Nothing

reverseLens : Lens -> Lens
reverseLens (AddProperty x y z) = RemoveProperty x y z
reverseLens (RemoveProperty x y z) = AddProperty x y z
reverseLens (RenameProperty x y) = RenameProperty y x
reverseLens (HoistProperty x y) = PlungeProperty x y
reverseLens (PlungeProperty x y) = HoistProperty x y
reverseLens WrapProperty = HeadProperty
reverseLens HeadProperty = WrapProperty
reverseLens (LensIn x y) = LensIn x (reverseLens y)
reverseLens (LensMap x) = LensMap (reverseLens x)

applyTwoLenses : Lens -> Lens -> Schema -> Maybe Schema
applyTwoLenses a b s =
    case applyLensSchema a s of
        Just s => applyLensSchema b s
        Nothing => Nothing

applyABimpliesApplyA : isJust (applyTwoLenses a b s) = True -> isJust (applyLensSchema a s) = True

reverseSchema : Lens -> Schema -> Maybe Schema
reverseSchema l s = applyTwoLenses l (reverseLens l) s

fnExample : (x : Maybe a) -> Maybe a
fnExample x =
    case x of
        Just x => Just x
        Nothing => Nothing

assertFnExample : (x : Maybe a) -> (isJust x = True) -> (isJust (fnExample x) = True)
assertFnExample Nothing Refl impossible
assertFnExample (Just x) prf = prf

assertFnExample2 : (x : Maybe a) -> (isJust (fnExample x) = True) -> (isJust x = True)
assertFnExample2 Nothing Refl impossible
assertFnExample2 (Just x) prf = prf

lemmaMaybeMap : (x : Maybe a) -> (f : a -> b) -> (isJust (map f x) = True) -> isJust x = True
lemmaMaybeMap Nothing _ Refl impossible
lemmaMaybeMap (Just x) _ _ = Refl

lemmaMaybeMap2 : (x : Maybe a) -> (f : a -> b) -> IsJust (map f x) -> IsJust x
lemmaMaybeMap2 Nothing _ ItIsJust impossible
lemmaMaybeMap2 (Just x) f y = ItIsJust

||| Forwards and backwards compatibility requires schema transformations to be reversible
assertReverseSchema :
    (lens: Lens) ->
    (schema: Schema) ->
    (IsJust (applyLensSchema lens schema)) ->
    (reverseSchema lens schema = Just schema)
assertReverseSchema (AddProperty n False v) SFalse _ = ?assertReverseSchema_rhs_25
assertReverseSchema (AddProperty n True v) SFalse _ = ?assertReverseSchema_rhs_26
assertReverseSchema (AddProperty _ _ _) SBoolean ItIsJust impossible
assertReverseSchema (AddProperty _ _ _) SNumber ItIsJust impossible
assertReverseSchema (AddProperty _ _ _) SText ItIsJust impossible
assertReverseSchema (AddProperty _ _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (AddProperty x y z) (SObject w) prf = ?assertReverseSchema_rhs_15
assertReverseSchema (RemoveProperty _ _ _) SFalse ItIsJust impossible
assertReverseSchema (RemoveProperty _ _ _) SBoolean ItIsJust impossible
assertReverseSchema (RemoveProperty _ _ _) SNumber ItIsJust impossible
assertReverseSchema (RemoveProperty _ _ _) SText ItIsJust impossible
assertReverseSchema (RemoveProperty _ _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (RemoveProperty x y z) (SObject w) prf = ?assertReverseSchema_rhs_17
assertReverseSchema (RenameProperty _ _) SFalse ItIsJust impossible
assertReverseSchema (RenameProperty _ _) SBoolean ItIsJust impossible
assertReverseSchema (RenameProperty _ _) SNumber ItIsJust impossible
assertReverseSchema (RenameProperty _ _) SText ItIsJust impossible
assertReverseSchema (RenameProperty _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (RenameProperty x y) (SObject z) prf = ?assertReverseSchema_rhs_18
assertReverseSchema (HoistProperty _ _) SFalse ItIsJust impossible
assertReverseSchema (HoistProperty _ _) SBoolean ItIsJust impossible
assertReverseSchema (HoistProperty _ _) SNumber ItIsJust impossible
assertReverseSchema (HoistProperty _ _) SText ItIsJust impossible
assertReverseSchema (HoistProperty _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (HoistProperty x y) (SObject z) prf = ?assertReverseSchema_rhs_19
assertReverseSchema (PlungeProperty _ _) SFalse ItIsJust impossible
assertReverseSchema (PlungeProperty _ _) SBoolean ItIsJust impossible
assertReverseSchema (PlungeProperty _ _) SNumber ItIsJust impossible
assertReverseSchema (PlungeProperty _ _) SText ItIsJust impossible
assertReverseSchema (PlungeProperty _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (PlungeProperty x y) (SObject z) prf = ?assertReverseSchema_rhs_20
assertReverseSchema WrapProperty _ _ = Refl
assertReverseSchema HeadProperty SFalse ItIsJust impossible
assertReverseSchema HeadProperty SBoolean ItIsJust impossible
assertReverseSchema HeadProperty SNumber ItIsJust impossible
assertReverseSchema HeadProperty SText ItIsJust impossible
assertReverseSchema HeadProperty (SArray False _) prf = Refl
assertReverseSchema HeadProperty (SArray True _) ItIsJust impossible
assertReverseSchema HeadProperty (SObject _) ItIsJust impossible
assertReverseSchema (LensIn _ _) SFalse ItIsJust impossible
assertReverseSchema (LensIn _ _) SBoolean ItIsJust impossible
assertReverseSchema (LensIn _ _) SNumber ItIsJust impossible
assertReverseSchema (LensIn _ _) SText ItIsJust impossible
assertReverseSchema (LensIn _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (LensIn x y) (SObject z) prf = ?assertReverseSchema_rhs_23
assertReverseSchema (LensMap _) SFalse ItIsJust impossible
assertReverseSchema (LensMap _) SBoolean ItIsJust impossible
assertReverseSchema (LensMap _) SNumber ItIsJust impossible
assertReverseSchema (LensMap _) SText ItIsJust impossible
assertReverseSchema (LensMap lens) (SArray allowEmpty schema) prf =
    let
        mm = lemmaMaybeMap2 (applyLensSchema lens schema) (SArray allowEmpty) prf
        ind = assertReverseSchema lens schema mm
    in ?assertReverseLensMap
assertReverseSchema (LensMap _) (SObject _) ItIsJust impossible

||| If transforming the schema succeeds, transforming the value must succeed
schemaJustImpliesValueJust :
    (lens: Lens) ->
    (schema: Schema) ->
    (value: Value) ->
    (validate schema value = True) ->
    (IsJust (applyLensSchema lens schema)) ->
    (IsJust (applyLensValue lens value))

schemaJustImpliesValueJust (AddProperty _ _ _) SFalse _ _ ItIsJust impossible
schemaJustImpliesValueJust (AddProperty _ _ _) SBoolean _ _ ItIsJust impossible
schemaJustImpliesValueJust (AddProperty _ _ _) SNumber _ _ ItIsJust impossible
schemaJustImpliesValueJust (AddProperty _ _ _) SText _ _ ItIsJust impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SArray _ _) _ _ ItIsJust impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject []) (Object []) _ _ = ItIsJust
schemaJustImpliesValueJust (AddProperty n r v) (SObject []) (Object (x :: xs)) prf ItIsJust = ?schemaJustImpliesValueJust_rhs_40
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject (x :: xs)) (Object []) _ _ = ItIsJust
schemaJustImpliesValueJust (AddProperty n r v) (SObject (x :: xs)) (Object (y :: ys)) prf prf1 = ?schemaJustImpliesValueJust_rhs_39
schemaJustImpliesValueJust (RemoveProperty _ _ _) SFalse _ _ ItIsJust impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) SBoolean _ _ ItIsJust impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) SNumber _ _ ItIsJust impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) SText _ _ ItIsJust impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SArray _ _) _ _ ItIsJust impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (RemoveProperty x y z) (SObject w) (Object v) prf prf1 = ?schemaJustImpliesValueJust_rhs_28
schemaJustImpliesValueJust (RenameProperty _ _) SFalse _ _ ItIsJust impossible
schemaJustImpliesValueJust (RenameProperty _ _) SBoolean _ _ ItIsJust impossible
schemaJustImpliesValueJust (RenameProperty _ _) SNumber _ _ ItIsJust impossible
schemaJustImpliesValueJust (RenameProperty _ _) SText _ _ ItIsJust impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SArray _ _) _ _ ItIsJust impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (RenameProperty x y) (SObject z) (Object w) prf prf1 = ?schemaJustImpliesValueJust_rhs_29
schemaJustImpliesValueJust (HoistProperty _ _) SFalse _ _ ItIsJust impossible
schemaJustImpliesValueJust (HoistProperty _ _) SBoolean _ _ ItIsJust impossible
schemaJustImpliesValueJust (HoistProperty _ _) SNumber _ _ ItIsJust impossible
schemaJustImpliesValueJust (HoistProperty _ _) SText _ _ ItIsJust impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SArray _ _) _ _ ItIsJust impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (HoistProperty x y) (SObject z) (Object w) prf prf1 = ?schemaJustImpliesValueJust_rhs_30
schemaJustImpliesValueJust (PlungeProperty _ _) SFalse _ _ ItIsJust impossible
schemaJustImpliesValueJust (PlungeProperty _ _) SBoolean _ _ ItIsJust impossible
schemaJustImpliesValueJust (PlungeProperty _ _) SNumber _ _ ItIsJust impossible
schemaJustImpliesValueJust (PlungeProperty _ _) SText _ _ ItIsJust impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SArray _ _) _ _ ItIsJust impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (PlungeProperty x y) (SObject z) (Object w) prf prf1 = ?schemaJustImpliesValueJust_rhs_31
schemaJustImpliesValueJust WrapProperty _ _ _ _ = ItIsJust
schemaJustImpliesValueJust HeadProperty SFalse _ _ ItIsJust impossible
schemaJustImpliesValueJust HeadProperty SBoolean _ _ ItIsJust impossible
schemaJustImpliesValueJust HeadProperty SNumber _ _ ItIsJust impossible
schemaJustImpliesValueJust HeadProperty SText _ _ ItIsJust impossible
schemaJustImpliesValueJust HeadProperty (SArray _ _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust HeadProperty (SArray _ _) (Number _) Refl _ impossible
schemaJustImpliesValueJust HeadProperty (SArray _ _) (Text _) Refl _ impossible
schemaJustImpliesValueJust HeadProperty (SArray False _) (Array []) Refl _ impossible
schemaJustImpliesValueJust HeadProperty (SArray False _) (Array (x :: xs)) _ _ = ItIsJust
schemaJustImpliesValueJust HeadProperty (SArray True _) (Array _) _ ItIsJust impossible
schemaJustImpliesValueJust HeadProperty (SArray _ _) (Object _) Refl _ impossible
schemaJustImpliesValueJust HeadProperty (SObject _) _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensIn _ _) SFalse _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensIn _ _) SBoolean _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensIn _ _) SNumber _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensIn _ _) SText _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensIn _ _) (SArray _ _) _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensIn _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (LensIn _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (LensIn _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (LensIn _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (LensIn x y) (SObject z) (Object w) prf prf1 = ?schemaJustImpliesValueJust_rhs_34
schemaJustImpliesValueJust (LensMap _) SFalse (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (LensMap _) SFalse (Number _) Refl _ impossible
schemaJustImpliesValueJust (LensMap _) SFalse (Text _) Refl _ impossible
schemaJustImpliesValueJust (LensMap x) SFalse (Array xs) prf prf1 = ?schemaJustImpliesValueJust_rhs_15
schemaJustImpliesValueJust (LensMap _) SFalse (Object _) Refl _ impossible
schemaJustImpliesValueJust (LensMap _) SBoolean _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensMap _) SNumber _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensMap _) SText _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensMap _) (SArray _ _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (LensMap _) (SArray _ _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (LensMap _) (SArray _ _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (LensMap l) (SArray allowEmpty schema) (Array xs) prf prf1 = ?schemaJustImpliesValueJust_rhs_19
schemaJustImpliesValueJust (LensMap _) (SArray _ _) (Object _) Refl _ impossible
schemaJustImpliesValueJust (LensMap _) (SObject _) _ _ ItIsJust impossible

validateLensed : Lens -> Schema -> Value -> Bool
validateLensed l s v =
    case (applyLensSchema l s, applyLensValue l v) of
        (Just s, Just v) => validate s v
        _ => False

andImpliesA' : (a : Bool) -> (b : Lazy Bool) -> (a && b = True) -> a = True
andImpliesA' False b prf = prf
andImpliesA' True b prf = Refl

andImpliesA : (a && b = True) -> a = True
andImpliesA prf = irrelevantEq $ andImpliesA' a b prf

assertLensLensMap : (IsJust (applyLensSchema (LensMap lens) schema)) -> (IsJust (applyLensSchema lens schema))
assertLensLensMap x = ?assertLensLensMap_rhs

||| Transforming a valid value must result in a valid value
assertLens :
    (lens: Lens) ->
    (schema: Schema) ->
    (value: Value) ->
    (validate schema value = True) ->
    (IsJust (applyLensSchema lens schema)) ->
    (validateLensed lens schema value = True)
assertLens (AddProperty k x y) schema value prf prf1 = ?assertLens_rhs_1
assertLens (RemoveProperty k x y) schema value prf prf1 = ?assertLens_rhs_2
assertLens (RenameProperty k j) schema value prf prf1 = ?assertLens_rhs_3
assertLens (HoistProperty k j) schema value prf prf1 = ?assertLens_rhs_4
assertLens (PlungeProperty k j) schema value prf prf1 = ?assertLens_rhs_5
assertLens WrapProperty SFalse _ Refl _ impossible
assertLens WrapProperty SBoolean _ prf _ = rewrite prf in Refl
assertLens WrapProperty SNumber _ prf _ = rewrite prf in Refl
assertLens WrapProperty SText _ prf _ = rewrite prf in Refl
assertLens WrapProperty (SArray x y) _ prf _ = rewrite prf in Refl
assertLens WrapProperty (SObject xs) _ prf _ = rewrite prf in Refl
assertLens HeadProperty SFalse _ Refl _ impossible
assertLens HeadProperty SBoolean _ _ ItIsJust impossible
assertLens HeadProperty SNumber _ _ ItIsJust impossible
assertLens HeadProperty SText _ _ ItIsJust impossible
assertLens HeadProperty (SArray False _) (Boolean _) Refl _ impossible
assertLens HeadProperty (SArray False _) (Number _) Refl _ impossible
assertLens HeadProperty (SArray False _) (Text _) Refl _ impossible
assertLens HeadProperty (SArray False _) (Array []) Refl _ impossible
assertLens HeadProperty (SArray False s) (Array (x :: xs)) prf _ = andImpliesA prf
assertLens HeadProperty (SArray False _) (Object _) Refl _ impossible
assertLens HeadProperty (SArray True _) _ _ ItIsJust impossible
assertLens HeadProperty (SObject _) _ _ ItIsJust impossible
assertLens (LensIn k x) schema value prf prf1 = ?assertLens_rhs_8
assertLens (LensMap lens) schema value prf isj =
    let
        isj = assertLensLensMap isj
        ind = assertLens lens schema value prf isj
    in ?assertLens_rhs_9

stripPostfix : Eq a => List a -> List a -> (List a, List a)
stripPostfix (a::as) (b::bs) =
    if a == b
    then stripPostfix as bs
    else (a::as, b::bs)
stripPostfix a b = (a, b)

transform : List Lens -> List Lens -> List Lens
transform a b =
    let
        a = reverse a
        b = reverse b
        (a, b) = stripPostfix a b
        a = reverse a
        a = map reverseLens a
    in a ++ b
