module Fcrdt.Lens

import Data.List
import Data.Maybe

%default total

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
    map = (delete key (insert key value map))
lemmaDeleteAfterInsert key value [] = rewrite lemmaNatEquality key in Refl
lemmaDeleteAfterInsert key value ((k, v) :: xs) = ?todo

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
    | SArray Schema
    | SObject (List (Nat, (Bool, Schema)))

schemaOf : Value -> Schema
schemaOf (Boolean x) = SBoolean
schemaOf (Number x) = SNumber
schemaOf (Text x) = SText
schemaOf (Array x) = SArray SFalse
schemaOf (Object x) = SObject empty

validate : Schema -> Value -> Bool
validate SFalse _ = False
validate SBoolean (Boolean _) = True
validate SBoolean _ = False
validate SNumber (Number _) = True
validate SNumber _ = False
validate SText (Text _) = True
validate SText _ = False
validate (SArray _) (Array []) = True
validate (SArray schema) (Array (y :: xs)) = validate schema y && validate (SArray schema) (Array xs)
validate (SArray _) _ = False
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
    | WrapProperty Nat
    | HeadProperty Nat
    | LensIn Nat Lens
    | LensMap Lens

Eq Lens where
    AddProperty p1 r1 v1 == AddProperty p2 r2 v2 = p1 == p2 && r1 == r2 && v1 == v2
    RemoveProperty p1 r1 v1 == RemoveProperty p2 r2 v2 = p1 == p2 && r1 == r2 && v1 == v2
    RenameProperty a1 b1 == RenameProperty a2 b2 = a1 == a2 && b1 == b2
    HoistProperty h1 p1 == HoistProperty h2 p2 = h1 == h2 && p1 == p2
    PlungeProperty h1 p1 == PlungeProperty h2 p2 = h1 == h2 && p1 == p2
    WrapProperty p1 == WrapProperty p2 = p1 == p2
    HeadProperty p1 == HeadProperty p2 = p1 == p2
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
applyLensSchema (WrapProperty key) (SObject ps) =
    case get key ps of
        Just (required, schema) =>
            Just (SObject (insert key (required, (SArray schema)) ps))
        Nothing => Nothing
applyLensSchema (WrapProperty _) _ = Nothing
applyLensSchema (HeadProperty key) (SObject ps) =
    case get key ps of
        Just (required, SArray schema) =>
            Just (SObject (insert key (required, schema) ps))
        _ => Nothing
applyLensSchema (HeadProperty _) _ = Nothing
applyLensSchema (LensIn key lens) (SObject ps) =
    case get key ps of
        Just (_, schema) => applyLensSchema lens schema
        Nothing => Nothing
applyLensSchema (LensIn _ _) _ = Nothing
applyLensSchema (LensMap lens) SFalse =
    applyLensSchema (LensMap lens) (SArray SFalse)
applyLensSchema (LensMap lens) (SArray schema) =
    case applyLensSchema lens schema of
        Just schema => Just (SArray schema)
        Nothing => Nothing
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
applyLensValue (WrapProperty x) v = Just (Array (v :: Nil))
-- not very useful transform if it only works with one array element
-- need to revisit the reversability property
applyLensValue (HeadProperty x) (Array (v :: Nil)) = Just v
applyLensValue (HeadProperty _) _ = Nothing
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
reverseLens (WrapProperty x) = HeadProperty x
reverseLens (HeadProperty x) = WrapProperty x
reverseLens (LensIn x y) = LensIn x (reverseLens y)
reverseLens (LensMap x) = LensMap (reverseLens x)

reverseSchema : Lens -> Schema -> Maybe Schema
reverseSchema l s =
    case applyLensSchema l s of
        Just s => applyLensSchema (reverseLens l) s
        Nothing => Nothing

assertReverseSchema :
    (lens: Lens) ->
    (schema: Schema) ->
    (isJust (applyLensSchema lens schema) = True) ->
    (reverseSchema lens schema = Just schema)
assertReverseSchema (AddProperty n False v) SFalse Refl = ?assertReverseSchema_rhs_25
assertReverseSchema (AddProperty n True v) SFalse Refl = ?assertReverseSchema_rhs_26
assertReverseSchema (AddProperty _ _ _) SBoolean Refl impossible
assertReverseSchema (AddProperty _ _ _) SNumber Refl impossible
assertReverseSchema (AddProperty _ _ _) SText Refl impossible
assertReverseSchema (AddProperty _ _ _) (SArray _) Refl impossible
assertReverseSchema (AddProperty x y z) (SObject w) prf = ?assertReverseSchema_rhs_15
assertReverseSchema (RemoveProperty _ _ _) SFalse Refl impossible
assertReverseSchema (RemoveProperty _ _ _) SBoolean Refl impossible
assertReverseSchema (RemoveProperty _ _ _) SNumber Refl impossible
assertReverseSchema (RemoveProperty _ _ _) SText Refl impossible
assertReverseSchema (RemoveProperty _ _ _) (SArray _) Refl impossible
assertReverseSchema (RemoveProperty x y z) (SObject w) prf = ?assertReverseSchema_rhs_17
assertReverseSchema (RenameProperty _ _) SFalse Refl impossible
assertReverseSchema (RenameProperty _ _) SBoolean Refl impossible
assertReverseSchema (RenameProperty _ _) SNumber Refl impossible
assertReverseSchema (RenameProperty _ _) SText Refl impossible
assertReverseSchema (RenameProperty _ _) (SArray _) Refl impossible
assertReverseSchema (RenameProperty x y) (SObject z) prf = ?assertReverseSchema_rhs_18
assertReverseSchema (HoistProperty _ _) SFalse Refl impossible
assertReverseSchema (HoistProperty _ _) SBoolean Refl impossible
assertReverseSchema (HoistProperty _ _) SNumber Refl impossible
assertReverseSchema (HoistProperty _ _) SText Refl impossible
assertReverseSchema (HoistProperty _ _) (SArray _) Refl impossible
assertReverseSchema (HoistProperty x y) (SObject z) prf = ?assertReverseSchema_rhs_19
assertReverseSchema (PlungeProperty _ _) SFalse Refl impossible
assertReverseSchema (PlungeProperty _ _) SBoolean Refl impossible
assertReverseSchema (PlungeProperty _ _) SNumber Refl impossible
assertReverseSchema (PlungeProperty _ _) SText Refl impossible
assertReverseSchema (PlungeProperty _ _) (SArray _) Refl impossible
assertReverseSchema (PlungeProperty x y) (SObject z) prf = ?assertReverseSchema_rhs_20
assertReverseSchema (WrapProperty _) SFalse Refl impossible
assertReverseSchema (WrapProperty _) SBoolean Refl impossible
assertReverseSchema (WrapProperty _) SNumber Refl impossible
assertReverseSchema (WrapProperty _) SText Refl impossible
assertReverseSchema (WrapProperty _) (SArray _) Refl impossible
assertReverseSchema (WrapProperty _) (SObject []) Refl impossible
assertReverseSchema (WrapProperty n) (SObject (x :: xs)) prf = ?assertReverseSchema_rhs_29
assertReverseSchema (HeadProperty _) SFalse Refl impossible
assertReverseSchema (HeadProperty _) SBoolean Refl impossible
assertReverseSchema (HeadProperty _) SNumber Refl impossible
assertReverseSchema (HeadProperty _) SText Refl impossible
assertReverseSchema (HeadProperty _) (SArray _) Refl impossible
assertReverseSchema (HeadProperty _) (SObject []) Refl impossible
assertReverseSchema (HeadProperty n) (SObject (x :: xs)) prf = ?assertReverseSchema_rhs_30
assertReverseSchema (LensIn _ _) SFalse Refl impossible
assertReverseSchema (LensIn _ _) SBoolean Refl impossible
assertReverseSchema (LensIn _ _) SNumber Refl impossible
assertReverseSchema (LensIn _ _) SText Refl impossible
assertReverseSchema (LensIn _ _) (SArray _) Refl impossible
assertReverseSchema (LensIn x y) (SObject z) prf = ?assertReverseSchema_rhs_23
assertReverseSchema (LensMap x) SFalse prf = ?assertReverseSchema_rhs_24
assertReverseSchema (LensMap _) SBoolean Refl impossible
assertReverseSchema (LensMap _) SNumber Refl impossible
assertReverseSchema (LensMap _) SText Refl impossible
assertReverseSchema (LensMap x) (SArray y) prf = ?assertReverseSchema_rhs_28
assertReverseSchema (LensMap _) (SObject _) Refl impossible

reverseValue : Lens -> Value -> Maybe Value
reverseValue l v =
    case applyLensValue l v of
        Just v => applyLensValue (reverseLens l) v
        Nothing => Nothing

assertReverseValue :
    (lens: Lens) ->
    (value: Value) ->
    (isJust (applyLensValue lens value) = True) ->
    (reverseValue lens value = Just value)
assertReverseValue (AddProperty _ _ _) (Boolean _) Refl impossible
assertReverseValue (AddProperty _ _ _) (Number _) Refl impossible
assertReverseValue (AddProperty _ _ _) (Text _) Refl impossible
assertReverseValue (AddProperty _ _ _) (Array _) Refl impossible
assertReverseValue (AddProperty _ False _) (Object []) _ = Refl
assertReverseValue (AddProperty n False v) (Object (x :: xs)) prf = ?assertReverseValueAddProperty
assertReverseValue (AddProperty n True v) (Object []) Refl = ?assertReverseValueAddPropertyRequired_1
assertReverseValue (AddProperty n True v) (Object (x :: xs)) prf = ?assertReverseValueAddPropertyRequired_2
assertReverseValue (RemoveProperty _ _ _) (Boolean _) Refl impossible
assertReverseValue (RemoveProperty _ _ _) (Number _) Refl impossible
assertReverseValue (RemoveProperty _ _ _) (Text _) Refl impossible
assertReverseValue (RemoveProperty _ _ _) (Array _) Refl impossible
assertReverseValue (RemoveProperty x False z) (Object w) prf = ?assertReverseValueRemoveProperty
assertReverseValue (RemoveProperty x True z) (Object w) prf = ?assertReverseValueRemovePropertyRequired
assertReverseValue (RenameProperty _ _) (Boolean _) Refl impossible
assertReverseValue (RenameProperty _ _) (Number _) Refl impossible
assertReverseValue (RenameProperty _ _) (Text _) Refl impossible
assertReverseValue (RenameProperty _ _) (Array _) Refl impossible
assertReverseValue (RenameProperty _ _) (Object []) Refl impossible
assertReverseValue (RenameProperty a b) (Object (x :: xs)) prf = ?assertReverseValueRenameProperty
assertReverseValue (HoistProperty _ _) (Boolean _) Refl impossible
assertReverseValue (HoistProperty _ _) (Number _) Refl impossible
assertReverseValue (HoistProperty _ _) (Text _) Refl impossible
assertReverseValue (HoistProperty _ _) (Array _) Refl impossible
assertReverseValue (HoistProperty _ _) (Object []) Refl impossible
assertReverseValue (HoistProperty h n) (Object (x :: xs)) prf = ?assertReverseValueHoistProperty
assertReverseValue (PlungeProperty _ _) (Boolean _) Refl impossible
assertReverseValue (PlungeProperty _ _) (Number _) Refl impossible
assertReverseValue (PlungeProperty _ _) (Text _) Refl impossible
assertReverseValue (PlungeProperty _ _) (Array _) Refl impossible
assertReverseValue (PlungeProperty _ _) (Object []) Refl impossible
assertReverseValue (PlungeProperty h n) (Object (x :: xs)) prf = ?assertReverseValuePlungeProperty
assertReverseValue (WrapProperty x) value prf  = Refl
assertReverseValue (HeadProperty _) (Boolean _) Refl impossible
assertReverseValue (HeadProperty _) (Number _) Refl impossible
assertReverseValue (HeadProperty _) (Text _) Refl impossible
assertReverseValue (HeadProperty _) (Array []) Refl impossible
assertReverseValue (HeadProperty _) (Array (x :: [])) Refl = Refl
assertReverseValue (HeadProperty _) (Array (_ :: (_ :: _))) Refl impossible
assertReverseValue (HeadProperty _) (Object _) Refl impossible
assertReverseValue (LensIn _ _) (Boolean _) Refl impossible
assertReverseValue (LensIn _ _) (Number _) Refl impossible
assertReverseValue (LensIn _ _) (Text _) Refl impossible
assertReverseValue (LensIn _ _) (Array _) Refl impossible
assertReverseValue (LensIn _ _) (Object []) Refl impossible
assertReverseValue (LensIn key lens) (Object (x :: xs)) prf = ?assertReverseValueLensIn
assertReverseValue (LensMap _) (Boolean _) Refl impossible
assertReverseValue (LensMap _) (Number _) Refl impossible
assertReverseValue (LensMap _) (Text _) Refl impossible
assertReverseValue (LensMap lens) (Array []) Refl = Refl
assertReverseValue (LensMap lens) (Array (x :: xs)) prf = ?assertReverseValueLensMap
assertReverseValue (LensMap _) (Object _) Refl impossible

schemaJustImpliesValueJust :
    (lens: Lens) ->
    (schema: Schema) ->
    (value: Value) ->
    (validate schema value = True) ->
    (isJust (applyLensSchema lens schema) = True) ->
    (isJust (applyLensValue lens value) = True)

schemaJustImpliesValueJust (AddProperty _ _ _) SFalse _ _ Refl impossible
schemaJustImpliesValueJust (AddProperty _ _ _) SBoolean _ _ Refl impossible
schemaJustImpliesValueJust (AddProperty _ _ _) SNumber _ _ Refl impossible
schemaJustImpliesValueJust (AddProperty _ _ _) SText _ _ Refl impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SArray _) _ _ Refl impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject []) (Object []) _ _ = Refl
schemaJustImpliesValueJust (AddProperty n r v) (SObject []) (Object (x :: xs)) prf Refl = ?schemaJustImpliesValueJust_rhs_40
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject (x :: xs)) (Object []) _ _ = Refl
schemaJustImpliesValueJust (AddProperty n r v) (SObject (x :: xs)) (Object (y :: ys)) prf prf1 = ?schemaJustImpliesValueJust_rhs_39
schemaJustImpliesValueJust (RemoveProperty _ _ _) SFalse _ _ Refl impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) SBoolean _ _ Refl impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) SNumber _ _ Refl impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) SText _ _ Refl impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SArray _) _ _ Refl impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (RemoveProperty x y z) (SObject w) (Object v) prf prf1 = ?schemaJustImpliesValueJust_rhs_28
schemaJustImpliesValueJust (RenameProperty _ _) SFalse _ _ Refl impossible
schemaJustImpliesValueJust (RenameProperty _ _) SBoolean _ _ Refl impossible
schemaJustImpliesValueJust (RenameProperty _ _) SNumber _ _ Refl impossible
schemaJustImpliesValueJust (RenameProperty _ _) SText _ _ Refl impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SArray _) _ _ Refl impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (RenameProperty x y) (SObject z) (Object w) prf prf1 = ?schemaJustImpliesValueJust_rhs_29
schemaJustImpliesValueJust (HoistProperty _ _) SFalse _ _ Refl impossible
schemaJustImpliesValueJust (HoistProperty _ _) SBoolean _ _ Refl impossible
schemaJustImpliesValueJust (HoistProperty _ _) SNumber _ _ Refl impossible
schemaJustImpliesValueJust (HoistProperty _ _) SText _ _ Refl impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SArray _) _ _ Refl impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (HoistProperty x y) (SObject z) (Object w) prf prf1 = ?schemaJustImpliesValueJust_rhs_30
schemaJustImpliesValueJust (PlungeProperty _ _) SFalse _ _ Refl impossible
schemaJustImpliesValueJust (PlungeProperty _ _) SBoolean _ _ Refl impossible
schemaJustImpliesValueJust (PlungeProperty _ _) SNumber _ _ Refl impossible
schemaJustImpliesValueJust (PlungeProperty _ _) SText _ _ Refl impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SArray _) _ _ Refl impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (PlungeProperty x y) (SObject z) (Object w) prf prf1 = ?schemaJustImpliesValueJust_rhs_31
schemaJustImpliesValueJust (WrapProperty _) SFalse _ _ Refl impossible
schemaJustImpliesValueJust (WrapProperty _) SBoolean _ _ Refl impossible
schemaJustImpliesValueJust (WrapProperty _) SNumber _ _ Refl impossible
schemaJustImpliesValueJust (WrapProperty _) SText _ _ Refl impossible
schemaJustImpliesValueJust (WrapProperty _) (SArray _) _ _ Refl impossible
schemaJustImpliesValueJust (WrapProperty _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (WrapProperty _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (WrapProperty _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (WrapProperty _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (WrapProperty _) (SObject _) (Object _) _ _ = Refl
schemaJustImpliesValueJust (HeadProperty _) SFalse _ _ Refl impossible
schemaJustImpliesValueJust (HeadProperty _) SBoolean _ _ Refl impossible
schemaJustImpliesValueJust (HeadProperty _) SNumber _ _ Refl impossible
schemaJustImpliesValueJust (HeadProperty _) SText _ _ Refl impossible
schemaJustImpliesValueJust (HeadProperty _) (SArray _) _ _ Refl impossible
schemaJustImpliesValueJust (HeadProperty _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (HeadProperty _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (HeadProperty _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (HeadProperty _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (HeadProperty x) (SObject y) (Object z) prf prf1 = ?schemaJustImpliesValueJust_rhs_33
schemaJustImpliesValueJust (LensIn _ _) SFalse _ _ Refl impossible
schemaJustImpliesValueJust (LensIn _ _) SBoolean _ _ Refl impossible
schemaJustImpliesValueJust (LensIn _ _) SNumber _ _ Refl impossible
schemaJustImpliesValueJust (LensIn _ _) SText _ _ Refl impossible
schemaJustImpliesValueJust (LensIn _ _) (SArray _) _ _ Refl impossible
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
schemaJustImpliesValueJust (LensMap _) SBoolean _ _ Refl impossible
schemaJustImpliesValueJust (LensMap _) SNumber _ _ Refl impossible
schemaJustImpliesValueJust (LensMap _) SText _ _ Refl impossible
schemaJustImpliesValueJust (LensMap _) (SArray _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (LensMap _) (SArray _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (LensMap _) (SArray _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (LensMap x) (SArray y) (Array xs) prf prf1 = ?schemaJustImpliesValueJust_rhs_19
schemaJustImpliesValueJust (LensMap _) (SArray _) (Object _) Refl _ impossible
schemaJustImpliesValueJust (LensMap _) (SObject _) _ _ Refl impossible

validateLensed : Lens -> Schema -> Value -> Bool
validateLensed l s v =
    case (applyLensSchema l s, applyLensValue l v) of
        (Just s, Just v) => validate s v
        _ => False

assertLens :
    (lens: Lens) ->
    (schema: Schema) ->
    (value: Value) ->
    (validate schema value = True) ->
    (isJust (applyLensSchema lens schema) = True) ->
    (validateLensed lens schema value = True)
assertLens (AddProperty x y z) schema value prf prf1 = ?assertLens_rhs_1
assertLens (RemoveProperty x y z) schema value prf prf1 = ?assertLens_rhs_2
assertLens (RenameProperty x y) schema value prf prf1 = ?assertLens_rhs_3
assertLens (HoistProperty x y) schema value prf prf1 = ?assertLens_rhs_4
assertLens (PlungeProperty x y) schema value prf prf1 = ?assertLens_rhs_5
assertLens (WrapProperty x) schema value prf prf1 = ?assertLens_rhs_6
assertLens (HeadProperty x) schema value prf prf1 = ?assertLens_rhs_7
assertLens (LensIn x y) schema value prf prf1 = ?assertLens_rhs_8
assertLens (LensMap x) schema value prf prf1 = ?assertLens_rhs_9

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
