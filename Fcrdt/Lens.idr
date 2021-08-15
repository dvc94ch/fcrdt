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
applyLensSchema (LensMap lens) SFalse =
    applyLensSchema (LensMap lens) (SArray True SFalse)
applyLensSchema (LensMap lens) (SArray allowEmpty schema) =
    case applyLensSchema lens schema of
        Just schema => Just (SArray allowEmpty schema)
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

reverseSchema : Lens -> Schema -> Maybe Schema
reverseSchema l s =
    case applyLensSchema l s of
        Just s => applyLensSchema (reverseLens l) s
        Nothing => Nothing

||| Forwards and backwards compatibility requires schema transformations to be reversible
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
assertReverseSchema (AddProperty _ _ _) (SArray _ _) Refl impossible
assertReverseSchema (AddProperty x y z) (SObject w) prf = ?assertReverseSchema_rhs_15
assertReverseSchema (RemoveProperty _ _ _) SFalse Refl impossible
assertReverseSchema (RemoveProperty _ _ _) SBoolean Refl impossible
assertReverseSchema (RemoveProperty _ _ _) SNumber Refl impossible
assertReverseSchema (RemoveProperty _ _ _) SText Refl impossible
assertReverseSchema (RemoveProperty _ _ _) (SArray _ _) Refl impossible
assertReverseSchema (RemoveProperty x y z) (SObject w) prf = ?assertReverseSchema_rhs_17
assertReverseSchema (RenameProperty _ _) SFalse Refl impossible
assertReverseSchema (RenameProperty _ _) SBoolean Refl impossible
assertReverseSchema (RenameProperty _ _) SNumber Refl impossible
assertReverseSchema (RenameProperty _ _) SText Refl impossible
assertReverseSchema (RenameProperty _ _) (SArray _ _) Refl impossible
assertReverseSchema (RenameProperty x y) (SObject z) prf = ?assertReverseSchema_rhs_18
assertReverseSchema (HoistProperty _ _) SFalse Refl impossible
assertReverseSchema (HoistProperty _ _) SBoolean Refl impossible
assertReverseSchema (HoistProperty _ _) SNumber Refl impossible
assertReverseSchema (HoistProperty _ _) SText Refl impossible
assertReverseSchema (HoistProperty _ _) (SArray _ _) Refl impossible
assertReverseSchema (HoistProperty x y) (SObject z) prf = ?assertReverseSchema_rhs_19
assertReverseSchema (PlungeProperty _ _) SFalse Refl impossible
assertReverseSchema (PlungeProperty _ _) SBoolean Refl impossible
assertReverseSchema (PlungeProperty _ _) SNumber Refl impossible
assertReverseSchema (PlungeProperty _ _) SText Refl impossible
assertReverseSchema (PlungeProperty _ _) (SArray _ _) Refl impossible
assertReverseSchema (PlungeProperty x y) (SObject z) prf = ?assertReverseSchema_rhs_20
assertReverseSchema WrapProperty _ _ = Refl
assertReverseSchema HeadProperty SFalse Refl impossible
assertReverseSchema HeadProperty SBoolean Refl impossible
assertReverseSchema HeadProperty SNumber Refl impossible
assertReverseSchema HeadProperty SText Refl impossible
assertReverseSchema HeadProperty (SArray False _) prf = Refl
assertReverseSchema HeadProperty (SArray True _) Refl impossible
assertReverseSchema HeadProperty (SObject _) Refl impossible
assertReverseSchema (LensIn _ _) SFalse Refl impossible
assertReverseSchema (LensIn _ _) SBoolean Refl impossible
assertReverseSchema (LensIn _ _) SNumber Refl impossible
assertReverseSchema (LensIn _ _) SText Refl impossible
assertReverseSchema (LensIn _ _) (SArray _ _) Refl impossible
assertReverseSchema (LensIn x y) (SObject z) prf = ?assertReverseSchema_rhs_23
assertReverseSchema (LensMap x) SFalse prf = ?assertReverseSchema_rhs_24
assertReverseSchema (LensMap _) SBoolean Refl impossible
assertReverseSchema (LensMap _) SNumber Refl impossible
assertReverseSchema (LensMap _) SText Refl impossible
assertReverseSchema (LensMap l) (SArray allowEmpty schema) prf = ?assertReverseSchemaLensMap
assertReverseSchema (LensMap _) (SObject _) Refl impossible

||| If transforming the schema succeeds, transforming the value must succeed
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
schemaJustImpliesValueJust (AddProperty _ _ _) (SArray _ _) _ _ Refl impossible
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
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SArray _ _) _ _ Refl impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (RemoveProperty x y z) (SObject w) (Object v) prf prf1 = ?schemaJustImpliesValueJust_rhs_28
schemaJustImpliesValueJust (RenameProperty _ _) SFalse _ _ Refl impossible
schemaJustImpliesValueJust (RenameProperty _ _) SBoolean _ _ Refl impossible
schemaJustImpliesValueJust (RenameProperty _ _) SNumber _ _ Refl impossible
schemaJustImpliesValueJust (RenameProperty _ _) SText _ _ Refl impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SArray _ _) _ _ Refl impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (RenameProperty x y) (SObject z) (Object w) prf prf1 = ?schemaJustImpliesValueJust_rhs_29
schemaJustImpliesValueJust (HoistProperty _ _) SFalse _ _ Refl impossible
schemaJustImpliesValueJust (HoistProperty _ _) SBoolean _ _ Refl impossible
schemaJustImpliesValueJust (HoistProperty _ _) SNumber _ _ Refl impossible
schemaJustImpliesValueJust (HoistProperty _ _) SText _ _ Refl impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SArray _ _) _ _ Refl impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (HoistProperty x y) (SObject z) (Object w) prf prf1 = ?schemaJustImpliesValueJust_rhs_30
schemaJustImpliesValueJust (PlungeProperty _ _) SFalse _ _ Refl impossible
schemaJustImpliesValueJust (PlungeProperty _ _) SBoolean _ _ Refl impossible
schemaJustImpliesValueJust (PlungeProperty _ _) SNumber _ _ Refl impossible
schemaJustImpliesValueJust (PlungeProperty _ _) SText _ _ Refl impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SArray _ _) _ _ Refl impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (PlungeProperty x y) (SObject z) (Object w) prf prf1 = ?schemaJustImpliesValueJust_rhs_31
schemaJustImpliesValueJust WrapProperty _ _ _ _ = Refl
schemaJustImpliesValueJust HeadProperty SFalse _ _ Refl impossible
schemaJustImpliesValueJust HeadProperty SBoolean _ _ Refl impossible
schemaJustImpliesValueJust HeadProperty SNumber _ _ Refl impossible
schemaJustImpliesValueJust HeadProperty SText _ _ Refl impossible
schemaJustImpliesValueJust HeadProperty (SArray _ _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust HeadProperty (SArray _ _) (Number _) Refl _ impossible
schemaJustImpliesValueJust HeadProperty (SArray _ _) (Text _) Refl _ impossible
schemaJustImpliesValueJust HeadProperty (SArray False _) (Array []) Refl _ impossible
schemaJustImpliesValueJust HeadProperty (SArray False _) (Array (x :: xs)) _ _ = Refl
schemaJustImpliesValueJust HeadProperty (SArray True _) (Array _) _ Refl impossible
schemaJustImpliesValueJust HeadProperty (SArray _ _) (Object _) Refl _ impossible
schemaJustImpliesValueJust HeadProperty (SObject _) _ _ Refl impossible
schemaJustImpliesValueJust (LensIn _ _) SFalse _ _ Refl impossible
schemaJustImpliesValueJust (LensIn _ _) SBoolean _ _ Refl impossible
schemaJustImpliesValueJust (LensIn _ _) SNumber _ _ Refl impossible
schemaJustImpliesValueJust (LensIn _ _) SText _ _ Refl impossible
schemaJustImpliesValueJust (LensIn _ _) (SArray _ _) _ _ Refl impossible
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
schemaJustImpliesValueJust (LensMap _) (SArray _ _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (LensMap _) (SArray _ _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (LensMap _) (SArray _ _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (LensMap l) (SArray allowEmpty schema) (Array xs) prf prf1 = ?schemaJustImpliesValueJust_rhs_19
schemaJustImpliesValueJust (LensMap _) (SArray _ _) (Object _) Refl _ impossible
schemaJustImpliesValueJust (LensMap _) (SObject _) _ _ Refl impossible

validateLensed : Lens -> Schema -> Value -> Bool
validateLensed l s v =
    case (applyLensSchema l s, applyLensValue l v) of
        (Just s, Just v) => validate s v
        _ => False

||| Transforming a valid value must result in a valid value
assertLens :
    (lens: Lens) ->
    (schema: Schema) ->
    (value: Value) ->
    (validate schema value = True) ->
    (isJust (applyLensSchema lens schema) = True) ->
    (validateLensed lens schema value = True)
assertLens lens schema value prf prf1 = ?assertLens_rhs

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
