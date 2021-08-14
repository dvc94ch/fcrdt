module Fcrdt.Lens

import Data.List
import Data.Maybe
import Data.SortedMap

||| TODO
||| Implement convert transform
||| Support combining schemas (and/or)

data Value =
      Boolean Bool
    | Number Int
    | Text String
    | Array (List Value)
    | Object (SortedMap String Value)

Eq Value where
    Boolean b1 == Boolean b2 = b1 == b2
    Number n1 == Number n2 = n1 == n2
    Text t1 == Text t2 = t1 == t2
    Array vs1 == Array vs2 = vs1 == vs2
    Object ps1 == Object ps2 = ps1 == ps2
    _ == _ = False

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
kindOf (Boolean x) = BooleanKind
kindOf (Number x) = NumberKind
kindOf (Text x) = TextKind
kindOf (Array xs) = ArrayKind
kindOf (Object x) = ObjectKind

data Schema =
      SFalse
    | SBoolean
    | SNumber
    | SText
    | SArray Schema
    | SObject (SortedMap String (Bool, Schema))

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
validate (SArray x) (Array vs) = foldr (\elem, acc => acc && (validate x elem)) True vs
validate (SArray _) _ = False
validate (SObject ss) (Object ps) = foldr
    (\(key, (required, schema)), acc =>
        acc && case lookup key ps of
            Just v => validate schema v
            Nothing => not required)
    True
    (SortedMap.toList ss)
validate (SObject _) _ = False

data Lens =
      AddProperty String Bool Value
    | RemoveProperty String Bool Value
    | RenameProperty String String
    | HoistProperty String String
    | PlungeProperty String String
    | WrapProperty String
    | HeadProperty String
    | LensIn String Lens
    | LensMap Lens
--    | Convert (List (Value, Value))

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
    case lookup key ps of
        Just p => Nothing
        Nothing => Just (SObject (insert key (required, schemaOf value) ps))
applyLensSchema (AddProperty _ _ _) _ = Nothing
applyLensSchema (RemoveProperty key _ _) (SObject ps) =
    case lookup key ps of
        Just p => Just (SObject (delete key ps))
        Nothing => Nothing
applyLensSchema (RemoveProperty _ _ _) _ = Nothing
applyLensSchema (RenameProperty x y) (SObject ps) =
    case (lookup x ps, lookup y ps) of
        (Just p, Nothing) => Just (SObject (insert y p (delete x ps)))
        _ => Nothing
applyLensSchema (RenameProperty _ _) _ = Nothing
applyLensSchema (HoistProperty h p) (SObject ps) =
    case lookup h ps of
        Just (required, SObject hps) =>
            (case lookup p hps of
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
    case (lookup n ps, lookup h ps) of
        (Just (required, schema), Nothing) =>
            let
                hps = insert n (required, schema) empty
            in
                Just (SObject (insert h (required, (SObject hps)) (delete n ps)))
        _ => Nothing
applyLensSchema (PlungeProperty _ _) _ = Nothing
applyLensSchema (WrapProperty key) (SObject ps) =
    case lookup key ps of
        Just (required, schema) =>
            Just (SObject (insert key (required, (SArray schema)) ps))
        Nothing => Nothing
applyLensSchema (WrapProperty _) _ = Nothing
applyLensSchema (HeadProperty key) (SObject ps) =
    case lookup key ps of
        Just (required, SArray schema) =>
            Just (SObject (insert key (required, schema) ps))
        _ => Nothing
applyLensSchema (HeadProperty _) _ = Nothing
applyLensSchema (LensIn key lens) (SObject ps) =
    case lookup key ps of
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
-- applyLensSchema (Convert map) schema = ?x_10

lensToSchema : List Lens -> Maybe Schema
lensToSchema [] = Just SFalse
lensToSchema (l::ls) =
    case lensToSchema ls of
        Just s => applyLensSchema l s
        Nothing => Nothing

applyLensValue : Lens -> Value -> Maybe Value
applyLensValue (AddProperty n required d) (Object ps) =
    if isNothing (lookup n ps)
    then Just (Object (if required then insert n d ps else ps))
    else Nothing
applyLensValue (AddProperty _ _ _) _ = Nothing
applyLensValue (RemoveProperty n required d) (Object ps) =
    if isJust (lookup n ps)
    then Just (Object (delete n ps))
    else if required then Nothing else Just (Object ps)
applyLensValue (RemoveProperty _ _ _) _ = Nothing
applyLensValue (RenameProperty x y) (Object ps) =
    case (lookup x ps, lookup y ps) of
        (Just v, Nothing) => Just (Object (insert y v (delete x ps)))
        (x, y) => Nothing
applyLensValue (RenameProperty _ _) _ = Nothing
applyLensValue (HoistProperty hp p) (Object ps) =
    case lookup hp ps of
        Just (Object hps) =>
            (case (lookup p hps, lookup p ps) of
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
    case (lookup p ps, lookup hp ps) of
        (Just v, Nothing) =>
            (let
                ps = (delete p ps)
            in
                Just (Object (insert hp (Object (insert hp v empty)) ps)))
        _ => Nothing
applyLensValue (PlungeProperty _ _) _ = Nothing
applyLensValue (WrapProperty x) v = Just (Array (v :: Nil))
applyLensValue (HeadProperty x) (Array (v :: vs)) = Just v
applyLensValue (HeadProperty _) _ = Nothing
applyLensValue (LensIn x l) (Object ps) =
    case lookup x ps of
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
-- applyLensValue (Convert _) (Array _) = Nothing
-- applyLensValue (Convert _) (Object _) = Nothing
-- applyLensValue (Convert Nil) _ = Just

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
-- reverseLens (Convert cs) = Convert (map (\(k, v) => (v, k)) cs)

{-total assertReverseSchema :
    (lens: Lens) ->
    (schema: Schema) ->
    (applyLensSchema (reverseLens lens) (applyLensSchema lens schema)) = schema
assertReverseSchema lens schema = ?y-}

reverseValue : Lens -> Value -> Maybe Value
reverseValue l v =
    case applyLensValue l v of
        Just v => applyLensValue (reverseLens l) v
        Nothing => Nothing

total assertReverseValue :
    (lens: Lens) ->
    (value: Value) ->
    (Dec (isJust (applyLensValue lens value) = True)) ->
    (Dec ((reverseValue lens value) = Just value))
assertReverseValue lens value = ?z

{-total assertLens :
    (lens: Lens) ->
    (schema: Schema) ->
    (value: Value) ->
    (Dec ((validate schema value) = True)) ->
    (Dec ((validate (applyLensSchema lens schema) (applyLensValue lens value)) = True))
assertLens lens schema value = ?v-}

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

{-total assertTransform :
    (a: Lens) ->
    (b: Lens) ->
    (Dec ((validate (lensToSchema a) value) = True)) ->
    (Dec ((validate (lensToSchema b) (applyLensValue (transform a b) value)) = True))
assertTransform a b = ?w-}
