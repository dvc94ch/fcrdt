module Fcrdt.Lens

import Data.List
import Data.Maybe
import Data.SortedMap

data Value =
      Null
    | Boolean Bool
    | Number Int
    | Text String
    | Array (List Value)
    | Object (SortedMap String Value)

data Kind =
      NullKind
    | BooleanKind
    | NumberKind
    | TextKind
    | ArrayKind
    | ObjectKind

Eq Kind where
    NullKind == NullKind = True
    BooleanKind == BooleanKind = True
    NumberKind == NumberKind = True
    TextKind == TextKind = True
    ArrayKind == ArrayKind = True
    ObjectKind == ObjectKind = True
    a == b = False

kindOf : Value -> Kind
kindOf Null = NullKind
kindOf (Boolean x) = BooleanKind
kindOf (Number x) = NumberKind
kindOf (Text x) = TextKind
kindOf (Array xs) = ArrayKind
kindOf (Object x) = ObjectKind

data Schema =
      STrue
    | SFalse
    | SAnd Schema Schema
    | SOr Schema Schema
    | SNot Schema
    | SNull
    | SBoolean
    | SNumber
    | SText
    | SArray Schema
    | SObject String Bool Schema

validate : Schema -> Value -> Bool
validate STrue _ = True
validate SFalse _ = False
validate (SAnd x y) value = (validate x value) && (validate y value)
validate (SOr x y) value = (validate x value) || (validate y value)
validate (SNot x) value = not (validate x value)
validate SNull Null = True
validate SNull _ = False
validate SBoolean (Boolean _) = True
validate SBoolean _ = False
validate SNumber (Number _) = True
validate SNumber _ = False
validate SText (Text _) = True
validate SText _ = False
validate (SArray x) (Array vs) = foldr (\elem, acc => acc && (validate x elem)) True vs
validate (SArray _) _ = False
validate (SObject key required schema) (Object ps) =
    case lookup key ps of
        Just v => validate schema v
        Nothing => not required
validate (SObject _ _ _) _ = False

data Lens =
      AddProperty String Value
    | RemoveProperty String Value
    | RenameProperty String String
    | HoistProperty String String
    | PlungeProperty String String
    | WrapProperty String
    | HeadProperty String
    | LensIn String Lens
    | LensMap Lens
    | Sequence Lens Lens
--    | Convert (List (Value, Value))

applyLens : Lens -> Lens -> Lens
applyLens a b = Sequence a b

applyLensSchema : Lens -> Schema -> Schema
applyLensSchema (AddProperty x y) schema = ?x_1
applyLensSchema (RemoveProperty x y) schema = ?x_2
applyLensSchema (RenameProperty x y) schema = ?x_3
applyLensSchema (HoistProperty x y) schema = ?x_4
applyLensSchema (PlungeProperty x y) schema = ?x_5
applyLensSchema (WrapProperty x) schema = ?x_6
applyLensSchema (HeadProperty x) schema = ?x_7
applyLensSchema (LensIn x y) schema = ?x_8
applyLensSchema (LensMap x) schema = ?x_9
applyLensSchema (Sequence x y) schema = (applyLensSchema y (applyLensSchema x schema))
-- applyLensSchema (Convert map) schema = ?x_10

lensToSchema : Lens -> Schema
lensToSchema lens = applyLensSchema lens STrue

applyLensValue : Lens -> Value -> Maybe Value
applyLensValue (AddProperty n d) (Object ps) =
    if isNothing (lookup n ps)
    then Just (Object (insert n d ps))
    else Nothing
applyLensValue (AddProperty _ _) _ = Nothing
applyLensValue (RemoveProperty n d) (Object ps) =
    if isJust (lookup n ps)
    then Just (Object (delete n ps))
    else Nothing
applyLensValue (RemoveProperty _ _) _ = Nothing
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
applyLensValue (Sequence x y) value =
    case applyLensValue x value of
        Just value => applyLensValue y value
        Nothing => Nothing
-- applyLensValue (Convert _) (Array _) = Nothing
-- applyLensValue (Convert _) (Object _) = Nothing
-- applyLensValue (Convert Nil) _ = Just

reverseLens : Lens -> Lens
reverseLens (AddProperty x y) = RemoveProperty x y
reverseLens (RemoveProperty x y) = AddProperty x y
reverseLens (RenameProperty x y) = RenameProperty y x
reverseLens (HoistProperty x y) = PlungeProperty x y
reverseLens (PlungeProperty x y) = HoistProperty x y
reverseLens (WrapProperty x) = HeadProperty x
reverseLens (HeadProperty x) = WrapProperty x
reverseLens (LensIn x y) = LensIn x (reverseLens y)
reverseLens (LensMap x) = LensMap (reverseLens x)
reverseLens (Sequence a b) = Sequence b a
-- reverseLens (Convert cs) = Convert (map (\(k, v) => (v, k)) cs)

{-total assertReverseSchema :
    (lens: Lens) ->
    (schema: Schema) ->
    (applyLensSchema (reverseLens lens) (applyLensSchema lens schema)) = schema
assertReverseSchema lens schema = ?y-}

{-total assertReverseValue :
    (lens: Lens) ->
    (value: Value) ->
    (applyLensValue (reverseLens lens) (applyLensValue lens value)) = value
assertReverseValue lens value = ?z-}

{-total assertLens :
    (lens: Lens) ->
    (schema: Schema) ->
    (value: Value) ->
    (Dec ((validate schema value) = True)) ->
    (Dec ((validate (applyLensSchema lens schema) (applyLensValue lens value)) = True))
assertLens lens schema value = ?v-}

transform: Lens -> Lens -> Lens
transform a b = ?a

{-total assertTransform :
    (a: Lens) ->
    (b: Lens) ->
    (Dec ((validate (lensToSchema a) value) = True)) ->
    (Dec ((validate (lensToSchema b) (applyLensValue (transform a b) value)) = True))
assertTransform a b = ?w-}
