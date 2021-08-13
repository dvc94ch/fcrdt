module Fcrdt.Lens

import Data.List
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
    | SObject (SortedMap String Schema)

validate : Schema -> Value -> Bool
validate STrue value = True
validate SFalse value = False
validate (SAnd x y) value = (validate x value) && (validate y value)
validate (SOr x y) value = (validate x value) || (validate y value)
validate (SNot x) value = not (validate x value)
validate SNull value = (kindOf value) == NullKind
validate SBoolean value = (kindOf value) == BooleanKind
validate SNumber value = (kindOf value) == NumberKind
validate SText value = (kindOf value) == TextKind
validate (SArray x) value = (kindOf value) == ArrayKind -- && (reduce True value (validate x))
validate (SObject x) value = (kindOf value) == ObjectKind -- && (reduce True value

data Lens =
      AddProperty String (List Kind) Value
    | RemoveProperty String (List Kind) Value
    | RenameProperty String String
    | HoistProperty String String
    | PlungeProperty String String
    | WrapProperty String
    | HeadProperty String
    | LensIn String Lens
    | LensMap Lens
    | Sequence Lens Lens

applyLens : Lens -> Lens -> Lens
applyLens a b = Sequence a b

applyLensSchema : Lens -> Schema -> Schema
applyLensSchema lens schema = schema

lensToSchema : Lens -> Schema
lensToSchema lens = applyLensSchema lens STrue

applyLensValue : Lens -> Value -> Value
applyLensValue lens value = value

reverseLens : Lens -> Lens
reverseLens (AddProperty x xs y) = RemoveProperty x xs y
reverseLens (RemoveProperty x xs y) = AddProperty x xs y
reverseLens (RenameProperty x y) = RenameProperty y x
reverseLens (HoistProperty x y) = PlungeProperty x y
reverseLens (PlungeProperty x y) = HoistProperty x y
reverseLens (WrapProperty x) = HeadProperty x
reverseLens (HeadProperty x) = WrapProperty x
reverseLens (LensIn x y) = LensIn x (reverseLens y)
reverseLens (LensMap x) = LensMap (reverseLens x)
reverseLens (Sequence a b) = Sequence b a

total assertReverseSchema :
    (lens: Lens) ->
    (schema: Schema) ->
    (applyLensSchema (reverseLens lens) (applyLensSchema lens schema)) = schema
assertReverseSchema lens schema = Refl

total assertReverseValue :
    (lens: Lens) ->
    (value: Value) ->
    (applyLensValue (reverseLens lens) (applyLensValue lens value)) = value
assertReverseValue lens value = Refl

total assertLens :
    (lens: Lens) ->
    (schema: Schema) ->
    (value: Value) ->
    (Dec ((validate schema value) = True)) ->
    (Dec ((validate (applyLensSchema lens schema) (applyLensValue lens value)) = True))
assertLens lens schema value = ?x

transform: Lens -> Lens -> Lens
transform a b = a

total assertTransform :
    (a: Lens) ->
    (b: Lens) ->
    (Dec ((validate (lensToSchema a) value) = True)) ->
    (Dec ((validate (lensToSchema b) (applyLensValue (transform a b) value)) = True))
assertTransform a b = ?y
