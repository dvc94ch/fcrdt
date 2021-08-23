module Fcrdt.Lens

import Data.List
import Data.Maybe
import Fcrdt.Map

%default total

data PrimitiveValue =
      Boolean Bool
    | Number Nat
    | Text String

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
    assert_total (validate schema x) && assert_total (validate (SArray True schema) (Array xs))
validate (SArray _ _) _ = False
validate (SObject smap) (Object vmap) = validateProperties (keys vmap) vmap smap && validateRequired (keys smap) smap vmap where
    validateProperties : Set -> Map Value -> Map (Bool, Schema) -> Bool
    validateProperties Empty _ _ = True
    validateProperties (Entry k ks _) vmap smap with (get k vmap, get k smap)
        validateProperties (Entry _ _ _) _ _ | (Nothing, _) = False
        validateProperties (Entry _ _ _) _  _ | (_, Nothing) = False
        validateProperties (Entry k ks _) vmap smap | (Just value , Just (_, schema)) =
            assert_total (validate schema value) && validateProperties ks vmap smap
    validateRequired : Set -> Map (Bool, Schema) -> Map Value -> Bool
    validateRequired Empty _ _ = True
    validateRequired (Entry k ks _) smap vmap with (get k smap, get k vmap)
        validateRequired (Entry k ks _) smap vmap | (Just (True, _), Nothing) = False
        validateRequired (Entry k ks _) smap vmap | (_, _) = validateRequired ks smap vmap
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

convert : PrimitiveValue -> List (PrimitiveValue, PrimitiveValue) -> Maybe PrimitiveValue
convert _ [] = Nothing
convert key ((k, v) :: xs) = if key == k then Just v else convert key xs

convertDefault : PrimitiveValue -> List (PrimitiveValue, PrimitiveValue) -> Maybe PrimitiveValue
convertDefault d m =
    case convert d m of
        Just d' => case convert d' m of
            Just d2 => if d == d2 then Just d' else Nothing
            Nothing => Nothing
        Nothing => Nothing

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
applyLensSchema (Make (KPrimitive KText)) SFalse = Just (SText "")
applyLensSchema (Make KArray) SFalse = Just (SArray True SFalse)
applyLensSchema (Make KObject) SFalse = Just (SObject empty)
applyLensSchema (Make _) _ = Nothing
applyLensSchema (Destroy (KPrimitive KBoolean)) (SBoolean False) = Just SFalse
applyLensSchema (Destroy (KPrimitive KNumber)) (SNumber 0) = Just SFalse
applyLensSchema (Destroy (KPrimitive KText)) (SText "") = Just SFalse
applyLensSchema (Destroy KArray) (SArray True SFalse) = Just SFalse
applyLensSchema (Destroy KObject) (SObject m) with (isEmpty m)
    applyLensSchema (Destroy KObject) (SObject m) | True = Just SFalse
    applyLensSchema (Destroy KObject) (SObject m) | False = Nothing
applyLensSchema (Destroy _) _ = Nothing
applyLensSchema (AddProperty key) (SObject smap) =
    case get key smap of
        Just _ => Nothing
        Nothing => Just (SObject (insert key (False, SFalse) smap))
applyLensSchema (AddProperty _) _ = Nothing
applyLensSchema (RemoveProperty key) (SObject smap) =
    case get key smap of
        Just (False, SFalse) => Just (SObject (delete key smap))
        _ => Nothing
applyLensSchema (RemoveProperty _) _ = Nothing
applyLensSchema (RenameProperty x y) (SObject smap) =
    case (get x smap, get y smap) of
        (Just p, Nothing) =>
            let
                smap = (delete x smap)
                smap = (insert y p smap)
            in Just (SObject smap)
        _ => Nothing
applyLensSchema (RenameProperty _ _) _ = Nothing
applyLensSchema (HoistProperty h t) (SObject m) =
    case (get h m, get t m) of
        (Just (hr, SObject hm), Nothing) =>
            case get t hm of
                Just p =>
                    let
                        hm = delete t hm
                        m = insert t p m
                        m = insert h (hr, SObject hm) m
                     in Just (SObject m)
                Nothing => Nothing
        _ => Nothing
applyLensSchema (HoistProperty _ _) _ = Nothing
applyLensSchema (PlungeProperty h t) (SObject m) =
    case (get t m, get h m, t == h) of
        (Just p, Just (hr, SObject hm), False) =>
            case get t hm of
                Nothing =>
                    let
                        hm = insert t p hm
                        m = delete t m
                        m = insert h (hr, SObject hm) m
                    in Just (SObject m)
                _ => Nothing
        _ => Nothing
applyLensSchema (PlungeProperty _ _) _ = Nothing
applyLensSchema WrapProperty schema = Just (SArray False schema)
applyLensSchema HeadProperty (SArray False schema) = Just schema
applyLensSchema HeadProperty _ = Nothing
applyLensSchema (LensIn key lens) (SObject smap) =
    case get key smap of
        Just (required, schema) =>
            case applyLensSchema lens schema of
                Just schema => Just (SObject (insert key (required, schema) smap))
                Nothing => Nothing
        Nothing => Nothing
applyLensSchema (LensIn _ _) _ = Nothing
applyLensSchema (LensMap lens) (SArray allowEmpty schema) =
    case applyLensSchema lens schema of
        Just schema' => Just (SArray allowEmpty schema')
        Nothing => Nothing
applyLensSchema (LensMap _) _ = Nothing
applyLensSchema (Require key r) (SObject smap) =
    case get key smap of
        Just (required, schema) =>
            if r == not required
            then Just (SObject (insert key (r, schema) smap))
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
applyLensSchema (Convert a b map) s with (convertIsValid a b map)
    applyLensSchema (Convert KBoolean b m) (SBoolean d) | True with (convertDefault (Boolean d) m)
        applyLensSchema (Convert KBoolean KBoolean _) (SBoolean d) | True | Just (Boolean d') = Just (SBoolean d')
        applyLensSchema (Convert KBoolean KNumber _) (SBoolean d) | True | Just (Number d') = Just (SNumber d')
        applyLensSchema (Convert KBoolean KText _) (SBoolean d) | True | Just (Text d') = Just (SText d')
        applyLensSchema (Convert KBoolean _ _) (SBoolean _) | True | _ = Nothing
    applyLensSchema (Convert KNumber b m) (SNumber d) | True with (convertDefault (Number d) m)
        applyLensSchema (Convert KNumber KBoolean _) (SNumber d) | True | Just (Boolean d') = Just (SBoolean d')
        applyLensSchema (Convert KNumber KNumber _) (SNumber d) | True | Just (Number d') = Just (SNumber d')
        applyLensSchema (Convert KNumber KText _) (SNumber d) | True | Just (Text d') = Just (SText d')
        applyLensSchema (Convert KNumber _ _) (SNumber _) | True | _ = Nothing
    applyLensSchema (Convert KText b m) (SText d) | True with (convertDefault (Text d) m)
        applyLensSchema (Convert KText KBoolean _) (SText d) | True | Just (Boolean d') = Just (SBoolean d')
        applyLensSchema (Convert KText KNumber _) (SText d) | True | Just (Number d') = Just (SNumber d')
        applyLensSchema (Convert KText KText _) (SText d) | True | Just (Text d') = Just (SText d')
        applyLensSchema (Convert KText _ _) (SText _) | True | _ = Nothing
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

convertIsValidAfterReverse : (a, b : PrimitiveKind) -> (m : List (PrimitiveValue, PrimitiveValue)) ->
    convertIsValid a b m = True -> convertIsValid b a (map (\(a, b) => (b, a)) m) = True
convertIsValidAfterReverse a b [] prf = Refl
convertIsValidAfterReverse a b ((x, y) :: xs) prf = ?convertIsValidAfterReverse_rhs_6

convertDefaultAfterReverse : (d, d' : PrimitiveValue) -> (m : List (PrimitiveValue, PrimitiveValue)) ->
    convertDefault d m = Just d' -> convertDefault d' (map (\(a, b) => (b, a)) m) = Just d
convertDefaultAfterReverse (Boolean x) (Boolean y) prf = ?convertDefaultAfterReverse_rhs_4
convertDefaultAfterReverse (Boolean x) (Number k) prf = ?convertDefaultAfterReverse_rhs_5
convertDefaultAfterReverse (Boolean x) (Text y) prf = ?convertDefaultAfterReverse_rhs_6
convertDefaultAfterReverse (Number k) d' prf = ?convertDefaultAfterReverse_rhs_2
convertDefaultAfterReverse (Text x) d' prf = ?convertDefaultAfterReverse_rhs_3

||| Forwards and backwards compatibility requires schema transformations to be reversible
assertReverseSchema :
    (lens: Lens) ->
    (schema: Schema) ->
    (IsJust (applyLensSchema lens schema)) ->
    (reverseSchema lens schema = Just schema)
{-assertReverseSchema (Make (KPrimitive KBoolean)) SFalse _ = Refl
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
assertReverseSchema (Destroy KObject) (SObject m) prf with (isEmpty m)
    assertReverseSchema (Destroy KObject) (SObject _) prf | False = absurd $ prf
    assertReverseSchema (Destroy KObject) (SObject m) prf | True = ?goodEnoughToConvinceMe
assertReverseSchema (AddProperty _) SFalse ItIsJust impossible
assertReverseSchema (AddProperty _) (SBoolean _) ItIsJust impossible
assertReverseSchema (AddProperty _) (SNumber _) ItIsJust impossible
assertReverseSchema (AddProperty _) (SText _) ItIsJust impossible
assertReverseSchema (AddProperty _) (SArray _ _) ItIsJust impossible
assertReverseSchema (AddProperty key) (SObject map) prf with (get key map) proof prf1
    assertReverseSchema (AddProperty key) (SObject map) _ | Nothing =
        rewrite update_eq map key (Just (False, SFalse)) in
            rewrite update_shadow map key (Just (False, SFalse)) Nothing in
                rewrite update_same map key Nothing prf1 in Refl
    assertReverseSchema (AddProperty _) (SObject _) prf | (Just _) = absurd $ prf
assertReverseSchema (RemoveProperty _) SFalse ItIsJust impossible
assertReverseSchema (RemoveProperty _) (SBoolean _) ItIsJust impossible
assertReverseSchema (RemoveProperty _) (SNumber _) ItIsJust impossible
assertReverseSchema (RemoveProperty _) (SText _) ItIsJust impossible
assertReverseSchema (RemoveProperty _) (SArray _ _) ItIsJust impossible
assertReverseSchema (RemoveProperty key) (SObject map) prf with (get key map) proof prf1
    assertReverseSchema (RemoveProperty key) (SObject map) prf | Nothing = absurd $ prf
    assertReverseSchema (RemoveProperty key) (SObject map) ItIsJust | (Just (False, SFalse)) =
        rewrite update_eq map key Nothing in
            rewrite update_shadow map key Nothing (Just (False, SFalse)) in
                rewrite update_same map key (Just (False, SFalse)) prf1 in Refl
    assertReverseSchema (RemoveProperty key) (SObject map) prf | (Just (False, (SBoolean _))) = absurd $ prf
    assertReverseSchema (RemoveProperty key) (SObject map) prf | (Just (False, (SNumber _))) = absurd $ prf
    assertReverseSchema (RemoveProperty key) (SObject map) prf | (Just (False, (SText _))) = absurd $ prf
    assertReverseSchema (RemoveProperty key) (SObject map) prf | (Just (False, (SArray _ _))) = absurd $ prf
    assertReverseSchema (RemoveProperty key) (SObject map) prf | (Just (False, (SObject _))) = absurd $ prf
    assertReverseSchema (RemoveProperty key) (SObject map) prf | (Just (True, _)) = absurd $ prf
assertReverseSchema (RenameProperty _ _) SFalse ItIsJust impossible
assertReverseSchema (RenameProperty _ _) (SBoolean _) ItIsJust impossible
assertReverseSchema (RenameProperty _ _) (SNumber _) ItIsJust impossible
assertReverseSchema (RenameProperty _ _) (SText _) ItIsJust impossible
assertReverseSchema (RenameProperty _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (RenameProperty a b) (SObject map) prf with (get a map, get b map) proof prf1
    assertReverseSchema (RenameProperty _ _) (SObject map) prf | (Nothing, _) = absurd $ prf
    assertReverseSchema (RenameProperty a b) (SObject map) x | ((Just y), Nothing) =
        rewrite update_eq (update a Nothing map) b (Just y)
        in let
            va = cong fst prf1
            vb = cong snd prf1
            not_a_eq_b = get_neq (tuple_eq prf1 uninhabited)
            not_b_eq_a = \p => not_a_eq_b (sym p)
        in rewrite update_permute map b a (Just y) Nothing not_b_eq_a
        in rewrite update_eq (update b (Just y) map) a Nothing
        in rewrite update_permute map a b Nothing (Just y) not_a_eq_b
        in rewrite update_shadow (update a Nothing map) b (Just y) Nothing
        in rewrite update_permute map b a Nothing Nothing not_b_eq_a
        in rewrite update_same map b Nothing vb
        in rewrite update_shadow map a Nothing (Just y)
        in rewrite update_same map a (Just y) va in Refl
    assertReverseSchema (RenameProperty _ _) (SObject _) prf | ((Just _), (Just _)) = absurd $ prf
assertReverseSchema (HoistProperty _ _) SFalse ItIsJust impossible
assertReverseSchema (HoistProperty _ _) (SBoolean _) ItIsJust impossible
assertReverseSchema (HoistProperty _ _) (SNumber _) ItIsJust impossible
assertReverseSchema (HoistProperty _ _) (SText _) ItIsJust impossible
assertReverseSchema (HoistProperty _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (HoistProperty h t) (SObject hm) prf with (get h hm, get t hm) proof prf1
    assertReverseSchema (HoistProperty _ _) (SObject _) prf | (Nothing, _) = absurd $ prf
    assertReverseSchema (HoistProperty _ _) (SObject _) prf | ((Just (_, SFalse)), (Just _)) = absurd $ prf
    assertReverseSchema (HoistProperty _ _) (SObject _) prf | ((Just (_, (SBoolean _))), (Just _)) = absurd $ prf
    assertReverseSchema (HoistProperty _ _) (SObject _) prf | ((Just (_, (SNumber _))), (Just _)) = absurd $ prf
    assertReverseSchema (HoistProperty _ _) (SObject _) prf | ((Just (_, (SText _))), (Just _)) = absurd $ prf
    assertReverseSchema (HoistProperty _ _) (SObject _) prf | ((Just (_, (SArray _ _))), (Just _)) = absurd $ prf
    assertReverseSchema (HoistProperty _ _) (SObject _) prf | ((Just (_, (SObject _))), (Just _)) = absurd $ prf
    assertReverseSchema (HoistProperty _ _) (SObject _) prf | ((Just (_, SFalse)), Nothing) = absurd $ prf
    assertReverseSchema (HoistProperty _ _) (SObject _) prf | ((Just (_, (SBoolean _))), Nothing) = absurd $ prf
    assertReverseSchema (HoistProperty _ _) (SObject _) prf | ((Just (_, (SNumber _))), Nothing) = absurd $ prf
    assertReverseSchema (HoistProperty _ _) (SObject _) prf | ((Just (_, (SText _))), Nothing) = absurd $ prf
    assertReverseSchema (HoistProperty _ _) (SObject _) prf | ((Just (_, (SArray _ _))), Nothing) = absurd $ prf
    assertReverseSchema (HoistProperty h t) (SObject hm) prf | ((Just (r, (SObject tm))), Nothing) with (get t tm) proof prf2
        assertReverseSchema (HoistProperty _ _) (SObject _) prf | ((Just (_, (SObject _))), Nothing) | Nothing = absurd $ prf
        assertReverseSchema (HoistProperty h t) (SObject hm) prf | ((Just (r, (SObject tm))), Nothing) | (Just x) =
            let neq_ht = get_neq (tuple_eq prf1 uninhabited)
                neq_th = \p => neq_ht $ sym p
                bne_th = ne_key t h neq_th
            in rewrite update_permute hm h t (Just (r, (SObject (update t Nothing tm)))) (Just x) neq_ht
            in rewrite update_eq (update h (Just (r, SObject (update t Nothing tm))) hm) t (Just x)
            in rewrite update_permute hm t h (Just x) (Just (r, SObject (update t Nothing tm))) neq_th
            in rewrite update_eq (update t (Just x) hm) h (Just (r, SObject (update t Nothing tm)))
            in rewrite bne_th
            in rewrite update_eq tm t Nothing
            in rewrite update_shadow tm t Nothing (Just x)
            in rewrite update_permute (update t (Just x) hm) t h Nothing (Just (r, SObject (update t Nothing tm))) neq_th
            in rewrite update_shadow hm t (Just x) Nothing
            in rewrite update_shadow (update t Nothing hm) h
                (Just (r, SObject (update t Nothing tm)))
                (Just (r, SObject (update t (Just x) tm)))
            in rewrite update_same hm t Nothing (cong snd prf1)
            in rewrite update_same tm t (Just x) prf2
            in rewrite update_same hm h (Just (r, SObject tm)) (cong fst prf1)
            in Refl
assertReverseSchema (PlungeProperty _ _) SFalse ItIsJust impossible
assertReverseSchema (PlungeProperty _ _) (SBoolean _) ItIsJust impossible
assertReverseSchema (PlungeProperty _ _) (SNumber _) ItIsJust impossible
assertReverseSchema (PlungeProperty _ _) (SText _) ItIsJust impossible
assertReverseSchema (PlungeProperty _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (PlungeProperty h t) (SObject m) prf with (get t m, get h m, t == h) proof prf1
    assertReverseSchema (PlungeProperty _ _) (SObject _) prf | (Nothing, _, _) = absurd $ prf
    assertReverseSchema (PlungeProperty _ _) (SObject _) prf | ((Just _), Nothing, _) = absurd $ prf
    assertReverseSchema (PlungeProperty _ _) (SObject _) prf | ((Just _), (Just (_, SFalse)), _) = absurd $ prf
    assertReverseSchema (PlungeProperty _ _) (SObject _) prf | ((Just _), (Just (_, (SBoolean _))), _) = absurd $ prf
    assertReverseSchema (PlungeProperty _ _) (SObject _) prf | ((Just _), (Just (_, (SNumber _))), _) = absurd $ prf
    assertReverseSchema (PlungeProperty _ _) (SObject _) prf | ((Just _), (Just (_, (SText _))), _) = absurd $ prf
    assertReverseSchema (PlungeProperty _ _) (SObject _) prf | ((Just _), (Just (_, (SArray _ _))), _) = absurd $ prf
    assertReverseSchema (PlungeProperty _ _) (SObject _) prf | ((Just _), (Just (_, (SObject _))), True) = absurd $ prf
    assertReverseSchema (PlungeProperty h t) (SObject m) prf | ((Just tv), (Just (hr, (SObject hm))), False) with (get t hm) proof prf2
        assertReverseSchema (PlungeProperty _ _) (SObject _) prf | ((Just _), (Just (_, (SObject _))), False) | (Just _) = absurd $ prf
        assertReverseSchema (PlungeProperty h t) (SObject m) prf | ((Just tv), (Just (hr, (SObject hm))), False) | Nothing =
            let neq_th = bne_key t h $ cong snd $ cong snd $ prf1
                neq_ht = \p => neq_th $ sym p
            in rewrite update_eq (update t Nothing m) h (Just (hr, SObject (update t (Just tv) hm)))
            in rewrite update_permute m h t (Just (hr, SObject (update t (Just tv) hm))) Nothing neq_ht
            in rewrite update_eq (update h (Just (hr, SObject (update t (Just tv) hm))) m) t Nothing
            in rewrite update_eq hm t (Just tv)
            in rewrite update_shadow hm t (Just tv) Nothing
            in rewrite update_shadow (update h (Just (hr, SObject (update t (Just tv) hm))) m) t Nothing (Just tv)
            in rewrite update_permute m t h (Just tv) (Just (hr, SObject (update t (Just tv) hm))) neq_th
            in rewrite update_same m t (Just tv) (cong fst prf1)
            in rewrite update_shadow m h (Just (hr, SObject (update t (Just tv) hm))) (Just (hr, SObject (update t Nothing hm)))
            in rewrite update_same hm t Nothing prf2
            in rewrite update_same m h (Just (hr, SObject hm)) (cong fst $ cong snd prf1)
            in Refl
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
assertReverseSchema (LensIn _ _) SFalse ItIsJust impossible
assertReverseSchema (LensIn _ _) (SBoolean _) ItIsJust impossible
assertReverseSchema (LensIn _ _) (SNumber _) ItIsJust impossible
assertReverseSchema (LensIn _ _) (SText _) ItIsJust impossible
assertReverseSchema (LensIn _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (LensIn k l) (SObject m) prf with (get k m) proof prf1
    assertReverseSchema (LensIn _ _) (SObject _) prf | Nothing = absurd $ prf
    assertReverseSchema (LensIn k l) (SObject m) prf | (Just (r, s)) with (applyLensSchema l s) proof prf2
        assertReverseSchema (LensIn _ _) (SObject _) prf | (Just (_, _)) | Nothing = absurd $ prf
        assertReverseSchema (LensIn k l) (SObject m) prf | (Just (r, s)) | (Just s') =
            rewrite update_eq m k (Just (r, s'))
            in let
                ij = it_is_just (applyLensSchema l s) prf2
                ind = assertReverseSchema (reverseLens l) s'
            in ?hole
            -- rewrite ind in ?assertReverseSchema_rhs_26
assertReverseSchema (LensMap _) SFalse ItIsJust impossible
assertReverseSchema (LensMap _) (SBoolean _) ItIsJust impossible
assertReverseSchema (LensMap _) (SNumber _) ItIsJust impossible
assertReverseSchema (LensMap _) (SText _) ItIsJust impossible
assertReverseSchema (LensMap l) (SArray e s) prf with (applyLensSchema l s) proof prf1
    assertReverseSchema (LensMap _) (SArray _ _) prf | Nothing = absurd $ prf
    assertReverseSchema (LensMap l) (SArray e s) prf | (Just s') with (applyLensSchema (reverseLens l) s') proof prf2
        assertReverseSchema (LensMap l) (SArray e s) prf | (Just s') | Nothing =
            let
                ij = it_is_just (applyLensSchema l s) prf1
                ind = assertReverseSchema l s ij
            in void $ ?reverseLensMap
        assertReverseSchema (LensMap l) (SArray e s) prf | (Just s') | (Just s'') =
            let
                ij = it_is_just (applyLensSchema l s) prf1
                ind = assertReverseSchema l s ij
            in ?h_2
assertReverseSchema (LensMap _) (SObject _) ItIsJust impossible
assertReverseSchema (Require _ _) SFalse ItIsJust impossible
assertReverseSchema (Require _ _) (SBoolean _) ItIsJust impossible
assertReverseSchema (Require _ _) (SNumber _) ItIsJust impossible
assertReverseSchema (Require _ _) (SText _) ItIsJust impossible
assertReverseSchema (Require _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (Require k r) (SObject m) prf with (get k m) proof prf1
    assertReverseSchema (Require _ _) (SObject _) prf | Nothing = absurd $ prf
    assertReverseSchema (Require k r) (SObject m) prf | (Just (r2, y)) with (r == (not r2)) proof prf2
        assertReverseSchema (Require _ _) (SObject _) prf | (Just (_, _)) | False = absurd $ prf
        assertReverseSchema (Require k r) (SObject m) prf | (Just (r2, y)) | True =
            rewrite update_eq m k (Just (r, y))
            in rewrite beq_bool (not r)
            in rewrite update_shadow m k (Just (r, y)) (Just (not r, y))
            in rewrite sym $ inv_bool r r2 $ eq_bool r (not r2) prf2
            in rewrite update_same m k (Just (r2, y)) prf1
            in Refl
assertReverseSchema (Default (Boolean _) (Boolean _)) SFalse ItIsJust impossible
assertReverseSchema (Default (Boolean b) (Boolean b')) (SBoolean b2) prf with (b == b2) proof prf1
    assertReverseSchema (Default (Boolean _) (Boolean _)) (SBoolean _) prf | False = absurd $ prf
    assertReverseSchema (Default (Boolean b) (Boolean b')) (SBoolean b2) prf | True =
        rewrite beq_bool b' in
        rewrite eq_bool b b2 prf1 in Refl
assertReverseSchema (Default (Boolean _) (Boolean _)) (SNumber _) ItIsJust impossible
assertReverseSchema (Default (Boolean _) (Boolean _)) (SText _) ItIsJust impossible
assertReverseSchema (Default (Boolean _) (Boolean _)) (SArray _ _) ItIsJust impossible
assertReverseSchema (Default (Boolean _) (Boolean _)) (SObject _) ItIsJust impossible
assertReverseSchema (Default (Boolean _) (Number _)) _ ItIsJust impossible
assertReverseSchema (Default (Boolean _) (Text _)) _ ItIsJust impossible
assertReverseSchema (Default (Number _) (Boolean _)) _ ItIsJust impossible
assertReverseSchema (Default (Number _) (Number _)) SFalse ItIsJust impossible
assertReverseSchema (Default (Number _) (Number _)) (SBoolean _) ItIsJust impossible
assertReverseSchema (Default (Number n) (Number n')) (SNumber n2) prf with (n == n2) proof prf1
    assertReverseSchema (Default (Number _) (Number _)) (SNumber _) prf | False = absurd $ prf
    assertReverseSchema (Default (Number n) (Number n')) (SNumber n2) prf | True =
        rewrite beq_nat n' in
        rewrite beq_implies_eq_nat n n2 prf1 in Refl
assertReverseSchema (Default (Number _) (Number _)) (SText _) ItIsJust impossible
assertReverseSchema (Default (Number _) (Number _)) (SArray _ _) ItIsJust impossible
assertReverseSchema (Default (Number _) (Number _)) (SObject _) ItIsJust impossible
assertReverseSchema (Default (Number _) (Text _)) _ ItIsJust impossible
assertReverseSchema (Default (Text _) (Boolean _)) _ ItIsJust impossible
assertReverseSchema (Default (Text _) (Number _)) _ ItIsJust impossible
assertReverseSchema (Default (Text _) (Text _)) SFalse ItIsJust impossible
assertReverseSchema (Default (Text _) (Text _)) (SBoolean _) ItIsJust impossible
assertReverseSchema (Default (Text _) (Text _)) (SNumber _) ItIsJust impossible
assertReverseSchema (Default (Text t) (Text t')) (SText t2) prf with (t == t2) proof prf1
    assertReverseSchema (Default (Text t) (Text t')) (SText t2) prf | False = absurd $ prf
    assertReverseSchema (Default (Text t) (Text t')) (SText t2) prf | True =
        rewrite beq_str t' in
        rewrite eq_str t t2 prf1 in Refl
assertReverseSchema (Default (Text _) (Text _)) (SArray _ _) ItIsJust impossible
assertReverseSchema (Default (Text _) (Text _)) (SObject _) ItIsJust impossible-}
assertReverseSchema (Convert a b m) s prf with (convertIsValid a b m) proof prf1
    assertReverseSchema (Convert KBoolean _ _) _ prf | False = absurd $ prf
    assertReverseSchema (Convert KNumber _ _) _ prf | False = absurd $ prf
    assertReverseSchema (Convert KText _ _) _ prf | False = absurd $ prf
    assertReverseSchema (Convert KBoolean _ _) SFalse prf | True = absurd $ prf
    assertReverseSchema (Convert KBoolean b m) (SBoolean d) prf | True with (convertDefault (Boolean d) m) proof prf2
        assertReverseSchema (Convert KBoolean b m) (SBoolean d) prf | True | Nothing = absurd $ prf
        assertReverseSchema (Convert KBoolean KBoolean m) (SBoolean d) prf | True | (Just (Boolean d')) =
            rewrite convertIsValidAfterReverse KBoolean KBoolean m prf1
            in rewrite convertDefaultAfterReverse (Boolean d) (Boolean d') m prf2 in Refl
        assertReverseSchema (Convert KBoolean KBoolean _) (SBoolean _) prf | True | (Just (Number _)) = absurd $ prf
        assertReverseSchema (Convert KBoolean KBoolean _) (SBoolean _) prf | True | (Just (Text _)) = absurd $ prf
        assertReverseSchema (Convert KBoolean KNumber _) (SBoolean _) prf | True | (Just (Boolean _)) = absurd $ prf
        assertReverseSchema (Convert KBoolean KNumber m) (SBoolean d) prf | True | (Just (Number d')) =
            rewrite convertIsValidAfterReverse KBoolean KNumber m prf1
            in rewrite convertDefaultAfterReverse (Boolean d) (Number d') m prf2 in Refl
        assertReverseSchema (Convert KBoolean KNumber _) (SBoolean _) prf | True | (Just (Text _)) = absurd $ prf
        assertReverseSchema (Convert KBoolean KText _) (SBoolean _) prf | True | (Just (Boolean _)) = absurd $ prf
        assertReverseSchema (Convert KBoolean KText _) (SBoolean _) prf | True | (Just (Number _)) = absurd $ prf
        assertReverseSchema (Convert KBoolean KText m) (SBoolean d) prf | True | (Just (Text d')) =
            rewrite convertIsValidAfterReverse KBoolean KText m prf1
            in rewrite convertDefaultAfterReverse (Boolean d) (Text d') m prf2 in Refl
    assertReverseSchema (Convert KBoolean _ _) (SNumber _) prf | True = absurd $ prf
    assertReverseSchema (Convert KBoolean _ _) (SText _) prf | True = absurd $ prf
    assertReverseSchema (Convert KBoolean _ _) (SArray _ _) prf | True = absurd $ prf
    assertReverseSchema (Convert KBoolean _ _) (SObject _) prf | True = absurd $ prf
    assertReverseSchema (Convert KNumber _ _) SFalse prf | True = absurd $ prf
    assertReverseSchema (Convert KNumber _ _) (SBoolean _) prf | True = absurd $ prf
    assertReverseSchema (Convert KNumber b m) (SNumber d) prf | True with (convertDefault (Number d) m) proof prf2
        assertReverseSchema (Convert KNumber _ _) (SNumber _) prf | True | Nothing = absurd $ prf
        assertReverseSchema (Convert KNumber KBoolean m) (SNumber d) prf | True | (Just (Boolean d')) =
            rewrite convertIsValidAfterReverse KNumber KBoolean m prf1
            in rewrite convertDefaultAfterReverse (Number d) (Boolean d') m prf2 in Refl
        assertReverseSchema (Convert KNumber KBoolean _) (SNumber _) prf | True | (Just (Number _)) = absurd $ prf
        assertReverseSchema (Convert KNumber KBoolean _) (SNumber _) prf | True | (Just (Text _)) = absurd $ prf
        assertReverseSchema (Convert KNumber KNumber _) (SNumber _) prf | True | (Just (Boolean _)) = absurd $ prf
        assertReverseSchema (Convert KNumber KNumber m) (SNumber d) prf | True | (Just (Number d')) =
            rewrite convertIsValidAfterReverse KNumber KNumber m prf1
            in rewrite convertDefaultAfterReverse (Number d) (Number d') m prf2 in Refl
        assertReverseSchema (Convert KNumber KNumber _) (SNumber _) prf | True | (Just (Text _)) = absurd $ prf
        assertReverseSchema (Convert KNumber KText _) (SNumber _) prf | True | (Just (Boolean _)) = absurd $ prf
        assertReverseSchema (Convert KNumber KText _) (SNumber _) prf | True | (Just (Number _)) = absurd $ prf
        assertReverseSchema (Convert KNumber KText m) (SNumber d) prf | True | (Just (Text d')) =
            rewrite convertIsValidAfterReverse KNumber KText m prf1
            in rewrite convertDefaultAfterReverse (Number d) (Text d') m prf2 in Refl
    assertReverseSchema (Convert KNumber _ _) (SText _) prf | True = absurd $ prf
    assertReverseSchema (Convert KNumber _ _) (SArray _ _) prf | True = absurd $ prf
    assertReverseSchema (Convert KNumber _ _) (SObject _) prf | True = absurd $ prf
    assertReverseSchema (Convert KText _ _) SFalse prf | True = absurd $ prf
    assertReverseSchema (Convert KText _ _) (SBoolean _) prf | True = absurd $ prf
    assertReverseSchema (Convert KText _ _) (SNumber _) prf | True = absurd $ prf
    assertReverseSchema (Convert KText b m) (SText d) prf | True with (convertDefault (Text d) m) proof prf2
        assertReverseSchema (Convert KText _ _) (SText _) prf | True | Nothing = absurd $ prf
        assertReverseSchema (Convert KText KBoolean m) (SText d) prf | True | (Just (Boolean d')) =
            rewrite convertIsValidAfterReverse KText KBoolean m prf1
            in rewrite convertDefaultAfterReverse (Text d) (Boolean d') m prf2 in Refl
        assertReverseSchema (Convert KText KBoolean _) (SText _) prf | True | (Just (Number _)) = absurd $ prf
        assertReverseSchema (Convert KText KBoolean _) (SText _) prf | True | (Just (Text _)) = absurd $ prf
        assertReverseSchema (Convert KText KNumber _) (SText _) prf | True | (Just (Boolean _)) = absurd $ prf
        assertReverseSchema (Convert KText KNumber m) (SText d) prf | True | (Just (Number d')) =
            rewrite convertIsValidAfterReverse KText KNumber m prf1
            in rewrite convertDefaultAfterReverse (Text d) (Number d') m prf2 in Refl
        assertReverseSchema (Convert KText KNumber _) (SText _) prf | True | (Just (Text _)) = absurd $ prf
        assertReverseSchema (Convert KText KText _) (SText _) prf | True | (Just (Boolean _)) = absurd $ prf
        assertReverseSchema (Convert KText KText _) (SText _) prf | True | (Just (Number _)) = absurd $ prf
        assertReverseSchema (Convert KText KText m) (SText d) prf | True | (Just (Text d')) =
            rewrite convertIsValidAfterReverse KText KText m prf1
            in rewrite convertDefaultAfterReverse (Text d) (Text d') m prf2 in Refl
    assertReverseSchema (Convert KText _ _) (SArray _ _) prf | True = absurd $ prf
    assertReverseSchema (Convert KText _ _) (SObject _) prf | True = absurd $ prf
assertReverseSchema _ _ _ = ?todo
