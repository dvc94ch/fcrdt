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
applyLensSchema (Make KObject) SFalse = Just (SObject empty)
applyLensSchema (Make _) _ = Nothing
applyLensSchema (Destroy (KPrimitive KBoolean)) (SBoolean False) = Just SFalse
applyLensSchema (Destroy (KPrimitive KNumber)) (SNumber 0) = Just SFalse
applyLensSchema (Destroy (KPrimitive KText)) (SText []) = Just SFalse
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
applyLensSchema (HoistProperty host target) (SObject smap) =
    case get host smap of
        Just (required, SObject host_smap) =>
            (case get target host_smap of
                Just p =>
                    let
                        host_smap = delete target host_smap
                        smap = insert host (required, SObject host_smap) smap
                        smap = insert target p smap
                     in Just (SObject smap)
                Nothing => Nothing)
        _ => Nothing
applyLensSchema (HoistProperty _ _) _ = Nothing
applyLensSchema (PlungeProperty host target) (SObject smap) =
    case (get target smap, get host smap) of
        (Just (required, schema), Nothing) =>
            let
                host_smap = insert target (required, schema) empty
                smap = delete target smap
                smap = insert host (required, SObject host_smap) smap
            in Just (SObject smap)
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
    map (SArray allowEmpty) (applyLensSchema lens schema)
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
assertReverseSchema (LensIn _ _) SFalse ItIsJust impossible
assertReverseSchema (LensIn _ _) (SBoolean _) ItIsJust impossible
assertReverseSchema (LensIn _ _) (SNumber _) ItIsJust impossible
assertReverseSchema (LensIn _ _) (SText _) ItIsJust impossible
assertReverseSchema (LensIn _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (LensIn key lens) (SObject map) prf with (get key map)
    assertReverseSchema (LensIn key lens) (SObject map) prf | Nothing = absurd $ prf
    assertReverseSchema (LensIn key lens) (SObject map) prf | (Just (x, y)) with (applyLensSchema lens y) proof prf1
        assertReverseSchema (LensIn key lens) (SObject map) prf | (Just (x, y)) | Nothing = absurd $ prf
        assertReverseSchema (LensIn key lens) (SObject map) prf | (Just (x, y)) | (Just z) =
            rewrite update_eq map key (Just (x, z))
            in let
                ij = it_is_just (applyLensSchema lens y) prf1
                ind = assertReverseSchema lens y ij
            in ?hole
            -- rewrite ind in ?assertReverseSchema_rhs_26
assertReverseSchema (LensMap _) SFalse ItIsJust impossible
assertReverseSchema (LensMap _) (SBoolean _) ItIsJust impossible
assertReverseSchema (LensMap _) (SNumber _) ItIsJust impossible
assertReverseSchema (LensMap _) (SText _) ItIsJust impossible
assertReverseSchema (LensMap lens) (SArray y z) x = ?assertReverseSchema_rhs_20
assertReverseSchema (LensMap _) (SObject _) ItIsJust impossible
assertReverseSchema (Require _ _) SFalse ItIsJust impossible
assertReverseSchema (Require _ _) (SBoolean _) ItIsJust impossible
assertReverseSchema (Require _ _) (SNumber _) ItIsJust impossible
assertReverseSchema (Require _ _) (SText _) ItIsJust impossible
assertReverseSchema (Require _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (Require key val) (SObject map) x = ?assertReverseSchema_rhs_22
assertReverseSchema (Default v1 v2) SFalse x = ?assertReverseSchema_rhs_16
assertReverseSchema (Default v1 v2) (SBoolean y) x = ?assertReverseSchema_rhs_17
assertReverseSchema (Default v1 v2) (SNumber k) x = ?assertReverseSchema_rhs_18
assertReverseSchema (Default v1 v2) (SText xs) x = ?assertReverseSchema_rhs_19
assertReverseSchema (Default v1 v2) (SArray y z) x = ?assertReverseSchema_rhs_21
assertReverseSchema (Default v1 v2) (SObject map) x = ?assertReverseSchema_rhs_23
assertReverseSchema (Convert k1 k2 xs) SFalse x = ?assertReverseSchema_rhs_26
assertReverseSchema (Convert k1 k2 xs) (SBoolean y) x = ?assertReverseSchema_rhs_27
assertReverseSchema (Convert k1 k2 xs) (SNumber k) x = ?assertReverseSchema_rhs_28
assertReverseSchema (Convert k1 k2 xs) (SText ys) x = ?assertReverseSchema_rhs_29
assertReverseSchema (Convert k1 k2 xs) (SArray y z) x = ?assertReverseSchema_rhs_30
assertReverseSchema (Convert k1 k2 xs) (SObject map) x = ?assertReverseSchema_rhs_31
