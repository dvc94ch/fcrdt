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

Uninhabited (a = b) => Uninhabited (Boolean a = Boolean b) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl

Uninhabited (Boolean a = Number b) where
    uninhabited Refl impossible

Uninhabited (Boolean a = Text b) where
    uninhabited Refl impossible

Uninhabited (a = b) => Uninhabited (Number a = Number b) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl

Uninhabited (Number a = Boolean b) where
    uninhabited Refl impossible

Uninhabited (Number a = Text b) where
    uninhabited Refl impossible

Uninhabited (a = b) => Uninhabited (Text a = Text b) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl

Uninhabited (Text a = Boolean b) where
    uninhabited Refl impossible

Uninhabited (Text a = Number b) where
    uninhabited Refl impossible

boolean : (v : PrimitiveValue) -> Maybe Bool
boolean (Boolean b) = Just b
boolean _ = Nothing

number : (v : PrimitiveValue) -> Maybe Nat
number (Number n) = Just n
number _ = Nothing

text : (v : PrimitiveValue) -> Maybe (List Char)
text (Text t) = Just t
text _ = Nothing

beq_prim : (v : PrimitiveValue) ->  v == v = True
beq_prim (Boolean b) = beq_bool b
beq_prim (Number n) = beq_nat n
beq_prim (Text t) = beq_str t

beq_prim2 : (v1, v2 : PrimitiveValue) -> (v1 == v2 = True) -> v1 = v2
beq_prim2 (Boolean x) (Boolean y) prf = rewrite eq_bool x y prf in Refl
beq_prim2 (Boolean _) (Number _) Refl impossible
beq_prim2 (Boolean _) (Text _) Refl impossible
beq_prim2 (Number _) (Boolean _) Refl impossible
beq_prim2 (Number k) (Number j) prf = rewrite eq_nat k j prf in Refl
beq_prim2 (Number _) (Text _) Refl impossible
beq_prim2 (Text _) (Boolean _) Refl impossible
beq_prim2 (Text _) (Number _) Refl impossible
beq_prim2 (Text xs) (Text ys) prf = rewrite eq_str xs ys prf in Refl

neq_prim : (v1, v2 : PrimitiveValue) -> (v1 == v2 = False) -> Not (v1 = v2)
neq_prim (Boolean x) (Boolean y) prf =
    neq_bool x y prf . justInjective . cong boolean
neq_prim (Boolean x) (Number k) prf = uninhabited
neq_prim (Boolean x) (Text xs) prf = uninhabited
neq_prim (Number k) (Boolean x) prf = uninhabited
neq_prim (Number k) (Number j) prf =
    neq_nat k j prf . justInjective . cong number
neq_prim (Number k) (Text xs) prf = uninhabited
neq_prim (Text xs) (Boolean x) prf = uninhabited
neq_prim (Text xs) (Number k) prf = uninhabited
neq_prim (Text xs) (Text ys) prf =
    neq_str xs ys prf . justInjective . cong text

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
      Null
    | Primitive PrimitiveValue
    | Array (List Value)
    | Object (Map Value)

%name Value val, v, v1, v2

Eq Value where
    Null == Null = True
    Primitive v1 == Primitive v2 = v1 == v2
    Array vs1 == Array vs2 = assert_total (vs1 == vs2)
    Object ps1 == Object ps2 = assert_total (ps1 == ps2)
    _ == _ = False

Uninhabited (Null = Primitive _) where
    uninhabited Refl impossible

Uninhabited (Null = Array _) where
    uninhabited Refl impossible

Uninhabited (Null = Object _) where
    uninhabited Refl impossible

Uninhabited (Primitive _ = Null) where
    uninhabited Refl impossible

Uninhabited (a = b) => Uninhabited (Primitive a = Primitive b) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl

Uninhabited (Primitive _ = Array _) where
    uninhabited Refl impossible

Uninhabited (Primitive _ = Object _) where
    uninhabited Refl impossible

Uninhabited (Array _ = Null) where
    uninhabited Refl impossible

Uninhabited (Array _ = Primitive _) where
    uninhabited Refl impossible

Uninhabited (a = b) => Uninhabited (Array a = Array b) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl

Uninhabited (Array _ = Object _) where
    uninhabited Refl impossible

Uninhabited (Object _ = Null) where
    uninhabited Refl impossible

Uninhabited (Object _ = Primitive _) where
    uninhabited Refl impossible

Uninhabited (Object _ = Array _) where
    uninhabited Refl impossible

Uninhabited (a = b) => Uninhabited (Object a = Object b) where
    uninhabited Refl @{ab} = uninhabited @{ab} Refl


data Kind =
      KNull
    | KPrimitive PrimitiveKind
    | KArray
    | KObject

%name Kind k, k1, k2

Eq Kind where
    KNull == KNull = True
    KPrimitive k1 == KPrimitive k2 = k1 == k2
    KArray == KArray = True
    KObject == KObject = True
    _ == _ = False

prim_kind_of : PrimitiveValue -> PrimitiveKind
prim_kind_of (Boolean x) = KBoolean
prim_kind_of (Number x) = KNumber
prim_kind_of (Text x) = KText

data Schema =
      SNull
    | SBoolean
    | SNumber
    | SText
    | SArray Bool Schema
    | SObject (Map Schema)

validate : Schema -> Value -> Bool
validate SNull Null = True
validate SNull _ = False
validate SBoolean (Primitive (Boolean _)) = True
validate SBoolean _ = False
validate SNumber (Primitive (Number _)) = True
validate SNumber _ = False
validate SText (Primitive (Text _)) = True
validate SText _ = False
validate (SArray allowEmpty schema) (Array []) = allowEmpty
validate (SArray _ schema) (Array (x :: xs)) =
    assert_total (validate schema x) && assert_total (validate (SArray True schema) (Array xs))
validate (SArray _ _) _ = False
validate (SObject smap) (Object vmap) =
    all_properties_exist smap vmap && validate_properties vmap smap where
        all_properties_exist : Map Schema -> Map Value -> Bool
        all_properties_exist Empty _ = True
        all_properties_exist (Entry k v m _) vmap with (get k vmap)
            all_properties_exist (Entry k _ m _) vmap | Nothing = False
            all_properties_exist (Entry k _ m _) vmap | Just _ = all_properties_exist m vmap
        validate_properties : Map Value -> Map Schema -> Bool
        validate_properties Empty _ = True
        validate_properties (Entry k v m _) smap with (get k smap)
            validate_properties (Entry _ _ _ _) _ | Nothing = False
            validate_properties (Entry k v m _) smap | Just schema =
                assert_total (validate schema v) && validate_properties m smap
validate (SObject _) _ = False

data Lens =
      Make Kind
    | Destroy Kind
    | AddProperty Key
    | RemoveProperty Key
    | RenameProperty Key Key
    | HoistProperty Key Key
    | PlungeProperty Key Key
    | Wrap
    | Head
    | LensIn Key Lens
    | LensMap Lens
    | Convert PrimitiveKind PrimitiveKind (List (PrimitiveValue, PrimitiveValue))

%name Lens lens, l, l1, l2

Eq Lens where
    Make k1 == Make k2 = k1 == k2
    Destroy k1 == Destroy k2 = k1 == k2
    AddProperty p1 == AddProperty p2 = p1 == p2
    RemoveProperty p1 == RemoveProperty p2 = p1 == p2
    RenameProperty a1 b1 == RenameProperty a2 b2 = a1 == a2 && b1 == b2
    HoistProperty h1 p1 == HoistProperty h2 p2 = h1 == h2 && p1 == p2
    PlungeProperty h1 p1 == PlungeProperty h2 p2 = h1 == h2 && p1 == p2
    Wrap == Wrap = True
    Head == Head = True
    LensIn p1 l1 == LensIn p2 l2 = p1 == p2 && l1 == l2
    LensMap l1 == LensMap l2 = l1 == l2
    Convert k11 k21 f1 == Convert k12 k22 f2 = k11 == k12 && k22 == k22 && f1 == f2
    _ == _ = False


flip_map : List (PrimitiveValue, PrimitiveValue) -> List (PrimitiveValue, PrimitiveValue)
flip_map [] = []
flip_map ((x, y) :: xs) = (y, x) :: (flip_map xs)

flip_map_twice : (m : List (PrimitiveValue, PrimitiveValue)) -> flip_map (flip_map m) = m
flip_map_twice [] = Refl
flip_map_twice ((x, y) :: xs) = rewrite flip_map_twice xs in Refl

validate_map : PrimitiveKind -> PrimitiveKind -> List (PrimitiveValue, PrimitiveValue) -> Bool
validate_map _ _ [] = True
validate_map kx ky ((x, y) :: map) =
    prim_kind_of x == kx && prim_kind_of y == ky && validate_map kx ky map

convert_prim : PrimitiveValue -> List (PrimitiveValue, PrimitiveValue) -> Maybe PrimitiveValue
convert_prim _ [] = Nothing
convert_prim key ((k, v) :: xs) = if key == k then Just v else convert_prim key xs

flip_map_preserves_validity : (a, b : PrimitiveKind) -> (m : List (PrimitiveValue, PrimitiveValue)) ->
    validate_map a b m = True -> validate_map b a (flip_map m) = True
flip_map_preserves_validity a b [] prf = Refl
flip_map_preserves_validity a b ((x, y) :: xs) prf =
    let sprf = and_split (prim_kind_of x == a) (prim_kind_of y == b && Delay (validate_map a b xs)) prf
        sprf2 = and_split (prim_kind_of y == b) (validate_map a b xs) (snd sprf)
        ind = flip_map_preserves_validity a b xs (snd sprf2)
    in rewrite fst sprf2 in rewrite fst sprf in ind

reverse_lens : Lens -> Lens
reverse_lens (Make k) = Destroy k
reverse_lens (Destroy k) = Make k
reverse_lens (AddProperty x) = RemoveProperty x
reverse_lens (RemoveProperty x) = AddProperty x
reverse_lens (RenameProperty x y) = RenameProperty y x
reverse_lens (HoistProperty x y) = PlungeProperty x y
reverse_lens (PlungeProperty x y) = HoistProperty x y
reverse_lens Wrap = Head
reverse_lens Head = Wrap
reverse_lens (LensIn x y) = LensIn x (reverse_lens y)
reverse_lens (LensMap x) = LensMap (reverse_lens x)
reverse_lens (Convert a b m) = Convert b a (flip_map m)

strip_postfix : Eq a => List a -> List a -> (List a, List a)
strip_postfix (a::as) (b::bs) =
    if a == b
    then strip_postfix as bs
    else (a::as, b::bs)
strip_postfix a b = (a, b)

transform_lenses : List Lens -> List Lens -> List Lens
transform_lenses a b =
    let
        a = reverse a
        b = reverse b
        (a, b) = strip_postfix a b
        a = reverse a
        a = map reverse_lens a
    in a ++ b

transform_schema : Lens -> Schema -> Maybe Schema
transform_schema (Make (KPrimitive KBoolean)) SNull = Just SBoolean
transform_schema (Make (KPrimitive KNumber)) SNull = Just SNumber
transform_schema (Make (KPrimitive KText)) SNull = Just SText
transform_schema (Make KArray) SNull = Just (SArray True SNull)
transform_schema (Make KObject) SNull = Just (SObject Empty)
transform_schema (Make _) _ = Nothing
transform_schema (Destroy (KPrimitive KBoolean)) SBoolean = Just SNull
transform_schema (Destroy (KPrimitive KNumber)) SNumber = Just SNull
transform_schema (Destroy (KPrimitive KText)) SText = Just SNull
transform_schema (Destroy KArray) (SArray True SNull) = Just SNull
transform_schema (Destroy KObject) (SObject Empty) = Just SNull
transform_schema (Destroy KObject) (SObject _) = Nothing
transform_schema (Destroy _) _ = Nothing
transform_schema (AddProperty key) (SObject smap) =
    case get key smap of
        Just _ => Nothing
        Nothing => Just (SObject (insert key SNull smap))
transform_schema (AddProperty _) _ = Nothing
transform_schema (RemoveProperty key) (SObject smap) =
    case get key smap of
        Just SNull => Just (SObject (delete key smap))
        _ => Nothing
transform_schema (RemoveProperty _) _ = Nothing
transform_schema (RenameProperty x y) (SObject smap) =
    case (get x smap, get y smap) of
        (Just p, Nothing) =>
            let
                smap = (delete x smap)
                smap = (insert y p smap)
            in Just (SObject smap)
        _ => Nothing
transform_schema (RenameProperty _ _) _ = Nothing
transform_schema (HoistProperty h t) (SObject m) =
    case (get h m, get t m) of
        (Just (SObject hm), Nothing) =>
            case get t hm of
                Just p =>
                    let
                        hm = delete t hm
                        m = insert t p m
                        m = insert h (SObject hm) m
                     in Just (SObject m)
                Nothing => Nothing
        _ => Nothing
transform_schema (HoistProperty _ _) _ = Nothing
transform_schema (PlungeProperty h t) (SObject m) =
    case (get t m, get h m, t == h) of
        (Just p, Just (SObject hm), False) =>
            case get t hm of
                Nothing =>
                    let
                        hm = insert t p hm
                        m = delete t m
                        m = insert h (SObject hm) m
                    in Just (SObject m)
                _ => Nothing
        _ => Nothing
transform_schema (PlungeProperty _ _) _ = Nothing
transform_schema Wrap schema = Just (SArray False schema)
transform_schema Head (SArray False schema) = Just schema
transform_schema Head _ = Nothing
transform_schema (LensIn key lens) (SObject smap) =
    case get key smap of
        Just schema =>
            case transform_schema lens schema of
                Just schema => Just (SObject (insert key schema smap))
                Nothing => Nothing
        Nothing => Nothing
transform_schema (LensIn _ _) _ = Nothing
transform_schema (LensMap lens) (SArray allowEmpty schema) =
    case transform_schema lens schema of
        Just schema' => Just (SArray allowEmpty schema')
        Nothing => Nothing
transform_schema (LensMap _) _ = Nothing
transform_schema (Convert a b map) s with (validate_map a b map)
    transform_schema (Convert KBoolean KBoolean _) SBoolean | True = Just SBoolean
    transform_schema (Convert KBoolean KNumber _) SBoolean | True = Just SNumber
    transform_schema (Convert KBoolean KText _) SBoolean | True = Just SText
    transform_schema (Convert KNumber KBoolean _) SNumber | True = Just SBoolean
    transform_schema (Convert KNumber KNumber _) SNumber | True = Just SNumber
    transform_schema (Convert KNumber KText _) SNumber | True = Just SText
    transform_schema (Convert KText KBoolean _) SText | True = Just SBoolean
    transform_schema (Convert KText KNumber _) SText | True = Just SNumber
    transform_schema (Convert KText KText _) SText | True = Just SText
    transform_schema (Convert _ _ _) _ | _ = Nothing

lenses_to_schema : List Lens -> Maybe Schema
lenses_to_schema [] = Just SNull
lenses_to_schema (l::ls) =
    case lenses_to_schema ls of
        Just s => transform_schema l s
        Nothing => Nothing

transform_value : Lens -> Value -> Value
transform_value (Make KNull) _ = Null
transform_value (Make (KPrimitive KBoolean)) _ = Primitive (Boolean False)
transform_value (Make (KPrimitive KNumber)) _ = Primitive (Number 0)
transform_value (Make (KPrimitive KText)) _ = Primitive (Text [])
transform_value (Make KArray) _ = Array []
transform_value (Make KObject) _ = Object Empty
transform_value (Destroy _) _ = Null
transform_value (AddProperty k) (Object m) = Object (insert k Null m)
transform_value (AddProperty _) v = v
transform_value (RemoveProperty k) (Object m) = Object (remove k m)
transform_value (RemoveProperty _) v = v
transform_value (RenameProperty k1 k2) (Object m) =
    case get k1 m of
        Just v => Object (insert k2 v (remove k1 m))
        Nothing => Object m
transform_value (RenameProperty _ _) v = v
transform_value (HoistProperty h t) (Object m) =
    case get h m of
        Just (Object hm) =>
            case get t hm of
                Just v => Object (insert h (Object (remove t hm)) $ insert t v m)
                Nothing => Object m
        _ => Object m
transform_value (HoistProperty _ _) v = v
transform_value (PlungeProperty h t) (Object m) =
    case (get h m, get t m) of
        (Just (Object hm), Just v) => Object (insert h (Object (insert t v hm)) $ remove t m)
        _ => Object m
transform_value (PlungeProperty _ _) v = v
transform_value Wrap v = Array [v]
transform_value Head (Array (x :: _)) = x
transform_value Head v = v
transform_value (LensIn k l) (Object vm) =
    case get k vm of
        Just v => Object (insert k (transform_value l v) vm)
        Nothing => Object vm
transform_value (LensIn _ _) v = v
transform_value (LensMap l) (Array xs) = Array (map (transform_value l) xs)
transform_value (LensMap _) v = v
transform_value (Convert _ _ m) (Primitive v) =
    case convert_prim v m of
        Just v => (Primitive v)
        Nothing => (Primitive v)
transform_value (Convert _ _ _) v = v


make_reversible : (k : Kind) ->
    (s : Schema) -> (s' : Schema) ->
    transform_schema (Make k) s = Just s' -> transform_schema (reverse_lens (Make k)) s' = Just s
make_reversible k s s' prf = ?make_reversible_rhs

make_preserves_validity : (k : Kind) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (Make k) s = Just s' -> transform_value (Make k) v = v' ->
    validate s v = True -> validate s' v' = True
make_preserves_validity k s s' v v' prf prf1 prf2 = ?make_preserves_validity_rhs

destroy_reversible : (k : Kind) ->
    (s : Schema) -> (s' : Schema) ->
    transform_schema (Destroy k) s = Just s' -> transform_schema (reverse_lens (Destroy k)) s' = Just s
destroy_reversible k s s' prf = ?destroy_reversible_rhs

destroy_preserves_validity : (k : Kind) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (Destroy k) s = Just s' -> transform_value (Destroy k) v = v' ->
    validate s v = True -> validate s' v' = True
destroy_preserves_validity k s s' v v' prf prf1 prf2 = ?destroy_lens_preserves_validity_rhs


add_property_reversible : (k : Key) ->
    (s : Schema) -> (s' : Schema) ->
    transform_schema (AddProperty k) s = Just s' -> transform_schema (reverse_lens (AddProperty k)) s' = Just s
add_property_reversible k s s' prf = ?add_property_reversible_rhs

add_property_preserves_validity : (k : Key) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (AddProperty k) s = Just s' -> transform_value (AddProperty k) v = v' ->
    validate s v = True -> validate s' v' = True
add_property_preserves_validity k s s' v v' prf prf1 prf2 = ?add_property_preserves_validity_rhs

remove_property_reversible : (k : Key) ->
    (s : Schema) -> (s' : Schema) ->
    transform_schema (RemoveProperty k) s = Just s' -> transform_schema (reverse_lens (RemoveProperty k)) s' = Just s
remove_property_reversible k s s' prf = ?remove_property_reversible_rhs

remove_property_preserves_validity : (k : Key) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (RemoveProperty k) s = Just s' -> transform_value (RemoveProperty k) v = v' ->
    validate s v = True -> validate s' v' = True
remove_property_preserves_validity k s s' v v' prf prf1 prf2 = ?remove_property_preserves_validity_rhs


rename_property_reversible : (k, k' : Key) ->
    (s : Schema) -> (s' : Schema) ->
    transform_schema (RenameProperty k k') s = Just s' -> transform_schema (reverse_lens (RenameProperty k k')) s' = Just s
rename_property_reversible k k' s s' prf = ?rename_property_reversible_rhs

rename_property_preserves_validity : (k, k' : Key) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (RenameProperty k k') s = Just s' -> transform_value (RenameProperty k k') v = v' ->
    validate s v = True -> validate s' v' = True
rename_property_preserves_validity k k' s s' v v' prf prf1 prf2 = ?rename_property_preserves_validity_rhs


hoist_property_reversible : (h, t : Key) ->
    (s : Schema) -> (s' : Schema) ->
    transform_schema (HoistProperty h t) s = Just s' -> transform_schema (reverse_lens (HoistProperty h t)) s' = Just s
hoist_property_reversible h t s s' prf = ?hoist_property_reversible_rhs

hoist_property_preserves_validity : (h, t : Key) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (HoistProperty h t) s = Just s' -> transform_value (HoistProperty h t) v = v' ->
    validate s v = True -> validate s' v' = True
hoist_property_preserves_validity h t s s' v v' prf prf1 prf2 = ?hoist_property_preserves_validity_rhs

plunge_property_reversible : (h, t : Key) ->
    (s : Schema) -> (s' : Schema) ->
    transform_schema (PlungeProperty h t) s = Just s' -> transform_schema (reverse_lens (PlungeProperty h t)) s' = Just s
plunge_property_reversible h t s s' prf = ?plunge_property_reversible_rhs

plunge_property_preserves_validity : (h, t : Key) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (PlungeProperty h t) s = Just s' -> transform_value (PlungeProperty h t) v = v' ->
    validate s v = True -> validate s' v' = True
plunge_property_preserves_validity h t s s' v v' prf prf1 prf2 = ?plunge_property_preserves_validity_rhs


wrap_reversible :
    (s : Schema) -> (s' : Schema) ->
    transform_schema Wrap s = Just s' -> transform_schema (reverse_lens Wrap) s' = Just s
wrap_reversible s s' prf = ?wrap_reversible_rhs

wrap_preserves_validity :
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema Wrap s = Just s' -> transform_value Wrap v = v' ->
    validate s v = True -> validate s' v' = True
wrap_preserves_validity s s' v v' prf prf1 prf2 = ?wrap_preserves_validity_rhs

head_reversible :
    (s : Schema) -> (s' : Schema) ->
    transform_schema Head s = Just s' -> transform_schema (reverse_lens Head) s' = Just s
head_reversible s s' prf = ?head_reversible_rhs

head_preserves_validity :
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema Head s = Just s' -> transform_value Head v = v' ->
    validate s v = True -> validate s' v' = True
head_preserves_validity s s' v v' prf prf1 prf2 = ?head_preserves_validity_rhs


convert_reversible : (k, k' : PrimitiveKind) -> (m : List (PrimitiveValue, PrimitiveValue)) ->
    (s : Schema) -> (s' : Schema) ->
    transform_schema (Convert k k' m) s = Just s' -> transform_schema (reverse_lens (Convert k k' m)) s' = Just s
convert_reversible k k' m s s' prf = ?convert_reversible_rhs

convert_preserves_validity : (k, k' : PrimitiveKind) -> (m : List (PrimitiveValue, PrimitiveValue)) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (Convert k k' m) s = Just s' -> transform_value (Convert k k' m) v = v' ->
    validate s v = True -> validate s' v' = True
convert_preserves_validity k k' m s s' v v' prf prf1 prf2 = ?convert_preserves_validity_rhs


||| Forwards and backwards compatibility requires schema transformations to be reversible
lens_reversible : (l : Lens) -> (s : Schema) -> (s' : Schema) ->
    transform_schema l s = Just s' -> transform_schema (reverse_lens l) s' = Just s
lens_reversible (Make k) s s' prf = make_reversible k s s' prf
lens_reversible (Destroy k) s s' prf = destroy_reversible k s s' prf
lens_reversible (AddProperty k) s s' prf = add_property_reversible k s s' prf
lens_reversible (RemoveProperty k) s s' prf = remove_property_reversible k s s' prf
lens_reversible (RenameProperty k k') s s' prf = rename_property_reversible k k' s s' prf
lens_reversible (HoistProperty h t) s s' prf = hoist_property_reversible h t s s' prf
lens_reversible (PlungeProperty h t) s s' prf = plunge_property_reversible h t s s' prf
lens_reversible Wrap s s' prf = wrap_reversible s s' prf
lens_reversible Head s s' prf = head_reversible s s' prf
lens_reversible (LensIn k l) s s' prf = ?lens_reversible_rhs_10
lens_reversible (LensMap l) s s' prf = ?lens_reversible_rhs_11
lens_reversible (Convert k k' m) s s' prf = convert_reversible k k' m s s' prf

||| Transforming a valid value must result in a valid value
lens_preserves_validity : (l : Lens) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema l s = Just s' -> transform_value l v = v' ->
    validate s v = True -> validate s' v' = True
lens_preserves_validity (Make k) s s' v v' prf prf1 prf2 =
    make_preserves_validity k s s' v v' prf prf1 prf2
lens_preserves_validity (Destroy k) s s' v v' prf prf1 prf2 =
    destroy_preserves_validity k s s' v v' prf prf1 prf2
lens_preserves_validity (AddProperty k) s s' v v' prf prf1 prf2 =
    add_property_preserves_validity k s s' v v' prf prf1 prf2
lens_preserves_validity (RemoveProperty k) s s' v v' prf prf1 prf2 =
    remove_property_preserves_validity k s s' v v' prf prf1 prf2
lens_preserves_validity (RenameProperty k k') s s' v v' prf prf1 prf2 =
    rename_property_preserves_validity k k' s s' v v' prf prf1 prf2
lens_preserves_validity (HoistProperty h t) s s' v v' prf prf1 prf2 =
    hoist_property_preserves_validity h t s s' v v' prf prf1 prf2
lens_preserves_validity (PlungeProperty h t) s s' v v' prf prf1 prf2 =
    plunge_property_preserves_validity h t s s' v v' prf prf1 prf2
lens_preserves_validity Wrap s s' v v' prf prf1 prf2 =
    wrap_preserves_validity s s' v v' prf prf1 prf2
lens_preserves_validity Head s s' v v' prf prf1 prf2 =
    head_preserves_validity s s' v v' prf prf1 prf2
lens_preserves_validity (LensIn k l) s s' v v' prf prf1 prf2 = ?lens_preserves_validity_rhs_10
lens_preserves_validity (LensMap l) s s' v v' prf prf1 prf2 = ?lens_preserves_validity_rhs_11
lens_preserves_validity (Convert k k' m) s s' v v' prf prf1 prf2 =
    convert_preserves_validity k k' m s s' v v' prf prf1 prf2
