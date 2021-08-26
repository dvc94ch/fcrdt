module Fcrdt.Lens.Util

import Data.Maybe
import Fcrdt.Lens
import Fcrdt.Lens.Uninhabited
import Fcrdt.Map

%default total

public export
beq_prim : (v : PrimitiveValue) ->  v == v = True
beq_prim (Boolean b) = beq_bool b
beq_prim (Number n) = beq_nat n
beq_prim (Text t) = beq_str t

public export
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

public export
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


public export
all_properties_exist_after_insert : (sm : Map Schema) -> (vm : Map Value) ->
    (k : Key) -> (s : Schema) -> (v : Value) ->
    all_properties_exist sm vm = True -> all_properties_exist (insert k s sm) (insert k v vm) = True
all_properties_exist_after_insert sm vm k s v prf with (containsP k vm)
    all_properties_exist_after_insert Empty Empty k s v prf | (ReflectT x prf1) = absurd $ prf1
    all_properties_exist_after_insert Empty (Entry k1 y m p) k s v prf | (ReflectT x prf1) = ?h3_6
    all_properties_exist_after_insert (Entry k1 y m p) vm k s v prf | (ReflectT x prf1) = ?h3_4
    all_properties_exist_after_insert sm vm k s v prf | (ReflectF f prf1) = ?h3_2

public export
all_properties_exist_after_remove : (sm : Map Schema) -> (vm : Map Value) -> (k : Key) ->
    all_properties_exist sm vm = True -> all_properties_exist (remove k sm) (remove k vm) = True

public export
not_all_properties_exist : (sm : Map Schema) -> (vm : Map Value) ->
    (k : Key) -> get k sm = Just _ -> get k vm = Nothing -> all_properties_exist sm vm = False

public export
validate_properties_after_insert : (vm : Map Value) -> (sm : Map Schema) ->
    (k : Key) -> (v : Value) -> (s : Schema) -> validate s v = True ->
    validate_properties vm sm = True -> validate_properties (insert k v vm) (insert k s sm) = True

public export
validate_properties_after_remove : (vm : Map Value) -> (sm : Map Schema) -> (k : Key) ->
    validate_properties vm sm = True -> validate_properties (remove k vm) (remove k sm) = True

public export
invalid_property : (vm : Map Value) -> (sm : Map Schema) -> (k : Key) ->
    (v : Value) -> (s : Schema) -> get k vm = Just v -> get k sm = Just s -> validate s v = False ->
    validate_properties vm sm = False

public export
still_valid : (vm : Map Value) -> (sm : Map Schema) ->
    (k : Key) -> (kvm : Value) -> (ksm : Schema) ->
    get k vm = Just kvm -> get k sm = Just ksm ->
    validate_properties vm sm = True -> validate ksm kvm = True

public export
still_invalid : (vm : Map Value) -> (sm : Map Schema) ->
    (k : Key) ->  get k vm = Just kvm -> get k sm = Just ksm ->
    validate ksm kvm = False -> validate_properties vm sm = False

public export
flip_map_twice : (m : List (PrimitiveValue, PrimitiveValue)) -> flip_map (flip_map m) = m
flip_map_twice [] = Refl
flip_map_twice ((x, y) :: xs) = rewrite flip_map_twice xs in Refl

public export
flip_map_preserves_validity : (a, b : PrimitiveKind) -> (m : List (PrimitiveValue, PrimitiveValue)) ->
    validate_map a b m = True -> validate_map b a (flip_map m) = True
flip_map_preserves_validity a b [] prf = Refl
flip_map_preserves_validity a b ((x, y) :: xs) prf =
    let sprf = and_split (prim_kind_of x == a) (prim_kind_of y == b && Delay (validate_map a b xs)) prf
        sprf2 = and_split (prim_kind_of y == b) (validate_map a b xs) (snd sprf)
        ind = flip_map_preserves_validity a b xs (snd sprf2)
    in rewrite fst sprf2 in rewrite fst sprf in ind

public export
convert_prim_kind : (a, b : PrimitiveKind) -> (va, vb : PrimitiveValue) ->
    (m : List (PrimitiveValue, PrimitiveValue)) -> validate_map a b m = True ->
    prim_kind_of va = a -> convert_prim va m = Just vb -> prim_kind_of vb = b
