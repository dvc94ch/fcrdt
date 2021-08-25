module Fcrdt.Lens.Valid

import Data.List
import Data.Maybe
import Fcrdt.Lens
import Fcrdt.Lens.Uninhabited
import Fcrdt.Lens.Util
import Fcrdt.Map

%default total


make_preserves_validity : (k : Kind) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (Make k) s = Just s' -> transform_value (Make k) v = v' ->
    validate s v = True -> validate s' v' = True
make_preserves_validity KNull _ _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KBoolean) SNull SNull _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KBoolean) SNull SBoolean _ _ _ prf1 _ = rewrite sym prf1 in Refl
make_preserves_validity (KPrimitive KBoolean) SNull SNumber _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KBoolean) SNull SText _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KBoolean) SNull (SArray _ _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity (KPrimitive KBoolean) SNull (SObject _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity (KPrimitive KBoolean) SBoolean _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KBoolean) SNumber _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KBoolean) SText _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KBoolean) (SArray _ _) _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KBoolean) (SObject _) _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KNumber) SNull SNull _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KNumber) SNull SBoolean _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KNumber) SNull SNumber _ _ _ prf1 _ = rewrite sym prf1 in Refl
make_preserves_validity (KPrimitive KNumber) SNull SText _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KNumber) SNull (SArray _ _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity (KPrimitive KNumber) SNull (SObject _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity (KPrimitive KNumber) SBoolean _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KNumber) SNumber _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KNumber) SText _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KNumber) (SArray _ _) _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KNumber) (SObject _) _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KText) SNull SNull _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KText) SNull SBoolean _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KText) SNull SNumber _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KText) SNull SText _ _ _ prf1 _ = rewrite sym prf1 in Refl
make_preserves_validity (KPrimitive KText) SNull (SArray _ _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity (KPrimitive KText) SNull (SObject _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity (KPrimitive KText) SBoolean _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KText) SNumber _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KText) SText _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KText) (SArray _ _) _ _ _ Refl _ _ impossible
make_preserves_validity (KPrimitive KText) (SObject _) _ _ _ Refl _ _ impossible
make_preserves_validity KArray SNull SNull _ _ Refl _ _ impossible
make_preserves_validity KArray SNull SBoolean _ _ Refl _ _ impossible
make_preserves_validity KArray SNull SNumber _ _ Refl _ _ impossible
make_preserves_validity KArray SNull SText _ _ Refl _ _ impossible
make_preserves_validity KArray SNull (SArray False _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity KArray SNull (SArray True _) _ _ _ prf1 _ = rewrite sym prf1 in Refl
make_preserves_validity KArray SNull (SObject _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity KArray SBoolean _ _ _ Refl _ _ impossible
make_preserves_validity KArray SNumber _ _ _ Refl _ _ impossible
make_preserves_validity KArray SText _ _ _ Refl _ _ impossible
make_preserves_validity KArray (SArray _ _) _ _ _ Refl _ _ impossible
make_preserves_validity KArray (SObject _) _ _ _ Refl _ _ impossible
make_preserves_validity KObject SNull SNull _ _ Refl _ _ impossible
make_preserves_validity KObject SNull SBoolean _ _ Refl _ _ impossible
make_preserves_validity KObject SNull SNumber _ _ Refl _ _ impossible
make_preserves_validity KObject SNull SText _ _ Refl _ _ impossible
make_preserves_validity KObject SNull (SArray _ _) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity KObject SNull (SObject Empty) _ _ _ prf1 _ = rewrite sym prf1 in Refl
make_preserves_validity KObject SNull (SObject (Entry _ _ _ _)) _ _ prf _ _ = absurd $ justInjective prf
make_preserves_validity KObject SBoolean _ _ _ Refl _ _ impossible
make_preserves_validity KObject SNumber _ _ _ Refl _ _ impossible
make_preserves_validity KObject SText _ _ _ Refl _ _ impossible
make_preserves_validity KObject (SArray _ _) _ _ _ Refl _ _ impossible
make_preserves_validity KObject (SObject _) _ _ _ Refl _ _ impossible

destroy_preserves_validity : (k : Kind) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (Destroy k) s = Just s' -> transform_value (Destroy k) v = v' ->
    validate s v = True -> validate s' v' = True
destroy_preserves_validity KNull _ _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KBoolean) SNull _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KBoolean) SBoolean SNull _ _ Refl prf1 _ = rewrite sym prf1 in Refl
destroy_preserves_validity (KPrimitive KBoolean) SNumber _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KBoolean) SText _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KBoolean) (SArray _ _) _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KBoolean) (SObject _) _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KNumber) SNull _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KNumber) SBoolean _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KNumber) SNumber SNull _ _ Refl prf1 _ = rewrite sym prf1 in Refl
destroy_preserves_validity (KPrimitive KNumber) SText _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KNumber) (SArray _ _) _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KNumber) (SObject _) _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KText) SNull _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KText) SBoolean _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KText) SNumber _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KText) SText SNull _ _ Refl prf1 prf2 = rewrite sym prf1 in Refl
destroy_preserves_validity (KPrimitive KText) (SArray _ _) _ _ _ Refl _ _ impossible
destroy_preserves_validity (KPrimitive KText) (SObject _) _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray SNull _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray SBoolean _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray SNumber _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray SText _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray (SArray False _) _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray (SArray True SNull) SNull _ _ Refl prf1 _ = rewrite sym prf1 in Refl
destroy_preserves_validity KArray (SArray True SBoolean) _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray (SArray True SNumber) _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray (SArray True SText) _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray (SArray True (SArray _ _)) _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray (SArray True (SObject _)) _ _ _ Refl _ _ impossible
destroy_preserves_validity KArray (SObject _) _ _ _ Refl _ _ impossible
destroy_preserves_validity KObject SNull _ _ _ Refl _ _ impossible
destroy_preserves_validity KObject SBoolean _ _ _ Refl _ _ impossible
destroy_preserves_validity KObject SNumber _ _ _ Refl _ _ impossible
destroy_preserves_validity KObject SText _ _ _ Refl _ _ impossible
destroy_preserves_validity KObject (SArray _ _) _ _ _ Refl _ _ impossible
destroy_preserves_validity KObject (SObject Empty) SNull _ _ Refl prf1 _ = rewrite sym prf1 in Refl
destroy_preserves_validity KObject (SObject (Entry _ _ _ _)) _ _ _ Refl _ _ impossible


add_property_preserves_validity : (k : Key) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (AddProperty k) s = Just s' -> transform_value (AddProperty k) v = v' ->
    validate s v = True -> validate s' v' = True
add_property_preserves_validity _ SNull _ _ _ Refl _ _ impossible
add_property_preserves_validity _ SBoolean _ _ _ Refl _ _ impossible
add_property_preserves_validity _ SNumber _ _ _ Refl _ _ impossible
add_property_preserves_validity _ SText _ _ _ Refl _ _ impossible
add_property_preserves_validity _ (SArray _ _) _ _ _ Refl _ _ impossible
add_property_preserves_validity k (SObject m) s' v v' prf prf1 prf2 with (get k m) proof prf3
    add_property_preserves_validity k (SObject _) _ _ _ prf _ _ | (Just _) = absurd $ prf
    add_property_preserves_validity k (SObject _) _ Null _ _ _ prf2 | Nothing = absurd $ prf2
    add_property_preserves_validity k (SObject _) _ (Primitive _) _ _ _ prf2 | Nothing = absurd $ prf2
    add_property_preserves_validity k (SObject _) _ (Array _) _ _ _ prf2 | Nothing = absurd $ prf2
    add_property_preserves_validity k (SObject sm) s' (Object vm) v' prf prf1 prf2 | Nothing =
        rewrite sym $ justInjective prf in
        rewrite sym prf1 in
        let
            split = and_split (all_properties_exist sm vm) (validate_properties vm sm) prf2
            exist = all_properties_exist_after_insert sm vm k SNull Null (fst split)
            valid = validate_properties_after_insert vm sm k Null SNull Refl (snd split)
        in rewrite exist in rewrite valid in Refl

remove_property_preserves_validity : (k : Key) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (RemoveProperty k) s = Just s' -> transform_value (RemoveProperty k) v = v' ->
    validate s v = True -> validate s' v' = True
remove_property_preserves_validity _ SNull _ _ _ Refl _ _ impossible
remove_property_preserves_validity _ SBoolean _ _ _ Refl _ _ impossible
remove_property_preserves_validity _ SNumber _ _ _ Refl _ _ impossible
remove_property_preserves_validity _ SText _ _ _ Refl _ _ impossible
remove_property_preserves_validity _ (SArray _ _) _ _ _ Refl _ _ impossible
remove_property_preserves_validity k (SObject m) s' v v' prf prf1 prf2 with (get k m) proof prf3
    remove_property_preserves_validity _ (SObject _) _ _ _ prf _ _ | Nothing = absurd $ prf
    remove_property_preserves_validity _ (SObject _) _ Null _ _ _ prf2 | (Just _) = absurd $ prf2
    remove_property_preserves_validity _ (SObject _) _ (Primitive _) _ _ _ prf2 | (Just _) = absurd $ prf2
    remove_property_preserves_validity _ (SObject _) _ (Array _) _ _ _ prf2 | (Just _) = absurd $ prf2
    remove_property_preserves_validity _ (SObject _) _ (Object _) _ prf _ _ | (Just SBoolean) = absurd $ prf
    remove_property_preserves_validity _ (SObject _) _ (Object _) _ prf _ _ | (Just SNumber) = absurd $ prf
    remove_property_preserves_validity _ (SObject _) _ (Object _) _ prf _ _ | (Just SText) = absurd $ prf
    remove_property_preserves_validity _ (SObject _) _ (Object _) _ prf _ _ | (Just (SArray _ _)) = absurd $ prf
    remove_property_preserves_validity _ (SObject _) _ (Object _) _ prf _ _ | (Just (SObject _)) = absurd $ prf
    remove_property_preserves_validity k (SObject sm) s' (Object vm) v' prf prf1 prf2 | (Just SNull) =
        rewrite sym $ justInjective prf in
        rewrite sym prf1 in
        let
            split = and_split (all_properties_exist sm vm) (validate_properties vm sm) prf2
            exist = all_properties_exist_after_remove sm vm k (fst split)
            valid = validate_properties_after_remove vm sm k (snd split)
        in rewrite exist in rewrite valid in Refl

rename_property_preserves_validity : (k, k' : Key) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (RenameProperty k k') s = Just s' -> transform_value (RenameProperty k k') v = v' ->
    validate s v = True -> validate s' v' = True
rename_property_preserves_validity k k' s s' v v' prf prf1 prf2 = ?rename_property_preserves_validity_rhs

hoist_property_preserves_validity : (h, t : Key) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (HoistProperty h t) s = Just s' -> transform_value (HoistProperty h t) v = v' ->
    validate s v = True -> validate s' v' = True
hoist_property_preserves_validity h t s s' v v' prf prf1 prf2 = ?hoist_property_preserves_validity_rhs

plunge_property_preserves_validity : (h, t : Key) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (PlungeProperty h t) s = Just s' -> transform_value (PlungeProperty h t) v = v' ->
    validate s v = True -> validate s' v' = True
plunge_property_preserves_validity h t s s' v v' prf prf1 prf2 = ?plunge_property_preserves_validity_rhs

wrap_preserves_validity :
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema Wrap s = Just s' -> transform_value Wrap v = v' ->
    validate s v = True -> validate s' v' = True
wrap_preserves_validity _ _ _ _ prf prf1 prf2 =
    rewrite sym $ justInjective prf in rewrite sym prf1 in rewrite prf2 in Refl

head_preserves_validity :
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema Head s = Just s' -> transform_value Head v = v' ->
    validate s v = True -> validate s' v' = True
head_preserves_validity SNull _ _ _ Refl _ _ impossible
head_preserves_validity SBoolean _ _ _ Refl _ _ impossible
head_preserves_validity SNumber _ _ _ Refl _ _ impossible
head_preserves_validity SText _ _ _ Refl _ _ impossible
head_preserves_validity (SArray False _) _ Null _ _ _ Refl impossible
head_preserves_validity (SArray False _) _ (Primitive _) _ _ _ Refl impossible
head_preserves_validity (SArray False _) _ (Array []) _ _ _ Refl impossible
head_preserves_validity (SArray False s) _ (Array (h :: xs)) _ prf prf1 prf2 =
    rewrite sym $ justInjective prf in rewrite sym prf1 in
    let split = and_split (validate s h) (validate (SArray True s) (Array xs)) prf2 in
    rewrite fst split in Refl
head_preserves_validity (SArray False _) _ (Object _) _ _ _ Refl impossible
head_preserves_validity (SArray True _) _ _ _ Refl _ _ impossible
head_preserves_validity (SObject _) _ _ _ Refl _ _ impossible

convert_preserves_validity : (k, k' : PrimitiveKind) -> (m : List (PrimitiveValue, PrimitiveValue)) ->
    (s : Schema) -> (s' : Schema) -> (v : Value) -> (v' : Value) ->
    transform_schema (Convert k k' m) s = Just s' -> transform_value (Convert k k' m) v = v' ->
    validate s v = True -> validate s' v' = True
convert_preserves_validity k k' m s s' v v' prf prf1 prf2 = ?convert_preserves_validity_rhs


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
lens_preserves_validity (LensIn _ _) SNull _ _ _ Refl _ _ impossible
lens_preserves_validity (LensIn _ _) SBoolean _ _ _ Refl _ _ impossible
lens_preserves_validity (LensIn _ _) SNumber _ _ _ Refl _ _ impossible
lens_preserves_validity (LensIn _ _) SText _ _ _ Refl _ _ impossible
lens_preserves_validity (LensIn _ _) (SArray _ _) _ _ _ Refl _ _ impossible
lens_preserves_validity (LensIn _ _) (SObject _) _ Null _ _ _ Refl impossible
lens_preserves_validity (LensIn _ _) (SObject _) _ (Primitive _) _ _ _ Refl impossible
lens_preserves_validity (LensIn _ _) (SObject _) _ (Array _) _ _ _ Refl impossible
lens_preserves_validity (LensIn k l) (SObject ms) s' (Object mv) v' prf prf1 prf2 = ?h_10
lens_preserves_validity (LensMap _) SNull _ _ _ Refl _ _ impossible
lens_preserves_validity (LensMap _) SBoolean _ _ _ Refl _ _ impossible
lens_preserves_validity (LensMap _) SNumber _ _ _ Refl _ _ impossible
lens_preserves_validity (LensMap _) SText _ _ _ Refl _ _ impossible
lens_preserves_validity (LensMap _) (SArray _ _) _ Null _ _ _ Refl impossible
lens_preserves_validity (LensMap _) (SArray _ _) _ (Primitive _) _ _ _ Refl impossible
lens_preserves_validity (LensMap l) (SArray e s2) s' (Array xs) v' prf prf1 prf2 with (transform_schema l s2) proof prf3
    lens_preserves_validity (LensMap _) (SArray _ _) SNull (Array _) _ prf _ _ | (Just _) =
        absurd $ justInjective $ prf
    lens_preserves_validity (LensMap _) (SArray _ _) SBoolean (Array _) _ prf _ _ | (Just _) =
        absurd $ justInjective $ prf
    lens_preserves_validity (LensMap _) (SArray _ _) SNumber (Array _) _ prf _ _ | (Just _) =
        absurd $ justInjective $ prf
    lens_preserves_validity (LensMap _) (SArray _ _) SText (Array _) _ prf _ _ | (Just _) =
        absurd $ justInjective $ prf
    lens_preserves_validity (LensMap _) (SArray _ _) (SArray _ _) (Array _) Null _ prf1 _ | (Just _) =
        absurd $ prf1
    lens_preserves_validity (LensMap _) (SArray _ _) (SArray _ _) (Array _) (Primitive _) _ prf1 _ | (Just _) =
        absurd $ prf1
    lens_preserves_validity (LensMap _) (SArray _ _) (SArray _ _) (Array []) (Array []) prf _ prf2 | (Just _) =
        rewrite sym $ justInjective $ cong allow_empty $ justInjective prf in
        rewrite prf2 in Refl
    lens_preserves_validity (LensMap _) (SArray _ _) (SArray _ _) (Array []) (Array (_ :: _)) _ prf1 _ | (Just _) =
        absurd $ prf1
    lens_preserves_validity (LensMap _) (SArray _ _) (SArray _ _) (Array (_ :: _)) (Array []) _ prf1 _ | (Just _) =
        absurd $ prf1
    lens_preserves_validity (LensMap l) (SArray e s2) (SArray e' s2') (Array (v2 :: xs)) (Array (v2' :: xs')) prf prf1 prf2 | (Just s2'2) with (validate s2 v2) proof prf4
        lens_preserves_validity (LensMap l) (SArray e s2) (SArray e' s2') (Array (v2 :: xs)) (Array (v2' :: xs')) prf prf1 prf2 | (Just s2'2) | False = absurd $ prf2
        lens_preserves_validity (LensMap l) (SArray e s2) (SArray e' s2') (Array (v2 :: xs)) (Array (v2' :: xs')) prf prf1 prf2 | (Just s2'2) | True =
        let ind = lens_preserves_validity l s2 s2' v2 v2' in
            ?hhhhhhh

    lens_preserves_validity (LensMap _) (SArray _ _) (SArray _ _) (Array _) (Object _) _ prf1 _ | (Just _) =
        absurd $ prf1

    lens_preserves_validity (LensMap _) (SArray _ _) (SObject _) (Array _) _ prf _ _ | (Just _) =
        absurd $ justInjective $ prf
lens_preserves_validity (LensMap _) (SArray _ _) _ (Object _) _ _ _ Refl impossible
lens_preserves_validity (LensMap _) (SObject _) _ _ _ Refl _ _ impossible
lens_preserves_validity (Convert k k' m) s s' v v' prf prf1 prf2 =
    convert_preserves_validity k k' m s s' v v' prf prf1 prf2
