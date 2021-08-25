
{-
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
assertReverseSchema (Destroy KObject) (SObject Empty) _ = Refl
assertReverseSchema (Destroy KObject) (SObject (Entry _ _ _ _)) prf = absurd $ prf
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
            in rewrite assertReverseSchema' l s s' prf2
            in rewrite update_shadow m k (Just (r, s')) (Just (r, s))
            in rewrite update_same m k (Just (r, s)) prf1
            in Refl
assertReverseSchema (LensMap _) SFalse ItIsJust impossible
assertReverseSchema (LensMap _) (SBoolean _) ItIsJust impossible
assertReverseSchema (LensMap _) (SNumber _) ItIsJust impossible
assertReverseSchema (LensMap _) (SText _) ItIsJust impossible
assertReverseSchema (LensMap l) (SArray e s) prf with (applyLensSchema l s) proof prf1
    assertReverseSchema (LensMap _) (SArray _ _) prf | Nothing = absurd $ prf
    assertReverseSchema (LensMap l) (SArray e s) prf | (Just s') =
        rewrite assertReverseSchema' l s s' prf1 in Refl
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
assertReverseSchema (Default (Text _) (Text _)) (SObject _) ItIsJust impossible
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
-}










module Fcrdt.Lens

import Data.List
import Data.Maybe

-- %default total

||| TODO
||| Implement convert transform
||| Support combining schemas (and/or)

data PrimitiveValue =
      Boolean Bool
    | Number Int
    | Text String

Eq PrimitiveValue where
    Boolean b1 == Boolean b2 = b1 == b2
    Number n1 == Number n2 = n1 == n2
    Text t1 == Text t2 = t1 == t2

data PrimitiveKind =
      KBoolean
    | KNumber
    | KText

Eq PrimitiveKind where
    KBoolean == KBoolean = True
    KNumber == KNumber = True
    KText == KText = True
    _ == _ = False

||| Modeling keys as nats as idris seems to be able to
||| reason better about equality
data Value =
      Primitive PrimitiveValue
    | Array (List Value)
    | Object (List (Nat, Value))

Eq Value where
    Primitive v1 == Primitive v2 = v1 == v2
    Array vs1 == Array vs2 = assert_total (vs1 == vs2)
    Object ps1 == Object ps2 = assert_total (ps1 == ps2)
    _ == _ = False

data Kind =
      KPrimitive PrimitiveKind
    | KArray
    | KObject

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
      AddProperty Nat
    | RemoveProperty Nat
    | RenameProperty Nat Nat
    | HoistProperty Nat Nat
    | PlungeProperty Nat Nat
    | WrapProperty
    | HeadProperty
    | AllowEmpty Bool Value
    | LensIn Nat Lens
    | LensMap Lens
    | Make Kind
    | Destroy Kind
    | Require Bool
    | Optional Bool
    | Default Value Value
    | Convert PrimitiveKind PrimitiveKind (List (Primitive, Primitive))

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
    Convert k11 k21 f1 == Convert k12 k22 f2 = k11 == k12 && k22 == k22 && f1 == f2
    _ == _ = False

{-applyLensSchema : Lens -> Schema -> Maybe Schema
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
applyLensSchema (LensMap lens) (SArray allowEmpty schema) =
    map (SArray allowEmpty) (applyLensSchema lens schema)
applyLensSchema (LensMap _) _ = Nothing
applyLensSchema (Convert VoidKind BooleanKind []) SFalse = SBoolean
applyLensSchema (Convert VoidKind NumberKind []) SFalse = SNumber
applyLensSchema (Convert VoidKind TextKind []) SFalse = SText
applyLensSchema (Convert VoidKind ArrayKind []) SFalse = SArray True SFalse
applyLensSchema (Convert VoidKind ObjectKind []) SFalse = SObject []
applyLensSchema (Convert VoidKind _ _) _ = Nothing
applyLensSchema (Convert BooleanKind b m) s = ?applyLensSchemaConvert_1
applyLensSchema (Convert NumberKind b m) s = ?applyLensSchemaConvert_2
applyLensSchema (Convert TextKind b m) s = ?applyLensSchemaConvert_3
applyLensSchema (Convert ArrayKind b m) s = ?applyLensSchemaConvert_4
applyLensSchema (Convert ObjectKind b m) s = ?applyLensSchemaConvert_5

lensToSchema : List Lens -> Maybe Schema
lensToSchema [] = Just SFalse
lensToSchema (l::ls) =
    case lensToSchema ls of
        Just s => applyLensSchema l s
        Nothing => Nothing

schemaToLens : Schema -> List Lens

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
applyLensValue (Convert a b f) v = ?applyLensValueConvert

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
reverseLens (Convert a b m) = Convert b a (map (\(a, b) => (b, a)) m)

applyTwoLenses : Lens -> Lens -> Schema -> Maybe Schema
applyTwoLenses a b s =
    case applyLensSchema a s of
        Just s => applyLensSchema b s
        Nothing => Nothing

applyABimpliesApplyA : isJust (applyTwoLenses a b s) = True -> isJust (applyLensSchema a s) = True

reverseSchema : Lens -> Schema -> Maybe Schema
reverseSchema l s = applyTwoLenses l (reverseLens l) s

fnExample : (x : Maybe a) -> Maybe a
fnExample x =
    case x of
        Just x => Just x
        Nothing => Nothing

assertFnExample : (x : Maybe a) -> (isJust x = True) -> (isJust (fnExample x) = True)
assertFnExample Nothing Refl impossible
assertFnExample (Just x) prf = prf

assertFnExample2 : (x : Maybe a) -> (isJust (fnExample x) = True) -> (isJust x = True)
assertFnExample2 Nothing Refl impossible
assertFnExample2 (Just x) prf = prf

lemmaMaybeMap : (x : Maybe a) -> (f : a -> b) -> (isJust (map f x) = True) -> isJust x = True
lemmaMaybeMap Nothing _ Refl impossible
lemmaMaybeMap (Just x) _ _ = Refl

lemmaMaybeMap2 : (x : Maybe a) -> (f : a -> b) -> IsJust (map f x) -> IsJust x
lemmaMaybeMap2 Nothing _ ItIsJust impossible
lemmaMaybeMap2 (Just x) f y = ItIsJust

||| Forwards and backwards compatibility requires schema transformations to be reversible
assertReverseSchema :
    (lens: Lens) ->
    (schema: Schema) ->
    (IsJust (applyLensSchema lens schema)) ->
    (reverseSchema lens schema = Just schema)
assertReverseSchema (AddProperty n False v) SFalse _ = ?assertReverseSchema_rhs_25
assertReverseSchema (AddProperty n True v) SFalse _ = ?assertReverseSchema_rhs_26
assertReverseSchema (AddProperty _ _ _) SBoolean ItIsJust impossible
assertReverseSchema (AddProperty _ _ _) SNumber ItIsJust impossible
assertReverseSchema (AddProperty _ _ _) SText ItIsJust impossible
assertReverseSchema (AddProperty _ _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (AddProperty x y z) (SObject w) prf = ?assertReverseSchema_rhs_15
assertReverseSchema (RemoveProperty _ _ _) SFalse ItIsJust impossible
assertReverseSchema (RemoveProperty _ _ _) SBoolean ItIsJust impossible
assertReverseSchema (RemoveProperty _ _ _) SNumber ItIsJust impossible
assertReverseSchema (RemoveProperty _ _ _) SText ItIsJust impossible
assertReverseSchema (RemoveProperty _ _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (RemoveProperty x y z) (SObject w) prf = ?assertReverseSchema_rhs_17
assertReverseSchema (RenameProperty _ _) SFalse ItIsJust impossible
assertReverseSchema (RenameProperty _ _) SBoolean ItIsJust impossible
assertReverseSchema (RenameProperty _ _) SNumber ItIsJust impossible
assertReverseSchema (RenameProperty _ _) SText ItIsJust impossible
assertReverseSchema (RenameProperty _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (RenameProperty x y) (SObject z) prf = ?assertReverseSchema_rhs_18
assertReverseSchema (HoistProperty _ _) SFalse ItIsJust impossible
assertReverseSchema (HoistProperty _ _) SBoolean ItIsJust impossible
assertReverseSchema (HoistProperty _ _) SNumber ItIsJust impossible
assertReverseSchema (HoistProperty _ _) SText ItIsJust impossible
assertReverseSchema (HoistProperty _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (HoistProperty x y) (SObject z) prf = ?assertReverseSchema_rhs_19
assertReverseSchema (PlungeProperty _ _) SFalse ItIsJust impossible
assertReverseSchema (PlungeProperty _ _) SBoolean ItIsJust impossible
assertReverseSchema (PlungeProperty _ _) SNumber ItIsJust impossible
assertReverseSchema (PlungeProperty _ _) SText ItIsJust impossible
assertReverseSchema (PlungeProperty _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (PlungeProperty x y) (SObject z) prf = ?assertReverseSchema_rhs_20
assertReverseSchema WrapProperty _ _ = Refl
assertReverseSchema HeadProperty SFalse ItIsJust impossible
assertReverseSchema HeadProperty SBoolean ItIsJust impossible
assertReverseSchema HeadProperty SNumber ItIsJust impossible
assertReverseSchema HeadProperty SText ItIsJust impossible
assertReverseSchema HeadProperty (SArray False _) prf = Refl
assertReverseSchema HeadProperty (SArray True _) ItIsJust impossible
assertReverseSchema HeadProperty (SObject _) ItIsJust impossible
assertReverseSchema (LensIn _ _) SFalse ItIsJust impossible
assertReverseSchema (LensIn _ _) SBoolean ItIsJust impossible
assertReverseSchema (LensIn _ _) SNumber ItIsJust impossible
assertReverseSchema (LensIn _ _) SText ItIsJust impossible
assertReverseSchema (LensIn _ _) (SArray _ _) ItIsJust impossible
assertReverseSchema (LensIn x y) (SObject z) prf = ?assertReverseSchema_rhs_23
assertReverseSchema (LensMap _) SFalse ItIsJust impossible
assertReverseSchema (LensMap _) SBoolean ItIsJust impossible
assertReverseSchema (LensMap _) SNumber ItIsJust impossible
assertReverseSchema (LensMap _) SText ItIsJust impossible
assertReverseSchema (LensMap lens) (SArray allowEmpty schema) prf =
    let
        mm = lemmaMaybeMap2 (applyLensSchema lens schema) (SArray allowEmpty) prf
        ind = assertReverseSchema lens schema mm
    in ?assertReverseLensMap
assertReverseSchema (LensMap _) (SObject _) ItIsJust impossible
assertReverseSchema (Convert a b m) s prf = ?assertReverseLensConvert

||| If transforming the schema succeeds, transforming the value must succeed
schemaJustImpliesValueJust :
    (lens: Lens) ->
    (schema: Schema) ->
    (value: Value) ->
    (validate schema value = True) ->
    (IsJust (applyLensSchema lens schema)) ->
    (IsJust (applyLensValue lens value))

schemaJustImpliesValueJust (AddProperty _ _ _) SFalse _ _ ItIsJust impossible
schemaJustImpliesValueJust (AddProperty _ _ _) SBoolean _ _ ItIsJust impossible
schemaJustImpliesValueJust (AddProperty _ _ _) SNumber _ _ ItIsJust impossible
schemaJustImpliesValueJust (AddProperty _ _ _) SText _ _ ItIsJust impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SArray _ _) _ _ ItIsJust impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject []) (Object []) _ _ = ItIsJust
schemaJustImpliesValueJust (AddProperty n r v) (SObject []) (Object (x :: xs)) prf ItIsJust = ?schemaJustImpliesValueJust_rhs_40
schemaJustImpliesValueJust (AddProperty _ _ _) (SObject (x :: xs)) (Object []) _ _ = ItIsJust
schemaJustImpliesValueJust (AddProperty n r v) (SObject (x :: xs)) (Object (y :: ys)) prf prf1 = ?schemaJustImpliesValueJust_rhs_39
schemaJustImpliesValueJust (RemoveProperty _ _ _) SFalse _ _ ItIsJust impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) SBoolean _ _ ItIsJust impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) SNumber _ _ ItIsJust impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) SText _ _ ItIsJust impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SArray _ _) _ _ ItIsJust impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (RemoveProperty _ _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (RemoveProperty x y z) (SObject w) (Object v) prf prf1 = ?schemaJustImpliesValueJust_rhs_28
schemaJustImpliesValueJust (RenameProperty _ _) SFalse _ _ ItIsJust impossible
schemaJustImpliesValueJust (RenameProperty _ _) SBoolean _ _ ItIsJust impossible
schemaJustImpliesValueJust (RenameProperty _ _) SNumber _ _ ItIsJust impossible
schemaJustImpliesValueJust (RenameProperty _ _) SText _ _ ItIsJust impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SArray _ _) _ _ ItIsJust impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (RenameProperty _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (RenameProperty x y) (SObject z) (Object w) prf prf1 = ?schemaJustImpliesValueJust_rhs_29
schemaJustImpliesValueJust (HoistProperty _ _) SFalse _ _ ItIsJust impossible
schemaJustImpliesValueJust (HoistProperty _ _) SBoolean _ _ ItIsJust impossible
schemaJustImpliesValueJust (HoistProperty _ _) SNumber _ _ ItIsJust impossible
schemaJustImpliesValueJust (HoistProperty _ _) SText _ _ ItIsJust impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SArray _ _) _ _ ItIsJust impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (HoistProperty _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (HoistProperty x y) (SObject z) (Object w) prf prf1 = ?schemaJustImpliesValueJust_rhs_30
schemaJustImpliesValueJust (PlungeProperty _ _) SFalse _ _ ItIsJust impossible
schemaJustImpliesValueJust (PlungeProperty _ _) SBoolean _ _ ItIsJust impossible
schemaJustImpliesValueJust (PlungeProperty _ _) SNumber _ _ ItIsJust impossible
schemaJustImpliesValueJust (PlungeProperty _ _) SText _ _ ItIsJust impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SArray _ _) _ _ ItIsJust impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SObject _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SObject _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SObject _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (PlungeProperty _ _) (SObject _) (Array _) Refl _ impossible
schemaJustImpliesValueJust (PlungeProperty x y) (SObject z) (Object w) prf prf1 = ?schemaJustImpliesValueJust_rhs_31
schemaJustImpliesValueJust WrapProperty _ _ _ _ = ItIsJust
schemaJustImpliesValueJust HeadProperty SFalse _ _ ItIsJust impossible
schemaJustImpliesValueJust HeadProperty SBoolean _ _ ItIsJust impossible
schemaJustImpliesValueJust HeadProperty SNumber _ _ ItIsJust impossible
schemaJustImpliesValueJust HeadProperty SText _ _ ItIsJust impossible
schemaJustImpliesValueJust HeadProperty (SArray _ _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust HeadProperty (SArray _ _) (Number _) Refl _ impossible
schemaJustImpliesValueJust HeadProperty (SArray _ _) (Text _) Refl _ impossible
schemaJustImpliesValueJust HeadProperty (SArray False _) (Array []) Refl _ impossible
schemaJustImpliesValueJust HeadProperty (SArray False _) (Array (x :: xs)) _ _ = ItIsJust
schemaJustImpliesValueJust HeadProperty (SArray True _) (Array _) _ ItIsJust impossible
schemaJustImpliesValueJust HeadProperty (SArray _ _) (Object _) Refl _ impossible
schemaJustImpliesValueJust HeadProperty (SObject _) _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensIn _ _) SFalse _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensIn _ _) SBoolean _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensIn _ _) SNumber _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensIn _ _) SText _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensIn _ _) (SArray _ _) _ _ ItIsJust impossible
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
schemaJustImpliesValueJust (LensMap _) SBoolean _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensMap _) SNumber _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensMap _) SText _ _ ItIsJust impossible
schemaJustImpliesValueJust (LensMap _) (SArray _ _) (Boolean _) Refl _ impossible
schemaJustImpliesValueJust (LensMap _) (SArray _ _) (Number _) Refl _ impossible
schemaJustImpliesValueJust (LensMap _) (SArray _ _) (Text _) Refl _ impossible
schemaJustImpliesValueJust (LensMap l) (SArray allowEmpty schema) (Array xs) prf prf1 = ?schemaJustImpliesValueJust_rhs_19
schemaJustImpliesValueJust (LensMap _) (SArray _ _) (Object _) Refl _ impossible
schemaJustImpliesValueJust (LensMap _) (SObject _) _ _ ItIsJust impossible
schemaJustImpliesValueJust (Convert a b m) s v prf prf1 = ?schemaJustImpliesValueJustConvert

validateLensed : Lens -> Schema -> Value -> Bool
validateLensed l s v =
    case (applyLensSchema l s, applyLensValue l v) of
        (Just s, Just v) => validate s v
        _ => False

andImpliesA' : (a : Bool) -> (b : Lazy Bool) -> (a && b = True) -> a = True
andImpliesA' False b prf = prf
andImpliesA' True b prf = Refl

andImpliesA : (a && b = True) -> a = True
andImpliesA prf = irrelevantEq $ andImpliesA' a b prf

assertLensLensMap : (IsJust (applyLensSchema (LensMap lens) schema)) -> (IsJust (applyLensSchema lens schema))
assertLensLensMap x = ?assertLensLensMap_rhs

||| Transforming a valid value must result in a valid value
assertLens :
    (lens: Lens) ->
    (schema: Schema) ->
    (value: Value) ->
    (validate schema value = True) ->
    (IsJust (applyLensSchema lens schema)) ->
    (validateLensed lens schema value = True)
assertLens (AddProperty k x y) schema value prf prf1 = ?assertLens_rhs_1
assertLens (RemoveProperty k x y) schema value prf prf1 = ?assertLens_rhs_2
assertLens (RenameProperty k j) schema value prf prf1 = ?assertLens_rhs_3
assertLens (HoistProperty k j) schema value prf prf1 = ?assertLens_rhs_4
assertLens (PlungeProperty k j) schema value prf prf1 = ?assertLens_rhs_5
assertLens WrapProperty SFalse _ Refl _ impossible
assertLens WrapProperty SBoolean _ prf _ = rewrite prf in Refl
assertLens WrapProperty SNumber _ prf _ = rewrite prf in Refl
assertLens WrapProperty SText _ prf _ = rewrite prf in Refl
assertLens WrapProperty (SArray x y) _ prf _ = rewrite prf in Refl
assertLens WrapProperty (SObject xs) _ prf _ = rewrite prf in Refl
assertLens HeadProperty SFalse _ Refl _ impossible
assertLens HeadProperty SBoolean _ _ ItIsJust impossible
assertLens HeadProperty SNumber _ _ ItIsJust impossible
assertLens HeadProperty SText _ _ ItIsJust impossible
assertLens HeadProperty (SArray False _) (Boolean _) Refl _ impossible
assertLens HeadProperty (SArray False _) (Number _) Refl _ impossible
assertLens HeadProperty (SArray False _) (Text _) Refl _ impossible
assertLens HeadProperty (SArray False _) (Array []) Refl _ impossible
assertLens HeadProperty (SArray False s) (Array (x :: xs)) prf _ = andImpliesA prf
assertLens HeadProperty (SArray False _) (Object _) Refl _ impossible
assertLens HeadProperty (SArray True _) _ _ ItIsJust impossible
assertLens HeadProperty (SObject _) _ _ ItIsJust impossible
assertLens (LensIn k x) schema value prf prf1 = ?assertLens_rhs_8
assertLens (LensMap lens) schema value prf isj =
    let
        isj = assertLensLensMap isj
        ind = assertLens lens schema value prf isj
    in ?assertLens_rhs_9
assertLens (Convert a b m) s v prf prf1 = ?assertLensConvert

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
    -}
