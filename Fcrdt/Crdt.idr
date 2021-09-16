module Fcrdt.Crdt

import Data.List
import Fcrdt.Map

%default total

record OpId where
    constructor MkOpId
    op_id, replica_id : Nat

Eq OpId where
    a == b = a.op_id == b.op_id && a.replica_id == b.replica_id

Ord OpId where
    compare a b = case compare a.op_id b.op_id of
        EQ => compare a.replica_id b.replica_id
        cmp => cmp

data Cursor =
      Root
    | Get Key Cursor
    | Idx Nat Cursor

%name Cursor cursor

data AssignVal =
      AssignBool Bool
    | AssignNumber Nat
    | AssignArray
    | AssignObject

%name AssignVal val

data Mut =
      Insert AssignVal
    | Delete
    | Assign AssignVal

%name Mut mut

record Op where
    constructor MkOp
    id : OpId
    deps : List OpId
    cursor : Cursor
    mut : Mut

%name Op op

Register : Type -> Type
Register a = Map OpId a

%name Register reg

interface Reg a where
    value : AssignVal -> Maybe a

    assign : OpId -> AssignVal -> Register a -> Register a
    assign id v reg =
        case value v of
            Just v => insert id v reg
            Nothing => reg

Reg Bool where
    value (AssignBool b) = Just b
    value _ = Nothing

Reg Nat where
    value (AssignNumber n) = Just n
    value _ = Nothing

reg_apply_op : Reg a => Op -> Register a -> Register a
reg_apply_op (MkOp id [] cursor (Insert v)) reg = reg
reg_apply_op (MkOp id [] cursor Delete) reg = remove id reg
reg_apply_op (MkOp id [] cursor (Assign val)) reg = assign id val reg
reg_apply_op (MkOp id (x :: xs) cursor mut) reg =
    assert_total (reg_apply_op (MkOp id xs cursor mut) (remove x reg))

reg_values : Register a -> List a
reg_values m = mapMaybe (\k => get k m) (keys m)



{-
data Crdt =
      Number (Register Nat)
    | Boolean (Register Bool)
    | Array (List Crdt)
    | Object (Map Key Crdt)



data Val =
      VNumber (Register Nat)
    | VBoolean (Register Bool)
    | VSelect Cursor Crdt
    | VKeys (List Key)

data Expr : Type where
    EDoc : Expr
    EVar : Key -> Expr
    EGet : Key -> Expr -> Expr
    EIdx : Nat -> Expr -> Expr
    EKeys : Expr -> Expr
    EVal : Expr -> Expr

%name Expr e, e1, e2

Ctx : Type
Ctx = Map Key Val

record State where
    constructor MkState
    ctx : Ctx
    crdt : Crdt
    replica_id : Nat
    ops : List OpId
    queue : List Op

data Cmd : Type where
    CSeq : Cmd -> Cmd -> Cmd
    CLet : Key -> Expr -> Cmd
    CAss : Expr -> SimpleVal -> Cmd
    CIns : Expr -> SimpleVal -> Cmd
    CDel : Expr -> Cmd
    CYield : Cmd

%name Cmd c, c1, c2

eval_expr : Expr -> State -> Maybe Val
eval_expr EDoc st = Just (VSelect Root st.crdt)
eval_expr (EVar key) st = get key st.ctx
eval_expr (EGet key expr) st =
    case eval_expr expr st of
        Just (VSelect cur (Object m)) =>
            case get key m of
                Just sel => Just (VSelect (Get key cur) sel)
                Nothing => Nothing
        _ => Nothing
eval_expr (EIdx idx expr) st =
    case eval_expr expr st of
        Just (VSelect cur (Array xs)) =>
            case getAt idx xs of
                Just sel => Just (VSelect (Idx idx cur) sel)
                Nothing => Nothing
        _ => Nothing
eval_expr (EKeys expr) st =
    case eval_expr expr st of
        Just (VSelect cur (Object m)) => Just (VKeys (keys m))
        _ => Nothing
eval_expr (EVal expr) st =
    case eval_expr expr st of
        Just (VSelect cur (Number reg)) => Just (VNumber reg)
        Just (VSelect cur (Boolean reg)) => Just (VBoolean reg)
        _ => Nothing

lamport : List OpId -> Nat
lamport [] = 0
lamport (x :: xs) =
    let max = lamport xs in
        if x.op_id > max then x.op_id else max

make_op_id : State -> OpId
make_op_id st = MkOpId (lamport st.ops) st.replica_id

make_op : State -> Cursor -> Mut -> Op
make_op st cur mut = MkOp (make_op_id st) st.ops cur mut

apply_local : State -> Op -> State
apply_local st op = record { ops $= (op.id ::), queue $= (op ::) } st

eval_cmd : Cmd -> State -> State
eval_cmd (CSeq c1 c2) st = eval_cmd c2 $ eval_cmd c1 st
eval_cmd (CLet key expr) st =
    case eval_expr expr st of
        Just val => record { ctx $= update key (Just val) } st
        _ => st
eval_cmd (CAss expr val) st =
    case eval_expr expr st of
        Just (VSelect cursor tree) =>
            let op = make_op st cursor (Assign val)
            in apply_local st op
        _ => st
eval_cmd (CIns expr val) st =
    case eval_expr expr st of
        Just (VSelect cursor tree) =>
            let op = make_op st cursor (Insert val)
            in apply_local st op
        _ => st
eval_cmd (CDel expr) st =
    case eval_expr expr st of
        Just (VSelect cursor tree) =>
            let op = make_op st cursor Delete
            in apply_local st op
        _ => st
eval_cmd CYield st = ?yield-}


{-
namespace Example
    shopping : Key
    shopping = MkKey 0

    eggs : Key
    eggs = MkKey 1

    cheese : Key
    cheese = MkKey 2

    milk : Key
    milk = MkKey 3

    doc : Expr
    doc = EDoc

    object : Val
    object = VObject

    array : Val
    array = VArray

    get : Key -> Expr -> Expr
    get k e = EGet k e

    insert : Val -> Expr -> Cmd
    insert v e = CIns v e

    idx : Nat -> Expr -> Expr
    idx n e = EIdx n e

    infixr 10 #
    (#): Cmd -> Cmd -> Cmd
    a # b = CSeq a b

    infixr 20 ::=
    (::=) : Expr -> Val -> Cmd
    e ::= v = CAss e v

    str : String -> Val
    str s = VText s

    example_program : Cmd
    example_program =
        doc ::= object #
        get shopping doc ::= array #
        let head = idx 0 $ get shopping doc in
            insert (str "eggs") head #
            let eggs = idx 1 $ get shopping doc in
                insert (str "cheese") head #
                insert (str "milk") eggs-}

data Permutation : List a -> List a -> Type where
    PNil : Permutation [] []
    PSkip : (x : a) -> Permutation xs ys -> Permutation (x :: xs) (x ::ys)
    PSwap : (x, y : a) -> Permutation xs xs -> Permutation (y :: x :: xs) (x :: y :: xs)
    PTrans : {ys : List a} -> Permutation xs ys -> Permutation ys zs -> Permutation xs zs

perm_trans : Permutation a b -> Permutation b a

not_perm : Permutation [1, 1] [1, 2] -> Void

is_perm' : Permutation [1, 2, 4] [4, 2, 1]
is_perm' =
    let base = PSkip 2 (PSwap 4 1 PNil)
    in ?xxxxxxxxxxxxxx --PTrans (PTrans ?h1 ?h3) ?h2

is_perm : Permutation [1, 2, 3, 4] [3, 4, 2, 1]
is_perm =
    let p = PSkip 2 (PSwap 4 1 PNil)
    in ?hhhhh --PSwap 3 2 [1, 2,?is_perm_rhs

data Permutation : List a -> List a -> Type where
    PNil : Permutation [] []
    PSkip : (x : a) -> Permutation xs ys -> Permutation (x :: xs) (x ::ys)
    PSwap : (x, y : a) -> Permutation xs xs -> Permutation (y :: x :: xs) (x :: y :: xs)
    PTrans : {ys : List a} -> Permutation xs ys -> Permutation ys zs -> Permutation xs zs
data History : (n : Nat) -> Type where
    HEmpty : History 0
    HCons : (op : Op) -> (lamport op >= n = True) -> History n -> History (lamport op)
