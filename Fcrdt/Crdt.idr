module Fcrdt.Crdt

import Fcrdt.Map

%default total

data Val =
      Number Nat
    | Text String
    | Boolean Bool
    | Null
    | Array
    | Object

data Expr : Type where
    EDoc : Expr
    EVar : Key -> Expr
    EGet : Key -> Expr -> Expr
    EIdx : Nat -> Expr -> Expr
    EKeys : Expr -> Expr
    EVal : Expr -> Expr

%name Expr e, e1, e2

data Cmd : Type where
    CLet : Key -> Expr -> Cmd
    CAss : Expr -> Val -> Cmd
    CIns : Val -> Expr -> Cmd
    CDel : Expr -> Cmd
    CYield : Cmd
    CSeq : Cmd -> Cmd -> Cmd

%name Cmd c, c1, c2

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
    object = Object

    array : Val
    array = Array

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
    str s = Text s

    example_program : Cmd
    example_program =
        doc ::= object #
        get shopping doc ::= array #
        let head = idx 0 $ get shopping doc in
            insert (str "eggs") head #
            let eggs = idx 1 $ get shopping doc in
                insert (str "cheese") head #
                insert (str "milk") eggs


data Path = Root | PMap Key | PList Nat

data TPath = TMap Path | TList Path

data Cursor = MkCursor (List TPath) Path

State : Type
State = Map Cursor


eval_expr : State -> Expr -> Maybe Cursor
eval_expr ctx EDoc = Just (MkCursor [] Root)
eval_expr ctx (EVar k) = get k ctx
eval_expr ctx (EGet k e) =
    case eval_expr ctx e of
        Just (MkCursor ps p) => Just (MkCursor ((TMap p) :: ps) (PMap k))
        Nothing => Nothing
eval_expr ctx (EIdx n e) =
    case eval_expr ctx e of
        Just (MkCursor ps p) => Just (MkCursor ((TList p) :: ps) (PList n))
        Nothing => Nothing
eval_expr ctx (EKeys x) = ?eval_expr_rhs_5
eval_expr ctx (EVal x) = ?eval_expr_rhs_6


data CEval : Cmd -> State -> State -> Type where
    E_Exec : CEval c1 st st' -> CEval c2 st' st'' -> CEval (CSeq c1 c2) st st''
    E_Let : CEval (CLet k e) st st -- TODO
    E_Ass : CEval (CAss e v) st st -- TODO
    E_Ins : CEval (CIns v e) st st
    E_Del : CEval (CDel e) st st
    E_Yield : CEval CYield st st
