Require Import Bool Arith List.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* Comments and source code are derived from the book Certified Programming with Dependent Types by Professor Adam Chlipala available for free at http://adam.chlipala.net/cpdt/. *)

(* We define an inductive datatype binop to stand for the binary operators of our source language *)
Inductive binop : Set := Plus | Times.

(* We write that a constant may be built from one argument, a natural number; and a binary operation may be built from a choice of operator and two operand expressions. *)
Inductive exp : Set := 
    | Const : nat -> exp
    | Binop : binop -> exp -> exp -> exp.

(* The meaning of a binary operator is a binary function over nat referring to the
functions plus and mult from the Coq standard library. *)
Definition binopDenote (b : binop) : nat -> nat -> nat :=
    match b with
        | Plus => plus
        | Times => mult
    end.

(* A simple recursive definition of the meaning of an expression. *)
Fixpoint expDenote (e : exp) : nat := 
    match e with
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
    end.

(* An instruction either pushes a constant onto the stack or pops two arguments, applies a binary operator to them, and pushes the result onto the stack.*)
Inductive instr : Set :=
    | iConst : nat -> instr
    | iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.


(* We can give instructions meanings as functions from stacks to optional stacks, where running an instruction results in None in case of a stack underflow and results in Some s’ when the result of execution is the new stack s’ *)
Definition instrDenote (i : instr) (s : stack) : option stack :=
    match i with
        | iConst n => Some (n :: s)
        | iBinop b => match s with
            | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
            | _ => None
        end
    end.

