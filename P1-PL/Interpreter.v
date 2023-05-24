(** * An Evaluation Function for Imp *)


(** Taken from the chapter Imp:
  https://softwarefoundations.cis.upenn.edu/lf-current/ImpCEvalFun.html

    It might be a good idea to read the chapter before or as you
    develop your solution.
*)

From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
Import Nat.
From Coq Require Import Arith.EqNat.
From FirstProject Require Import Imp Maps.

(* Let's import the result datatype from the relational evaluation file *)
From FirstProject Require Import RelationalEvaluation.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)


Notation "'LETOPT' (x,y) <== e1 'IN' e2"
   := (match e1 with
         | Some (x,y) => e2
         | None => None
       end)
   (right associativity, at level 60).


(** 2.1. TODO: Implement ceval_step as specified. To improve readability,
               you are strongly encouraged to define auxiliary notation.
               See the notation LETOPT commented above (or in the ImpCEval chapter).
*)

Fixpoint ceval_step (st : state) (c : com) (i : nat): option (state*result) :=
  match i with
  | O => None
  | S i' =>
    match c with
        | <{ break}> =>
            Some (st , SBreak)
        | <{ skip }> =>
            Some (st, SContinue)
        | <{ l := a1 }> =>
            Some ((l !-> aeval st a1 ; st),SContinue)
        | <{ c1 ; c2 }> =>
            match ceval_step st c1 i' with
            | Some (st1, SBreak) => Some (st1, SBreak)
            | None => None
            | Some (st1, SContinue) => ceval_step st1 c2 i'
            end
        | <{ if b then c1 else c2 end }> =>
            if (beval st b)
              then ceval_step st c1 i'
              else ceval_step st c2 i'
        | <{ while b1 do c1 end }> =>
            (if (beval st b1)
            then match ceval_step st c1 i' with
            | Some (st', SContinue) => ceval_step st' c i'
            | _ => Some (st, SContinue)
            end
            else Some (st ,SContinue))
    end 
  end.

(* The following definition is taken from the book and it can be used to
   test the step-indexed interpreter. *)
Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some (st, _) => Some (st X, st Y, st Z)
  end.

Example example_test_ceval :
     test_ceval empty_st

     <{ X := 2;
        if (X <= 1)
        then Y := 3
        else Z := 4
        end }>

     = Some (2, 0, 4).
Proof. reflexivity. Qed.


(** 
  2.2. TODO: Prove the following three properties.
             Add a succint explanation in your own words of why `equivalence1` and `inequivalence1` are valid.
*)
Theorem equivalence1: forall st c,
(exists i0,
forall i1, i1>=i0 ->
ceval_step st <{ break; c }> i1
=
ceval_step st <{ break; skip }> i1
).
Proof.
intros.
exists 2.
intros. 
destruct i1;try lia.
destruct i1;try lia.
simpl.
reflexivity.
Qed.

Theorem inequivalence1: forall st c,
(exists i0,
forall i1, i1>=i0 ->
ceval_step st <{ break; c }> i1
<>
ceval_step st <{ skip }> i1
).
Proof.
intros.
exists 2.
intros. 
destruct i1;try lia.
destruct i1;try lia.
simpl.
injection.
discriminate.
Qed.

Theorem p1_equivalent_p2: forall st,
  (exists i0,
    forall i1, i1>=i0 ->
      ceval_step st p1 i1 = ceval_step st p2 i1
  ).
Proof.
intros.
exists 6.
intros. 
destruct i1;try lia.
destruct i1;try lia.
destruct i1;try lia.
destruct i1;try lia.
destruct i1;try lia.
destruct i1;try lia.
simpl.
reflexivity.
Qed.
