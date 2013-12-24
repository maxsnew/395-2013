<<<<<<< Updated upstream
Require Import braun monad log insert.
=======
Require Import braun monad fl_log insert util.
>>>>>>> Stashed changes
Require Import Div2 List.
Require Import Arith.
Set Implicit Arguments.

Section ilist.
  Variable A : Set.
  Variable P : nat -> Set.

  Inductive ilist : nat -> Set :=
  | Nil  : ilist 0
  | Cons : forall n, A -> ilist n -> ilist (S n).
End ilist.

Section ifoldr.
  Variables A : Set.
  Variable B : nat -> Set.
  Variable f : forall n, A -> B n -> B (S n).
  Variable i : B 0.

  Fixpoint ifoldr n (ls : ilist A n) : B n :=
    match ls with
      | Nil => i
      | Cons _ x ls' => f x (ifoldr ls')
    end.
End ifoldr.

Section make_array_naive.
  Variable A : Set.

  (* Not sure how to prove this is O(nlogn) *)
  Fixpoint rt_naive n : nat :=
    match n with
      | 0 => 0
      | S n' => rt_naive n' + (fl_log n' + 1)
    end.

  Example rt_naive_ex :
    map rt_naive (1 :: 2 :: 3 :: 4 ::  5 ::  6 ::  7 ::  8 ::  9 :: 10 :: nil)
               = (1 :: 3 :: 5 :: 8 :: 11 :: 14 :: 17 :: 21 :: 25 :: 29 :: nil).
  compute; reflexivity. Qed.
  
  Program Definition make_array_naive n (s : ilist A n)
  : C (braun_tree A n) (rt_naive n) :=
    ifoldr (fun n => C (braun_tree A n) (rt_naive n))
           (fun n x ct => ct >>= insert x)
           (ret Empty)
           s.
  Obligation 1. omega. Qed.

End make_array_naive.


(* Some subset type notation *)
Notation "[ e ]" := (exist _ e _).
Require Import Arith.Even.
Section make_array_naive'.
  Variable A : Set.

  Definition bnode_cond m1 m2 n : Prop :=
    ((even n /\ m1 = m2) \/ (odd n /\ m1 = S m2)) /\ m1 + m2 = n.

  Lemma div2_double_even : forall n, even n -> div2 n + div2 n = n.
    intros.
    SearchAbout even.
  Admitted.
  
  Lemma div2_double_odd : forall n, odd n -> S (div2 n) + div2 n = n.
    intros.
    SearchAbout even.
  Admitted.

  Definition sep m : { mn : nat * nat | bnode_cond (fst mn) (snd mn) m }.
    refine (
        if even_odd_dec m
        then [ (div2 m, div2 m) ]
        else [ (S (div2 m), div2 m) ]
      ); unfold bnode_cond; simpl; split.
    left. split; [assumption | reflexivity].
    admit.
    right. split; [assumption | reflexivity].
    admit.
  Qed.
  
  Program Fixpoint unravel n (l : ilist A n): forall m1 m2, bnode_cond m1 m2 n -> ilist A m1 * ilist A m2 :=
    match l with
      | Nil => fun _ _ _ => (Nil _ , Nil _)
      | Cons n x xs => fun _ _ _ =>
        let '(odds, evens) := unravel xs (proj2_sig (sep n)) in
        (Cons x evens, odds)
    end.
  Obligation 1. inversion H1. omega.
  Obligation 2. inversion H1. omega.
  Obligation 3. remember (sep n0) as H'. inversion H'. inversion H2.
  inversion H3; clear H3.
  

  
  inversion H1.
  
  
End make_array_naive'.
