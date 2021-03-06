Require Import braun util log.
Require Import Coq.Program.Wf.
Require Import Arith Arith.Even Arith.Div2.
Set Implicit Arguments.

Section size.
  Variable A : Set.

  Inductive SizeLinearR : (bin_tree A) -> nat -> nat -> Prop :=
    | SLR_mt :
        SizeLinearR (bt_mt A) 0 0
    | SLR_node :
        forall y s t s_sz s_time t_sz t_time,
          SizeLinearR s s_sz s_time ->
          SizeLinearR t t_sz t_time ->         
          SizeLinearR (bt_node y s t) (s_sz + t_sz + 1) (s_time + t_time + 1).
  Hint Constructors SizeLinearR.

  Theorem size_linear :
    forall bt,
      { sz | exists t, SizeLinearR bt sz t }.
  Proof.
    induction bt as [|y s IS t IT].

    exists 0. eauto.    
    destruct IS as [s_sz IS].
    destruct IT as [t_sz IT].
    exists (s_sz + t_sz + 1).
    destruct IS as [s_time IS].
    destruct IT as [t_time IT].
    exists (s_time + t_time + 1).
    eauto.
  Defined.

  Theorem SizeLinearR_correct_and_time :
    forall bt n,
      Braun bt n ->
      SizeLinearR bt n n.
  Proof.
    induction bt as [|y s IS t IT]; intros n B;
    inversion_clear B; eauto.
  Qed.
  Hint Resolve SizeLinearR_correct_and_time.

  Inductive DiffR : (bin_tree A) -> nat -> nat -> nat -> Prop :=
    | DR_mt :
          DiffR (bt_mt A) 0 0 0
    | DR_single :
        forall x,
          DiffR (bt_node x (bt_mt A) (bt_mt A)) 0 1 1
    | DR_one :
        forall x s t s_df s_time k,
          DiffR s k s_df s_time ->
          DiffR (bt_node x s t) (2 * k + 1) s_df (s_time+1)
    | DR_two :
        forall x s t t_df t_time k,
          DiffR t k t_df t_time ->
          DiffR (bt_node x s t) (2 * k + 2) t_df (t_time+1).
  Hint Constructors DiffR.

  Lemma DiffR_fun :
    forall s m df dt,
      DiffR s m df dt ->
      forall df' dt',
        DiffR s m df' dt' ->
        df = df' /\ dt = dt'.
  Proof.
    intros s m df dt DR.
    induction DR; intros df' dt' DR';
    inversion DR'; subst; clear DR'; try omega;
    replace k0 with k in *; try omega;
    apply IHDR in H5; omega.
  Qed.

  Theorem DiffR_correct_ans :
    forall s m df t,
      DiffR s m df t ->
      (df = 0 \/ df = 1).
  Proof.
    intros s m df t DR.
    induction DR; auto.
  Qed.

  Theorem DiffR_correct_zero :
    forall s m,
      Braun s m ->
      exists t, DiffR s m 0 t.
  Proof.
    intros s m B.
    induction B; eauto.
    
    assert (s_size = t_size \/ s_size = t_size + 1) as CASES; try omega.
    destruct CASES as [EQ|EQ]; subst.

    replace (t_size + t_size + 1) with (2 * t_size + 1); try omega.
    destruct IHB1 as [s_time Ds].
    exists (s_time+1).
    eauto.

    replace (t_size + 1 + t_size + 1) with (2 * t_size + 2); try omega.
    destruct IHB2 as [t_time Dt].
    exists (t_time+1).
    eauto.
  Qed.
  Hint Resolve DiffR_correct_zero.

  Theorem DiffR_correct_one :
    forall s m,
      Braun s (m+1) ->
      exists t, DiffR s m 1 t.
  Proof.
    intros s m B.
    remember (m+1) as n.
    generalize m Heqn. clear m Heqn.
    induction B; intros m Heqn.

    omega.

    destruct s_size as [|s_size];
      destruct t_size as [|t_size].

    exists 1.
    replace m with 0 in *; try omega.
    inversion B1; try omega.
    inversion B2; try omega.
    eapply DR_single.

    destruct (IHB2 m); omega.

    assert (s_size = 0); try omega. subst.
    replace m with 1 in *; try omega.
    destruct (IHB1 0) as [s_time Ds]; try omega.
    exists (s_time+1).
    replace 1 with (2 * 0 + 1); try omega.
    eapply DR_one.
    auto.

    replace m with (S s_size + S t_size) in *; try omega.
    clear Heqn.

    assert (s_size = t_size \/ s_size = t_size + 1) as CASES; try omega.
    destruct CASES as [EQ|EQ]; subst.

    destruct (IHB2 t_size) as [t_time Dt]; try omega.
    exists (t_time+1).
    replace (S t_size + S t_size) with (2 * t_size + 2); try omega.
    eapply DR_two. auto.

    destruct (IHB1 (t_size+1)) as [s_time Ds]; try omega.
    exists (s_time+1).
    replace (S (t_size + 1) + S t_size) with (2 * (t_size + 1) + 1); try omega.
    eapply DR_one. auto.
  Qed.
  Hint Resolve DiffR_correct_one.

  Theorem DiffR_time :
    forall bt n,
      Braun bt n ->
      forall df dt,
        DiffR bt n df dt ->
        dt = fl_log n.
  Proof.
    intros bf n B.
    induction B;
    intros df dt DR.

    inversion_clear DR.
    apply fl_log_zero.

    inversion DR; clear DR; subst.

    omega.

    replace k with s_size in *; try omega.
    rewrite (IHB1 df s_time H6) in *.
    replace (s_size + 0) with s_size; try omega.
    symmetry.
    apply fl_log_odd.

    assert (s_size = t_size \/ s_size = t_size + 1) as CASES; try omega.
    destruct CASES as [EQ|EQ]; subst.

    omega.

    replace k with t_size in *; try omega.
    rewrite (IHB2 df t_time H6) in *; try omega.
    replace (t_size + 0) with t_size; try omega.
    symmetry.
    replace (t_size + t_size + 2) with (t_size + 1 + (t_size + 1)); try omega.
    apply fl_log_even.
  Qed.

  Theorem diff_dec :
    forall bt m,
      { df | exists t, DiffR bt m df t } + 
      { forall df t, ~ DiffR bt m df t }.
  Proof.
    induction bt as [|y s IS t IT]; intros m.

    destruct m as [|m'].
    left. eauto.
    right. intros df t DR. inversion DR.

    destruct m as [|m'].

    destruct s as [|sx ss st];
      destruct t as [|tx ts tt]; eauto; right;
      intros df dt DR;
      inversion DR; clear DR; subst; try omega.

    destruct (even_odd_dec m') as [E | O].

    apply even_2n in E. 
    destruct E as [k E]; subst.
    destruct (IS k) as [ [s_df ISk] | ISk_Fail ].
    left. exists s_df.
    destruct ISk as [s_time ISk].
    exists (s_time+1).
    unfold double.
    replace (S (k + k)) with (2 * k + 1); try omega.
    eauto.

    right. intros df dt DR.
    inversion DR; clear DR; subst.
    unfold double in *.
    replace k0 with k in *; try omega.
    eapply ISk_Fail. apply H5.

    unfold double in *.
    omega.

    apply odd_S2n in O.
    destruct O as [k O]; subst.
    destruct (IT k) as [[t_df ITk] | ITk_Fail ].
    left. exists t_df.
    destruct ITk as [t_time ITk].
    exists (t_time+1).
    unfold double.
    replace (S (S (k + k))) with (2 * k + 2); try omega.
    eauto.

    right. intros df dt DR.
    inversion DR; clear DR; subst;
    unfold double in *.

    omega.

    replace k0 with k in *; try omega.
    eapply ITk_Fail. apply H5.
  Defined.

  Theorem diff_Braun :
    forall bt m,
      (Braun bt m) \/ (Braun bt (m+1)) ->
      exists df t,
        DiffR bt m df t.
  Proof.
    intros bt m [B | B].
    eauto.
    exists 1.
    eauto.
  Qed.

  Theorem diff :
    forall bt m,
      (Braun bt m) \/ (Braun bt (m+1)) ->
      { df | exists t, DiffR bt m df t }.
  Proof.
    intros bt m Bor.
    destruct (diff_dec bt m) as [OK | FAIL].
    eauto.
    apply diff_Braun in Bor.
    assert False; try tauto.
    destruct Bor as [df [t DR]].
    apply FAIL in DR.
    auto.
  Defined.

  Inductive SizeR : (bin_tree A) -> nat -> nat -> Prop :=
    | SR_mt :
        SizeR (bt_mt A) 0 0
    | SR_node :
        forall x s t m t_time s_df s_time,
          SizeR t m t_time ->
          DiffR s m s_df s_time ->
          SizeR (bt_node x s t) (1 + 2 * m + s_df) (s_time + t_time + 1).
  Hint Constructors SizeR.

  Theorem SizeR_correct :
    forall bt n,
      Braun bt n ->
      exists t, SizeR bt n t.
  Proof.
    induction bt as [|y s IS t IT]; intros n B;
    inversion_clear B; eauto.

    clear IS.
    rename H0 into Bs.
    rename H1 into Bt.
    apply IT in Bt.
    destruct Bt as [t_time SRt].

    assert (s_size = t_size \/ s_size = t_size + 1) as CASES; try omega.
    destruct CASES as [EQ|EQ]; subst.

    replace (t_size + t_size + 1) with (1 + 2 * t_size + 0); try omega.
    apply DiffR_correct_zero in Bs.
    destruct Bs as [s_time Ds].
    exists (s_time + t_time + 1).
    eapply SR_node; eauto.

    replace (t_size + 1 + t_size + 1) with (1 + 2 * t_size + 1); try omega.
    apply DiffR_correct_one in Bs.
    destruct Bs as [s_time Ds].
    exists (s_time + t_time + 1).
    eapply SR_node; eauto.
  Qed.

  (* XXX size running time *)

  Theorem SizeR_invert :
    forall bt n,
      Braun bt n ->
      forall m t,
        SizeR bt m t ->
        m = n.
  Proof.
    intros bt n B m t SR.
    induction SR.

    inversion_clear B. auto.

    inversion B; subst; clear B.

  Admitted.

  Theorem SizeR_time :
    forall bt n,
      Braun bt n ->
      forall st,
        SizeR bt n st ->
        st = sum_of_logs n.
  Proof.
    intros bt n B.
    induction B; intros st SR.

    inversion SR; subst; clear SR.
    auto.

    inversion SR; subst; clear SR.
    rename H into BP.
    rename H5 into SR.
    rename H6 into DR.
    rename H4 into EQ.
    replace m with t_size in *; [| symmetry; eapply SizeR_invert; eauto ].
    apply IHB2 in SR. subst.
    destruct (DiffR_correct_ans DR); subst.
    
    replace s_size with t_size in *; try omega.
    apply DiffR_time in DR; auto.
    subst.

    (* XXX Is this true? *)
    admit.
       
    assert (s_size = t_size \/ s_size = t_size + 1) as CASES; try omega.
    destruct CASES as [E|E]; subst.
    omega.
    apply DiffR_time in DR; auto.
    subst.

    (* XXX Possibly we need something like DiffR_time for m+1 *)
  Admitted.

  Lemma SizeR_fun :
    forall s sz st,
      SizeR s sz st ->
      forall sz' st',
        SizeR s sz' st' ->
        sz = sz' /\ st = st'.
  Proof.
    intros s sz st SR.

    induction SR; intros sz' st' SR';
    inversion SR'; clear SR'; subst;
    try (split; omega).

    destruct (IHSR m0 t_time0 H5); subst m0 t_time0.
    destruct (DiffR_fun H H6); subst.
    omega.
  Qed.

  Theorem size_dec :
    forall bt,
      { sz | exists t, SizeR bt sz t } + 
      { forall sz t, ~ SizeR bt sz t }.
  Proof.
    induction bt as [|y s IS t IT].
    eauto.
    clear IS.
    destruct IT as [[m IT] | FAIL ].
    destruct (diff_dec s m) as [[s_df DS] | DFAIL ].
    left. exists (1 + 2 * m + s_df).
    destruct IT as [t_time IT].
    destruct DS as [s_time DS].
    eauto.

    right. intros sz st SR.
    inversion SR; clear SR; subst.
    destruct IT as [t_time' SRt].
    replace m0 with m in *.
    eapply DFAIL. apply H5.
    destruct (SizeR_fun SRt H4); auto.

    right. intros sz st SR.
    inversion SR; clear SR; subst.
    eapply FAIL; apply H4.
  Defined.

  Theorem size :
    forall bt m,
      Braun bt m ->
      { sz | exists t, SizeR bt sz t }.
  Proof.
    intros bt m B.
    destruct (size_dec bt) as [ OK | FAIL ]; eauto.
    assert False; try tauto.
    apply SizeR_correct in B.
    destruct B as [ st SR ].
    eapply FAIL. apply SR.
  Defined.
End size.

(*
Program Definition diff : 
  forall A n (b : braun_tree A n) (m : nat) (P : m <= n <= m+1), 
    C nat (if (eq_nat_dec m n) then (fl_log n) else (cl_log n)) :=
  fun A => fix diff n (b : braun_tree A n) : forall (m : nat) (P : m <= n <= m+1),
                                               C nat (if (eq_nat_dec m n)
                                                      then (fl_log n)
                                                      else (cl_log n)) :=
  match b as b in braun_tree _ n with
    | Empty => fun m P => ret 0
    | Node _ s1_size t1_size _ s1 t1 => 
      fun m P =>
        match m with
          | 0 => ++1; ret 1
          | S m' => 
            if even_odd_dec m
            then (zo <- diff t1_size t1 (div2 (m' - 1)) _;
                  ++1;
                  ret zo)
            else (zo <- diff s1_size s1 (div2 m') _;
                  ++1;
                  ret zo)
        end
  end.

Obligation 1.
inversion H; intuition.
Defined.

Obligation 2.
dispatch_if n o; intuition.
assert (s1_size = 0);[omega|];assert (t1_size = 0);[omega|].
subst;compute;reflexivity.
Defined.

Obligation 6.
dispatch_if n1 o1; dispatch_if o n.

(* case 1 *)
replace (s1_size+t1_size+ 1) with (t1_size+s1_size+1); [|omega].
apply braun_invariant_implies_fl_log_property.
inversion H; apply even_double in H3; unfold double in H3.
omega.

(* case 2 *)
inversion H as [n' EVEN].
apply even_double in EVEN.
unfold double in EVEN.
intuition.

(* case 3 *)
assert (m'=s1_size+t1_size);[omega|]; subst m'.
assert (t1_size = s1_size \/ s1_size = t1_size +1) as TWOCASES; [omega|];
inversion TWOCASES;subst.
  
(* case 3a *)
rewrite double_div2 in o1; intuition.
  
(* case 3b *)
replace (S (t1_size + 1 + t1_size)) with ((S t1_size) + (S t1_size)) in H; [|omega].
apply even_not_odd in H; intuition.

(* case 4 *) 
apply braun_invariant_implies_cl_log_property.
omega.
Defined.

Obligation 4.
dispatch_if n1 o1; dispatch_if n o.

(* case 1 *)
apply braun_invariant_implies_fl_log_property.
omega.

(* case 2 *)
destruct m';[inversion H;inversion H3|]. (* m' is not 0 *)
assert (even m');[inversion H; inversion H3; assumption|].
apply even_double in H2; unfold double in H2.
simpl in n1; rewrite minus_0r in n1.
intuition.

(* case 3 *)
assert (t1_size = s1_size \/ s1_size = t1_size+1) as SIZES1; [omega|]; destruct SIZES1.

(* case 3a *)
subst t1_size.
rewrite n in H.
apply odd_not_even in H.
intuition.

(* case 3b *)
subst s1_size.
assert (m'-1 = t1_size + t1_size); [omega|].
assert (div2(m'-1) = t1_size); [rewrite H2;apply double_div2|].
intuition.

(* case 4 *)
assert (t1_size = s1_size \/ s1_size = t1_size+1) as SIZES1; [omega|]; 
destruct SIZES1; subst s1_size.

(* case 4a *)
apply braun_invariant_implies_cl_log_property.
omega.

(* case 4b *)
assert (t1_size+t1_size+1 = S m' \/ t1_size+t1_size+1 = S (m'+1)) as SIZES2;
  [omega|]; destruct SIZES2; intuition.
rewrite <- H2 in H.
apply odd_not_even in H.
intuition.
Defined.

Obligation 5.
clear b Heq_b wildcard' s1 t1 A.

assert (s1_size = t1_size \/ s1_size = t1_size + 1) as SIZES1; [omega|]; clear l l0.
assert (S m' = s1_size + t1_size + 1 \/ S (m'+1) = s1_size + t1_size + 1) as SIZES2; [omega|]; clear H0 H1.
destruct SIZES1; destruct SIZES2; subst s1_size.

assert (m'=t1_size+t1_size); [omega|].
replace (div2 m') with t1_size; [omega|subst m'; rewrite double_div2; reflexivity].

rewrite plus_comm in H1.
simpl in H1.
rewrite plus_comm in H1.
simpl in H1.
inversion H1.
rewrite H2 in H.
apply even_not_odd in H.
intuition.

rewrite H1 in H.
replace (t1_size+1+t1_size+1) with ((t1_size+1)+(t1_size+1)) in H; [|omega].
apply even_not_odd in H.
intuition.

assert (m'=t1_size +t1_size); [omega|].
subst m'.
rewrite double_div2.
omega.

Defined.

Obligation 3.
clear b Heq_b wildcard' s1 t1 A.

assert (s1_size = t1_size \/ s1_size = t1_size + 1) as SIZES1; [omega|]; clear l l0.
assert (S m' = s1_size + t1_size + 1 \/ S (m'+1) = s1_size + t1_size + 1) as SIZES2; [omega|]; clear H0 H1.
destruct SIZES1; destruct SIZES2; subst s1_size.

rewrite H1 in H.
apply odd_not_even in H.
intuition.

assert (m'-1 = (t1_size-1)+(t1_size-1)); [omega|].
rewrite H0.
rewrite double_div2.
omega.

assert (m'-1 = t1_size+t1_size); [omega|].
rewrite H0.
rewrite double_div2.
omega.

assert (S m' = t1_size+t1_size+1); [omega|].
rewrite H0 in H.
apply odd_not_even in H.
intuition.
Defined.

Program Fixpoint size A (n:nat) (b : braun_tree A n) : C nat (sum_of_logs n) := 
  match b with 
    | Empty => ret 0
    | Node _ s_size t_size P s t =>
      (++1;
       zo <- diff s P ;
       (size_t <- size t ; 
        ret (1 + 2 * size_t + zo)))
  end.

Obligation 1.
clear Heq_b s t b.

dispatch_if n o; subst; rewrite plus_0_r.

rewrite <- sum_of_logs_odd.
rewrite fl_log_odd.
omega.

assert (t_size+1=s_size) as MN; [omega|].
subst s_size.
rewrite <- sum_of_logs_even.
rewrite <- cl_log_even.
omega.

Defined.
*)
