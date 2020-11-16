Require Import List.
Import ListNotations.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import  Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Bool.Bool.
Require Import Omega.
Require Import Lia.
From Scheduler.Proof Require Import Lib Assumptions JobsAxioms.
From Scheduler.SchedulerMockup Require Import Jobs.
From Scheduler.Model Require Import AbstractTypes AbstractFunctions.

Module EdfPolicyMod (J : JobsAxiomsMod) (Assms : AssumptionsMod J).
  Import J.
  Import Assms.


  Definition idleAt ( t : nat) := bforall (fun i => negb (run  i t)) N.

  
  Definition countersAt(t : nat) :=
    generic_sum (fun i => c i t) (fun _ => true) 0 N.

  Lemma idleAt_countersAt : forall t,
      idleAt  t = true ->  countersAt  (S t) = countersAt  t.
  Proof.
      intros  t Hidle.
      generalize (bforall_forall _ _ Hidle) ;
        clear Hidle; intro Hidle.
      unfold countersAt in *.
      erewrite generic_sum_f_eq 
        with (f2 := fun k =>  c  k t); auto with arith.
      intros k _ HkSN _.
      rewrite c_constant_when_not_running ; auto.
      replace true with (negb false) in Hidle; auto.
      apply negb_inj.
      apply Hidle ; auto.
Qed.
  
  Lemma notidleAt_runAt : forall t,
      idleAt  t = false ->
      exists i, i < N /\ run i t = true /\ 
         forall j, j < N -> j <> i -> run  j t = false.
  Proof.
    unfold countersAt, idleAt ; intros.
    destruct (notbforall_exists _ _ H) as (i & HxN & Hnegb);
      clear H.
    replace false with (negb true) in Hnegb ; auto.
    apply negb_inj in Hnegb. 
    exists i ; repeat split ; auto.
    intros.
    generalize (at_most_one_runs _ _ _ HxN H Hnegb) ; intro Habs.
    case_eq (run  j t) ; intro Hcas ; try reflexivity.
    rewrite Habs in H0 ; auto ; exfalso ; apply H0 ; reflexivity.   
  Qed.

  Lemma runAt_countersAt :
    forall t, 
      (exists i, i < N /\ run i t = true /\ 
         forall j, j < N -> j <> i -> run j t = false) ->
      S (countersAt  (S t)) = countersAt  t.
  Proof.
    intros  t (i & HiN & Hruntrue & Hrunfalse).
    unfold countersAt.
    rewrite generic_sum_index_split with (k :=i); auto with arith.
    symmetry.
    rewrite generic_sum_index_split with (k :=i); auto with arith.
    replace ( generic_sum (fun i0 : nat => c  i0 (S t)) (fun _ : nat => true) 0 i) with ( generic_sum (fun i0 : nat => c  i0 t) (fun _ : nat => true) 0 i).
    {
      replace (generic_sum (fun i0 : nat => c i0 (S t))
                           (fun _ : nat => true) (S i) N) with
        (generic_sum (fun i0 : nat => c  i0 t)
                     (fun _ : nat => true) (S i) N).
      {
        replace (S
    (generic_sum (fun i0 : nat => c i0 t) 
       (fun _ : nat => true) 0 i + c  i (S t) +
     generic_sum (fun i0 : nat => c i0 t) 
       (fun _ : nat => true) (S i) N))
          with
     (generic_sum (fun i0 : nat => c  i0 t) 
       (fun _ : nat => true) 0 i + S (c  i (S t)) +
     generic_sum (fun i0 : nat => c  i0 t)
                 (fun _ : nat => true) (S i) N).
        {
          assert ( c  i t = S (c  i (S t))).
          {
            destruct (c_decreases_when_running  _ _ HiN Hruntrue).
            lia.
          }  
          rewrite H; auto.

        }
        lia.
      }
      apply generic_sum_f_eq; auto with arith.
      intros k Hle HkN _ .
      rewrite c_constant_when_not_running ; auto.
      apply Hrunfalse; auto; try lia.
    }
     apply generic_sum_f_eq; auto with arith.
      intros k Hle HkN _ .
      rewrite c_constant_when_not_running ; auto ; try lia.
      apply Hrunfalse; auto; try lia.
 Qed.


   Lemma notidleAt_countersAt_aux : forall t,
      idleAt  t = false ->  S (countersAt (S t)) = countersAt t.
   Proof.
     intros; apply runAt_countersAt, notidleAt_runAt ; auto.
   Qed.

   Lemma notidleAt_countersAt_gt_0 : forall  t,
      idleAt  t = false ->  countersAt  t > 0.
   Proof.
     intros  t Hidle.
     generalize (notidleAt_countersAt_aux  _ Hidle) ; intro Haux.
     lia.
   Qed.
   
   Lemma notidleAt_countersAt : forall t,
      idleAt  t = false ->  countersAt (S t) = countersAt t -1.
   Proof.
     intros t Hidle.
     generalize (notidleAt_countersAt_aux  _ Hidle) ; intro Haux.
     lia.
  Qed.
   
  Definition idle( l r : nat) := generic_sum (fun _ => 1) (idleAt ) l r.
  

  Lemma idle_idleAt_grows : forall  l r,
      l <= r ->  idleAt r = true -> idle  l (S r) = S (idle l r).
  Proof.
    intros l r Hle Hidle.
    cbn.
    rewrite Hidle.
    replace (l <=? r) with true.
    * reflexivity.
    * symmetry; rewrite Nat.leb_le; auto.
  Qed.

  Lemma idle_notidleAt_stays : forall l r,
      l <= r ->  idleAt r = false -> idle l (S r) = idle l r.
  Proof.
    intros l r Hle Hidle.
    cbn.
    rewrite Hidle.
    reflexivity.
  Qed.

 
  Lemma idle_mono :  forall  l r, l <= r ->  idle  l r <= idle  l (S r).
  Proof.
    intros  l r Hle.
    case_eq (idleAt  r); intro Hidle.
    * rewrite idle_idleAt_grows; auto.
    * rewrite idle_notidleAt_stays; auto.
  Qed.


  Lemma idle_le_interval : forall l r, l <= r -> idle  l r <= r - l.
  Proof.
  intros l r Hle.
  induction Hle.
  * unfold idle;
    rewrite  generic_sum_eq; lia.
  * case_eq (idleAt  m); intro Hidle.
    +
      rewrite idle_idleAt_grows; auto; lia.
    +  rewrite idle_notidleAt_stays; auto; lia.
 Qed.

 Lemma countersAt_interval :  forall l r, l <= r -> countersAt r <= countersAt  l. 
 Proof.
   intros l r Hle.
   induction Hle; auto.
   case_eq (idleAt m); intro Hidle.
   +  rewrite idleAt_countersAt; auto; lia.
   +  rewrite  notidleAt_countersAt; auto; lia.
 Qed.



 Lemma idle_lem_aux : forall  l r,
      l <= r -> r - l -  (idle l r)  =  (countersAt  l) -  (countersAt r) .
  Proof.  
   intros l r Hle.
   induction Hle; intros.
    * unfold idle.
      rewrite  generic_sum_eq ; auto; lia.
    *  case_eq (idleAt  m); intro Hidle.
     +  rewrite idle_idleAt_grows, idleAt_countersAt; auto.
        rewrite <- IHHle.
        clear ;  lia.      
     + rewrite idle_notidleAt_stays ; auto.
       rewrite  notidleAt_countersAt; auto.
      
       replace (countersAt  l - (countersAt  m - 1)) with
           (S (countersAt  l - countersAt  m )).
       -  generalize (countersAt_interval _ _ Hle); intro Hle0.
          generalize (notidleAt_countersAt_gt_0  m Hidle); intro Hgt0.
          generalize (idle_le_interval  _ _ Hle); intro Hle1.
          replace ( S m - l - idle  l m) with (S (m - l - idle  l m)).
          ** rewrite IHHle; reflexivity.
          ** rewrite subs1; auto.
             rewrite IHHle; lia.
           
       - generalize (notidleAt_countersAt_gt_0  m Hidle); intro Hgt0.
         generalize (countersAt_interval  _ _ Hle); intro Hle0.
         lia.    
 Qed.


  Lemma idle_lem : forall  l r,
      l <= r -> idle  l r = r - l - ((countersAt l) - (countersAt r)).
  Proof.  
    intros  l r Hle.
    generalize (idle_lem_aux  _ _ Hle); intro Haux.
    generalize (countersAt_interval  _ _ Hle); intro Hle0.
    generalize (idle_le_interval  _ _ Hle); intro Hle1.
    assert (r - l - idle  l r + idle  l r =  countersAt  l - countersAt  r + idle l r).
    * rewrite Haux; auto.
    * rewrite NPeano.Nat.sub_add in H ; auto.
      rewrite H.   
      rewrite minus_plus; auto.
  Qed.      
  
  
  
  Definition laterAt (t  r: nat) :=
    bexists (fun i => andb (run  i t) (r <? deadline(Jobs i) )) N.

  Definition ctrs_laterAt(t r : nat) :=
    generic_sum (fun i => c i t) (fun i =>  (r <? deadline(Jobs i) )) 0 N.

    
  Lemma not_laterAt_ctrs : forall t r,
      laterAt t r = false ->
      ctrs_laterAt (S t) r = ctrs_laterAt  t r.
 Proof.
      intros  t r Hlater.
      generalize (notbexists_forall _ _ Hlater) ; clear Hlater; intro Hlater.
      unfold ctrs_laterAt in *.
      erewrite generic_sum_f_eq 
        with (f2 := fun k =>  c k t); auto with arith.
      intros k _ HkN Hdead.
      rewrite c_constant_when_not_running ; auto.
      specialize (Hlater _ HkN).
      rewrite Hdead in Hlater.
      rewrite  andb_false_iff in Hlater; intuition; discriminate.
 Qed.
 


  Lemma laterAt_runAt : forall t r,
      laterAt  t r = true ->
      exists i, i < N /\ run i t = true /\ r <? deadline(Jobs i)  = true
       /\   forall j, j < N -> j <> i -> run j t = false.
  Proof.
    unfold laterAt ; intros.
    destruct (bexists_exists _ _ H) as (i & HxN & Hnegb);
      clear H.
    rewrite andb_true_iff in Hnegb ; destruct Hnegb.
    
    exists i ; repeat split ; auto.
    intros.
    generalize (at_most_one_runs  _ _ _ HxN H1 H); intro Habs.
    case_eq (run  j t) ; intro Hcas ; try reflexivity.
    rewrite Hcas in Habs ; auto ; exfalso ; apply H2; rewrite Habs; reflexivity.   
  Qed.

  
  Lemma runAt_ctrs_laterAt :
    forall t r, 
      (exists i, i < N /\ run  i t = true /\ r <? deadline(Jobs i)  = true /\ 
         forall j, j < N -> j <> i -> run  j t = false) ->
      S ( ctrs_laterAt  (S t) r) =  ctrs_laterAt t r.
  Proof.
    intros  t r (i & HiN & Hruntrue & Hdead & Hrunfalse).
    unfold ctrs_laterAt.
    rewrite generic_sum_index_split with (k :=i); auto with arith.
    symmetry.
    rewrite generic_sum_index_split with (k :=i); auto with arith.
    replace (generic_sum (fun i0 : nat => c  i0 (S t))
                         (fun i0 : nat => r <? deadline (Jobs i0)) 0 i) with
        (generic_sum (fun i0 : nat => c  i0 t)
       (fun i0 : nat => r <? deadline (Jobs i0)) 0 i).
    {
      replace (generic_sum (fun i0 : nat => c  i0 (S t))
       (fun i0 : nat => r <? deadline (Jobs i0))
       (S i) N) with
        (generic_sum (fun i0 : nat => c  i0 t)
       (fun i0 : nat => r <? deadline (Jobs i0))
       (S i) N).
      {
        rewrite Hdead.
        replace (S
    (generic_sum (fun i0 : nat => c  i0 t)
       (fun i0 : nat => r <? deadline (Jobs i0)) 0 i +
     c  i (S t) +
     generic_sum (fun i0 : nat => c i0 t)
       (fun i0 : nat => r <? deadline (Jobs i0))
       (S i) N))
          with
    (generic_sum (fun i0 : nat => c  i0 t)
       (fun i0 : nat => r <? deadline (Jobs i0)) 0 i +
      S (c i (S t)) +
     generic_sum (fun i0 : nat => c i0 t)
       (fun i0 : nat => r <? deadline (Jobs i0))
       (S i) N).
        {
          assert ( c  i t = S (c  i (S t))).
          {
            destruct (c_decreases_when_running  _ _ HiN Hruntrue).
            lia.
          }  
          rewrite H; auto.

        }
        lia.
      }
      apply generic_sum_f_eq; auto with arith.
      intros k Hle HkN _ .
      rewrite c_constant_when_not_running ; auto.
      apply Hrunfalse; auto; try lia.
    }
     apply generic_sum_f_eq; auto with arith.
      intros k Hle HkN _ .
      rewrite c_constant_when_not_running ; auto ; try lia.
      apply Hrunfalse; auto; try lia.
 Qed.


  Lemma  laterAt_ctrs_aux : forall t r,
      laterAt t r = true ->  S ( ctrs_laterAt  (S t) r) =  ctrs_laterAt  t r.
  Proof.
    intros ; apply runAt_ctrs_laterAt, laterAt_runAt; auto.
  Qed.

  Lemma laterAt_ctrs_gt_0 :  forall t r,
      laterAt t r = true ->  ctrs_laterAt t r > 0.
  Proof.
  intros; rewrite <- laterAt_ctrs_aux; auto; lia.
  Qed.

  Lemma  laterAt_ctrs : forall  t r,
      laterAt  t r = true ->  ctrs_laterAt  (S t) r =  ctrs_laterAt t r -1 .
  Proof.
    intros; symmetry; rewrite <- laterAt_ctrs_aux; auto; lia.
  Qed.

  
  Definition later ( r' l r : nat) :=
    generic_sum (fun _ => 1) (fun t => laterAt  t r') l r.

  
  Lemma laterAt_later_grows : forall  l r r' ,
      l <= r ->  laterAt  r r' = true -> later r' l (S r) = S (later r' l r).
  Proof.
    intros  l r r' Hle HlaterAt.
    cbn.
    rewrite HlaterAt.
    replace (l <=? r) with true.
    * reflexivity.
    * symmetry; rewrite Nat.leb_le; auto.
  Qed.

  Lemma notLaterAt_later_stays : forall  l r r',
      l <= r ->  laterAt  r r' = false -> later r' l (S r) = later  r' l r.
  Proof.
    intros l r r' Hle Hlat.
    cbn.
    rewrite Hlat.
    reflexivity.
  Qed.

 
  Lemma later_mono :  forall  l r r' , l <= r ->  later r' l r <= later r' l (S r).
  Proof.
    intros l r r' Hle.
    case_eq (laterAt r r'); intro Hlat.
    * rewrite laterAt_later_grows; auto.
    * rewrite notLaterAt_later_stays; auto.
  Qed.


  Lemma later_le_interval : forall l r r', l <= r -> later r' l r <= r - l.
  Proof.
  intros  l r r' Hle.
  induction Hle.
  * unfold later;
    rewrite  generic_sum_eq; lia.
  * case_eq (laterAt  m r'); intro Hlat.
    + rewrite laterAt_later_grows; auto ; lia.
    + rewrite notLaterAt_later_stays; auto; lia.
 Qed.

  Lemma ctrs_laterAt_interval :
    forall l r r', l <= r -> ctrs_laterAt r r'  <= ctrs_laterAt l r' . 
 Proof.
   intros l r r' Hle.
   induction Hle; auto.
   case_eq (laterAt m r'); intro Hlat.
    + rewrite laterAt_ctrs; auto ; lia.
    + rewrite not_laterAt_ctrs; auto; lia.
 Qed.



  
  Lemma later_lem : forall  l r r',
      l <= r ->
      later r' l r =  ctrs_laterAt l r' -  ctrs_laterAt r r'.
  Proof.
   intros  l r r' Hle.
   induction Hle; intros.
   * unfold later.
      rewrite  generic_sum_eq ; auto; lia.
   *  case_eq (laterAt  m r'); intro Hlat.
    +  rewrite laterAt_ctrs, laterAt_later_grows ; auto.
      generalize ( laterAt_ctrs_gt_0 _ _ Hlat); intro Hgt.
      generalize (ctrs_laterAt_interval _ _ r' Hle); intro Hle'.
      rewrite IHHle; lia.
    + rewrite not_laterAt_ctrs, notLaterAt_later_stays ; auto.
  Qed.


  
  
  Definition earlyAt (t  r: nat) :=
    bexists (fun i => andb (run  i t) (deadline(Jobs i) <=? r )) N.

  Definition ctrs_earlyAt( t r : nat) :=
    generic_sum (fun i => c  i t) (fun i =>  (deadline(Jobs i) <=? r )) 0 N.

    
  Lemma not_earlyAt_ctrs : forall  t r,
      earlyAt  t r = false ->
      ctrs_earlyAt (S t) r = ctrs_earlyAt  t r.
 Proof.
      intros  t r Hearly.
      generalize (notbexists_forall _ _ Hearly) ; clear Hearly; intro Hearly.
      unfold ctrs_earlyAt in *.
      erewrite generic_sum_f_eq 
        with (f2 := fun k =>  c  k t); auto with arith.
      intros k _ HkN Hdead.
      rewrite c_constant_when_not_running ; auto.
      specialize (Hearly _ HkN).
      rewrite Hdead in Hearly.
      rewrite  andb_false_iff in Hearly; intuition; discriminate.
 Qed.
 


  Lemma earlyAt_runAt : forall t r,
      earlyAt  t r = true ->
      exists i, i < N /\ run i t = true /\ deadline(Jobs i) <=? r  = true
       /\   forall j, j < N -> j <> i -> run  j t = false.
  Proof.
    unfold earlyAt ; intros.
    destruct (bexists_exists _ _ H) as (i & HxN & Hnegb);
      clear H.
    rewrite andb_true_iff in Hnegb ; destruct Hnegb.
    
    exists i ; repeat split ; auto.
    intros.
    generalize (at_most_one_runs  _ _ _ HxN H1 H); intro Habs.
    case_eq (run  j t) ; intro Hcas ; try reflexivity.
    rewrite Hcas in Habs ; auto ; exfalso ; apply H2; rewrite Habs; reflexivity.  
  Qed.

  
  Lemma runAt_ctrs_earlyAt :
    forall t r, 
      (exists i, i < N /\ run i t = true /\ deadline(Jobs i) <=? r = true /\ 
         forall j, j < N -> j <> i -> run  j t = false) ->
      S ( ctrs_earlyAt  (S t) r) =  ctrs_earlyAt t r.
   Proof.
    intros t r (i & HiN & Hruntrue & Hdead & Hrunfalse).
    unfold ctrs_earlyAt.
    rewrite generic_sum_index_split with (k :=i); auto with arith.
    symmetry.
    rewrite generic_sum_index_split with (k :=i); auto with arith.
    replace (generic_sum (fun i0 : nat => c i0 (S t))
                         (fun i0 : nat =>  deadline (Jobs i0) <=? r) 0 i) with
        (generic_sum (fun i0 : nat => c i0 t)
       (fun i0 : nat =>  deadline (Jobs i0) <=? r) 0 i).
    {
      replace (generic_sum (fun i0 : nat => c  i0 (S t))
       (fun i0 : nat =>  deadline (Jobs i0) <=? r)
       (S i) N) with
        (generic_sum (fun i0 : nat => c  i0 t)
       (fun i0 : nat =>  deadline (Jobs i0) <=? r)
       (S i) N).
      {
        rewrite Hdead.
        replace (S
    (generic_sum (fun i0 : nat => c  i0 t)
       (fun i0 : nat =>  deadline (Jobs i0) <=? r) 0 i +
     c  i (S t) +
     generic_sum (fun i0 : nat => c  i0 t)
       (fun i0 : nat =>  deadline (Jobs i0) <=? r)
       (S i) N))
          with
    (generic_sum (fun i0 : nat => c  i0 t)
       (fun i0 : nat =>  deadline (Jobs i0) <=? r) 0 i +
      S (c i (S t)) +
     generic_sum (fun i0 : nat => c  i0 t)
       (fun i0 : nat =>  deadline (Jobs i0) <=? r)
       (S i) N).
        {
          assert ( c  i t = S (c  i (S t))).
          {
            destruct (c_decreases_when_running  _ _ HiN Hruntrue).
            lia.
          }  
          rewrite H; auto.

        }
        lia.
      }
      apply generic_sum_f_eq; auto with arith.
      intros k Hle HkN _ .
      rewrite c_constant_when_not_running ; auto.
      apply Hrunfalse; auto; try lia.
    }
     apply generic_sum_f_eq; auto with arith.
      intros k Hle HkN _ .
      rewrite c_constant_when_not_running ; auto ; try lia.
      apply Hrunfalse; auto; try lia.
 Qed.


  Lemma  earlyAt_ctrs_aux : forall  t r,
      earlyAt  t r = true ->  S ( ctrs_earlyAt  (S t) r) =  ctrs_earlyAt  t r.
  Proof.
    intros ; apply runAt_ctrs_earlyAt, earlyAt_runAt; auto.
  Qed.

  Lemma earlyAt_ctrs_gt_0 :  forall  t r,
      earlyAt t r = true ->  ctrs_earlyAt t r > 0.
  Proof.
  intros; rewrite <- earlyAt_ctrs_aux; auto; lia.
  Qed.

  Lemma  earlyAt_ctrs : forall  t r,
      earlyAt  t r = true ->  ctrs_earlyAt (S t) r =  ctrs_earlyAt  t r -1 .
  Proof.
    intros; symmetry; rewrite <- earlyAt_ctrs_aux; auto; lia.
  Qed.

  
  Definition early ( r' l r : nat) :=
    generic_sum (fun _ => 1) (fun t => earlyAt t r') l r.

  
  Lemma earlyAt_early_grows : forall  l r r' ,
      l <= r ->  earlyAt r r' = true -> early  r' l (S r) = S (early r' l r).
  Proof.
    intros l r r' Hle HearlyAt.
    cbn.
    rewrite HearlyAt.
    replace (l <=? r) with true.
    * reflexivity.
    * symmetry; rewrite Nat.leb_le; auto.
  Qed.

  Lemma notEarlyAt_early_stays : forall l r r',
      l <= r ->  earlyAt r r' = false -> early r' l (S r) = early r' l r.
  Proof.
    intros  l r r' Hle Hlat.
    cbn.
    rewrite Hlat.
    reflexivity.
  Qed.

 
  Lemma early_mono :  forall  l r r' , l <= r ->  early r' l r <= early r' l (S r).
  Proof.
    intros  l r r' Hle.
    case_eq (earlyAt  r r'); intro Hlat.
    * rewrite earlyAt_early_grows; auto.
    * rewrite notEarlyAt_early_stays; auto.
  Qed.


  Lemma early_le_interval : forall l r r', l <= r -> early r' l r <= r - l.
  Proof.
  intros l r r' Hle.
  induction Hle.
  * unfold early;
    rewrite  generic_sum_eq; lia.
  * case_eq (earlyAt m r'); intro Hlat.
    + rewrite earlyAt_early_grows; auto ; lia.
    + rewrite notEarlyAt_early_stays; auto; lia.
 Qed.

  Lemma ctrs_earlyAt_interval :
    forall l r r', l <= r -> ctrs_earlyAt r r'  <= ctrs_earlyAt l r' . 
 Proof.
   intros l r r' Hle.
   induction Hle; auto.
   case_eq (earlyAt m r'); intro Hlat.
    + rewrite earlyAt_ctrs; auto ; lia.
    + rewrite not_earlyAt_ctrs; auto; lia.
 Qed.


  
  Lemma early_lem : forall  l r r',
      l <= r ->
      early r' l r =  ctrs_earlyAt l r' -  ctrs_earlyAt r r'.
  Proof.
   intros l r r' Hle.
   induction Hle; intros.
   * unfold early.
      rewrite  generic_sum_eq ; auto; lia.
   *  case_eq (earlyAt m r'); intro Hear.
    +  rewrite earlyAt_ctrs, earlyAt_early_grows ; auto.
      generalize ( earlyAt_ctrs_gt_0  _ _ Hear); intro Hgt.
      generalize (ctrs_earlyAt_interval _ _ r' Hle); intro Hle'.
      rewrite IHHle; lia.
    + rewrite not_earlyAt_ctrs, notEarlyAt_early_stays ; auto.
  Qed.


  Lemma idle_not_early :  forall  t r,
       idleAt t = true -> earlyAt t r = false.
  Proof.
    unfold idleAt, earlyAt ; intros t r; intro Hbfor.
    apply  forall_notbexists.
    intros i Hin.
    apply bforall_forall with (i:=i) in Hbfor; auto.
    rewrite andb_false_iff.
    left.
    replace true with (negb false) in Hbfor; auto.
    apply negb_inj ; auto.
  Qed.
  
  Lemma idle_not_later :  forall  t r,
      idleAt  t = true -> laterAt  t r = false.
   Proof.
    unfold idleAt, laterAt ; intros t r; intro Hbfor.
    apply  forall_notbexists.
    intros i Hin.
    apply bforall_forall with (i:=i) in Hbfor; auto.
    rewrite andb_false_iff.
    left.
    replace true with (negb false) in Hbfor; auto.
    apply negb_inj ; auto.
  Qed.


  Lemma early_not_idle :  forall  t r,
      earlyAt t r = true -> idleAt  t = false .
   Proof.
    unfold earlyAt, idleAt ; intros  t r; intro Hbfor.
    apply  exists_notbforall.
    apply bexists_exists in Hbfor; auto.
    destruct Hbfor as (i & HiN & Hrun).
    rewrite andb_true_iff in Hrun; destruct Hrun.
    exists i ; split; auto.
    rewrite H ; auto.
  Qed.

  Lemma early_not_later :  forall  t r,
      earlyAt t r = true -> laterAt t r = false .
  Proof.
    unfold earlyAt, laterAt ; intros t r; intro Hbfor.
    apply bexists_exists in Hbfor; auto.
    destruct Hbfor as (i & HiN & Hrun).
    rewrite andb_true_iff in Hrun; destruct Hrun.
    apply forall_notbexists; intros j HjN.
    rewrite andb_false_iff.
    generalize ( at_most_one_runs  _ _ _ HiN HjN H) ; intro Hij.
    case_eq (run j t) ; intro Hcas.
    * right.
      rewrite leb_le in H0.
      rewrite (Hij Hcas) in H0.
      rewrite PeanoNat.Nat.ltb_ge; auto.
   *  left; auto.
  Qed.



  Lemma later_not_idle :  forall  t r,
      laterAt t r = true -> idleAt  t = false .
   Proof.
    unfold laterAt, idleAt ; intros t r; intro Hbfor.
    apply  exists_notbforall.
    apply bexists_exists in Hbfor; auto.
    destruct Hbfor as (i & HiN & Hrun).
    rewrite andb_true_iff in Hrun; destruct Hrun.
    exists i ; split; auto.
    rewrite H ; auto.
  Qed.


  Lemma later_not_early :  forall  t r,
      laterAt t r = true -> earlyAt  t r = false.
   Proof.
    unfold earlyAt, laterAt ; intros  t r; intro Hbfor.
    apply bexists_exists in Hbfor; auto.
    destruct Hbfor as (i & HiN & Hrun).
    rewrite andb_true_iff in Hrun; destruct Hrun.
    apply forall_notbexists; intros j HjN.
    rewrite andb_false_iff.
    generalize ( at_most_one_runs  _ _ _ HiN HjN H) ; intro Hij.
    case_eq (run  j t) ; intro Hcas.
    * right.
      rewrite ltb_lt in H0.
      rewrite (Hij Hcas) in H0.
      rewrite PeanoNat.Nat.leb_gt; auto.
   *  left; auto.
  Qed.                                                  

  Lemma not_idle_not_later_early : forall t r,
    idleAt t  = false ->
    laterAt t r = false ->
    earlyAt t r = true.
  Proof.
  unfold idleAt, laterAt, earlyAt.  
  intros t r Hidle Hlater.    
  apply exists_bexists.
  apply notbforall_exists in Hidle.
  destruct Hidle as (i & HiN & Hrun). 
  apply notbexists_forall with (i :=i) in Hlater; auto.
  rewrite andb_false_iff in Hlater.   
  destruct Hlater as [Hlater | Hlater ].
  * rewrite Hlater in Hrun ;  discriminate.
  * exists i ; repeat split ; auto.
    rewrite andb_true_iff ; split.
   + replace false with (negb true) in Hrun ; auto; apply negb_inj;
     auto.
   + rewrite PeanoNat.Nat.ltb_ge in Hlater.
     rewrite leb_le; assumption.
Qed.

  Lemma idle_later_early :
    forall  l r r',
      l <= r -> r - l = idle l r + later r' l r + early  r' l r.
  Proof.
  intros l r r' Hle.
  induction Hle; intros.
  * unfold early, later, idle;
      repeat rewrite generic_sum_eq ; auto ; lia.
  *  rewrite idle_lem, later_lem, early_lem in *; auto.
     case_eq (idleAt  m) ; intro Hidle.
     { generalize (idle_not_early  _ r' Hidle) ; intro Hear.
       generalize (idle_not_later  _ r' Hidle) ; intro Hlat.
       rewrite  idleAt_countersAt in *; auto.  
       rewrite not_laterAt_ctrs ; auto.
       rewrite not_earlyAt_ctrs ; auto.
       rewrite <- idle_lem, <- later_lem, <- early_lem in *; auto.
       replace (S m - l) with (S (m -l)) ; try lia.
       rewrite <- idle_lem_aux; auto.
       rewrite IHHle.
       lia; auto.
   }   
   { case_eq (laterAt m r') ; intro Hlat.
     { generalize ( later_not_early  _ _ Hlat) ; intro Hear.
        rewrite  notidleAt_countersAt in *; auto. 
        rewrite laterAt_ctrs in *; auto.
        rewrite not_earlyAt_ctrs in *; auto.
        rewrite <- idle_lem, <- later_lem, <- early_lem in *; auto.
        replace (S m - l) with (S (m -l)) ; [| lia].
       
        rewrite IHHle.
        replace (countersAt  l - (countersAt  m - 1)) with
            (S (countersAt l - countersAt m)).
       + rewrite <- idle_lem_aux; auto.
         replace (ctrs_laterAt  l r' - (ctrs_laterAt  m r' - 1))
           with (S (ctrs_laterAt  l r' - ctrs_laterAt  m r')).
         - rewrite IHHle.
           rewrite <- later_lem; auto.
            lia.
         - generalize ( laterAt_ctrs_gt_0   _ _ Hlat) ;
           intro Hc.
           generalize (ctrs_laterAt_interval  _ _ r' Hle);
           intro Hc'.
          lia.
      + generalize ( notidleAt_countersAt_gt_0  _ Hidle) ;
        intro Hc.
        generalize (countersAt_interval  _ _  Hle);
               intro Hc'.
        lia.
      }
     {
       generalize ( not_idle_not_later_early  _ _ Hidle Hlat) ;
         intro Hear.
        rewrite  notidleAt_countersAt in *; auto. 
        rewrite not_laterAt_ctrs in *; auto.
        rewrite earlyAt_ctrs in *; auto.
        rewrite <- idle_lem, <- later_lem, <- early_lem in *; auto.
        replace (S m - l) with (S (m -l)) ; [| lia].
         replace (countersAt  l - (countersAt  m - 1)) with
            (S (countersAt l - countersAt  m)).
       + rewrite <- idle_lem_aux; auto.
         replace (ctrs_earlyAt  l r' - (ctrs_earlyAt m r' - 1))
           with (S (ctrs_earlyAt  l r' - ctrs_earlyAt  m r')).
         - rewrite IHHle.
           rewrite <- early_lem; auto.
           lia.
         - generalize (earlyAt_ctrs_gt_0   _ _ Hear) ;
           intro Hc.
           generalize (ctrs_earlyAt_interval _ _ r' Hle);
           intro Hc'.
          lia.
      + generalize ( notidleAt_countersAt_gt_0  _ Hidle) ;
        intro Hc.
        generalize (countersAt_interval _ _  Hle);
               intro Hc'.
        lia.
     }  
   }   
  Qed.
  

  
  Definition waiting(i t : nat)  :=
    i < N /\ arrival (Jobs i) <= t /\ c i t > 0 /\ run i t = false.

  (*
  Definition EdfPolicyUpTo(r : nat) :=
    forall (N i t : nat),
      i < N -> t <= r -> run N  i t = true ->
      forall (j : nat),  
            waiting N j t -> deadline (Jobs i) <= deadline (Jobs j).
   *)

  Definition EdfPolicyUpTo(r : nat) :=
     forall i t, i < N -> t <= r -> run  i t = true ->
      forall (j : nat),  
        waiting  j t -> deadline (Jobs i) <= deadline (Jobs j).
  
  Definition EdfPolicy := forall r, EdfPolicyUpTo  r.                         
  
  
  Definition DBF( l r : nat) :nat :=
    generic_sum
      (fun i => duration (Jobs i))
      (fun i =>  (deadline (Jobs i) <=? r)&& (l <=? arrival(Jobs i)))
      0 N.


   Lemma eq1 : forall l r , l <= r ->
    r - l  +  generic_sum (fun i => c  i r) (
                            fun i =>  (deadline(Jobs i) <=? r)) 0 N
    = idle l r + later  r l r + 
             generic_sum (fun i => c i l)
                         (fun i =>  (deadline(Jobs i) <=? r)) 0 N. 
  Proof.
    intros l r Hle.
    rewrite  idle_later_early with (r' := r); auto.
    repeat rewrite <- Nat.add_assoc.
    repeat rewrite Nat.add_cancel_l.
    rewrite plus_comm.
    rewrite early_lem; auto.
    erewrite le_plus_minus; eauto.
    apply ctrs_earlyAt_interval ; auto.          
Qed.


  Lemma eq2_aux : forall l r,
    generic_sum (fun i => c  i l)
                (fun i =>  (deadline(Jobs i) <=? r)) 0 N =
    generic_sum (fun i => c i l)
                (fun i =>  (deadline(Jobs i) <=? r) &&
                           (arrival (Jobs i) <? l)) 0 N +
    generic_sum (fun i => c  i l)
                (fun i =>  (deadline(Jobs i) <=? r) &&
                           (l <=? arrival (Jobs i))) 0 N.
  Proof.
    intros  l r.
    replace (generic_sum (fun i : nat => c  i l)
    (fun i : nat =>
     (deadline (Jobs i) <=? r) &&
     (l <=? arrival (Jobs i))) 0 N) with
    (generic_sum (fun i : nat => c  i l)
    (fun i : nat =>
     (deadline (Jobs i) <=? r) &&
     negb  (arrival (Jobs i) <? l)) 0 N).
    * apply  generic_sum_split ; auto with arith.
    * apply generic_sum_filter_eq ; auto with arith.
      intros.
      
      assert (Heq :  negb (arrival (Jobs k) <? l) =  (l <=? arrival (Jobs k))).
     + case_eq (l <=? arrival (Jobs k)); intro Hcas.
        - rewrite leb_le in Hcas.
          assert (Hf : (arrival (Jobs k) <? l = false)) ; [ | rewrite  Hf;auto ].
          rewrite PeanoNat.Nat.ltb_ge ; auto.
        - rewrite PeanoNat.Nat.leb_gt in Hcas.
          replace false with (negb true); auto.
          assert (Hf : (arrival (Jobs k) <? l = true)) ; [ | rewrite  Hf;auto ].
          apply ltb_lt; auto.
     + rewrite Heq ; auto.
Qed.

  Lemma eq3_aux : forall  l r,  generic_sum (fun i => c  i l)
                (fun i =>  (deadline(Jobs i) <=? r) &&
                           (l <=? arrival (Jobs i))) 0 N = DBF  l r.
  Proof.
    intros l r.
    apply  generic_sum_f_eq ; auto with arith.
    intros k H0K HkN Heq.
    rewrite andb_true_iff in Heq.
    destruct Heq as (Heq1 & Heq2).
    rewrite leb_le in Heq1, Heq2.
    eapply  c_is_duration_upto_arrival; eauto.
  Qed.

 

 Lemma eq3 :  forall  l r, l <= r ->
      r - l +  generic_sum (fun i => c i r) (
                             fun i =>  (deadline(Jobs i) <=? r)) 0 N
      = idle l r + later r l r + DBF  l r +
             generic_sum (fun i => c  i l)
             (fun i =>  (deadline(Jobs i) <=? r) &&  (arrival (Jobs i) <? l)) 0 N.
  Proof.
    intros l r Hle.
    rewrite eq1 ; auto.
    (* repeat rewrite <- plus_assoc ; auto.
    rewrite Nat.add_cancel_l.*)
    rewrite <- eq3_aux, eq2_aux;  lia.
  Qed. 

  
  Lemma min_eq3_aux :  forall l r,
      l <= r ->
      exists l',
        (l' <= l /\ idle  l' r = idle  l r /\ later  r l' r = later r l r) /\
        forall l'',
          l'' <= l ->  idle l'' r = idle  l r -> later  r l'' r = later r l r ->
                       ~ (l'' < l').
  Proof.
    intros  l r Hle.
    assert
      (Hex :
         exists l0,
           l0 <= l /\ idle l0 r = idle  l r /\ later r l0 r = later  r l r);
      [now exists l |]. 
    generalize ( nonempty_set_minimal_elt _ _ lt_wf
     (fun x => x <= l /\ idle x r = idle l r /\ later r x r = later r l r) Hex) ;
      clear Hex; intro Hex.
    destruct Hex as (y & (Hly & Hi & Hl) & Hz).
    exists y ; repeat split ; auto.
  Qed.


    Lemma min_eq3 : forall  l r,
      l <= r ->   EdfPolicyUpTo r ->
      exists l', l' <= l /\ idle  l' r = idle l r /\ later r l' r = later r l r /\
         r - l' + ctrs_earlyAt r r = idle l r + later r l r + DBF l' r .
  Proof.      
    intros  l r Hle Hedf.
    destruct (min_eq3_aux _ _ Hle) as  (y & (Hly & Hi & Hl) & Hz).
    exists y ; repeat split ; auto.
    rewrite eq3; try lia.
    unfold  ctrs_earlyAt.
    case_eq (generic_sum (fun i : nat => c i y)
    (fun i : nat =>
     (deadline (Jobs i) <=? r) &&
     (arrival (Jobs i) <? y)) 0 N) ; intros.
      * rewrite Hi,Hl; auto.
      * exfalso.
        destruct y.
    +rewrite
       generic_sum_filter_eq with (filter2 := fun _ => false) in H;
       auto with arith.
      - rewrite generic_sum_0 in H; auto with arith.
        discriminate.
      -  intros K Hk0 HkN.
         rewrite andb_false_iff.
         right.
         rewrite NPeano.Nat.ltb_ge ; auto with arith.
         + (* from H : at y there is an active task with deadline <= r *)
           assert (Hgen : generic_sum (fun i : nat => c i y)
        (fun i : nat =>
         (deadline (Jobs i) <=? r) &&
         (arrival (Jobs i) <? S y)) 0 N >= S n).
           {rewrite <- H.
             apply generic_sum_f_ge; auto with arith.
             intros k  Hk0 HkN.
             case_eq (run k y) ; intro Hcas.
             * destruct ( c_decreases_when_running  _ _ HkN Hcas); lia.
             *rewrite c_constant_when_not_running; auto with arith.
           }
           clear H.
           replace (generic_sum (fun i : nat => c   i y)
           (fun i : nat =>
            (deadline (Jobs i) <=? r) &&
            (arrival (Jobs i) <? S y)) 0 N)
            with (generic_sum (fun i : nat => c i y)
           (fun i : nat =>
            (deadline (Jobs i) <=? r) &&
            (arrival (Jobs i) <=?  y)) 0 N) in Hgen.
           {
             assert (Hex :  exists j, j < N /\ run j y = true).
             {
               apply sum_arrived_some_running.
               unfold sum_counters_arrived.
               assert
                 (Hge: generic_sum (fun i : nat => c  i y)
                               (fun i : nat =>
                                  arrival (Jobs i) <=? y) 0 N >=
                   generic_sum (fun i : nat => c  i y)
                               (fun i : nat =>
            (deadline (Jobs i) <=? r) && (arrival (Jobs i) <=? y))
                               0 N).
               {
                 apply  generic_sum_filter_ge; auto with arith.
               }
             lia.  
             }
            destruct Hex as ( j & HjN & Hrun).

           assert (Hyl : y <=l) ; try lia.
           apply  (Hz _ Hyl) ; try lia.
            (* amounts to prove not idle at y : *)
             (* because  at y there is a running task  *) 
             - rewrite <- Hi.
               unfold idle.
               rewrite generic_sum_rev_le_S; try lia.
               unfold idleAt.
               rewrite exists_notbforall; auto.
               exists j; split; auto.
               rewrite Hrun ; auto.

               -(* amounts to prove no job with deadline > r runs at y : *)
                (* because  at y there is an active task with deadline <= r 
                and by edf policy assumption.*) 
               rewrite <- Hl.
               unfold later.
               rewrite generic_sum_rev_le_S; try lia.
               unfold laterAt.
               rewrite forall_notbexists ; auto.
               intros i HiN.
               rewrite andb_false_iff.
               case (Nat.eq_dec i j) ; intros ; subst.
               **   right.
                    assert (Hgen' : generic_sum (fun i : nat => c i y)
                           (fun i : nat =>
                            (deadline (Jobs i) <=? r) &&
                            (arrival (Jobs i) <=? y)) 0 N > 0);
                      try lia; clear Hgen.
                    apply  generic_sum_gt_0_ex in Hgen' ;
                      auto with arith.
                    destruct Hgen' as (k & HkN & Hk  &Hc).
                    rewrite andb_true_iff in Hk.
                    destruct Hk as (Hded & Harr).
                    unfold EdfPolicyUpTo in Hedf.
                    
                    assert (Hyr : y <= r) ; try lia.
                    
                    specialize (Hedf  j y HjN Hyr Hrun k).
                    unfold waiting in Hedf.
                    case_eq (run  k y); intro Hcas.
                   ++
                    generalize
                      (at_most_one_runs _ _ y HiN HkN Hrun Hcas);
                      intro ; subst.
                    rewrite leb_le in Hded.
                    rewrite  NPeano.Nat.ltb_ge; auto.
                   ++  rewrite leb_le in Harr.
                        assert
                         (Hded': deadline (Jobs j) <=
                                 deadline (Jobs k));
                         [apply Hedf; repeat split ; auto|].
                        rewrite leb_le in Hded.
                    rewrite  NPeano.Nat.ltb_ge; auto; lia.
                    
               **   left.
                    generalize (at_most_one_runs  _ _ y HiN HjN); intro Htm.
                    rewrite Hrun in Htm ; cbn in Htm.
                    case_eq (run  i y) ; intro Hcas; auto.
                    rewrite Htm in n0; auto ; lia.
            
           }
           {
             apply generic_sum_filter_eq ; auto with arith.
           }
   Qed.

 
  Definition overdue(i t : nat) :=
    i < N /\ c i t > 0 /\ deadline(Jobs i) <= t.

  Lemma overdue_not_idle : forall i r,  overdue i r ->  idleAt r = false.
  Proof.
  unfold overdue, idleAt.
  intros i r (Hi & Hc & Hded).
  apply exists_notbforall.
  assert (Harr : arrival (Jobs i) <= r).
  {
    generalize ( job_arrival_plus_duration_le_deadline i); intro; lia.
  }
  assert (Hrun : exists j, j < N /\ run  j r = true).
  {
    apply sum_arrived_some_running.
    apply generic_sum_rev_gt_0_ex; auto with arith.
    exists i ; repeat split ; auto with arith.
    rewrite leb_le; auto.
  }
  destruct Hrun as (j & Hj & Hrun).
  exists j ; split ; auto.
  rewrite Hrun ; auto.
  Qed.

  Lemma overdue_not_later :
    forall  i r,
      overdue  i r ->
      EdfPolicyUpTo r ->
      laterAt r r = false.

  Proof.
  unfold overdue, laterAt, EdfPolicyUpTo.
  intros i r  (Hi & Hc & Hded) Hedf.
   assert (Harr : arrival (Jobs i) <= r).
  {
    generalize ( job_arrival_plus_duration_le_deadline i); intro; lia.
  }
  assert (Hrun : exists j, j < N /\ run j r = true).
  {
    apply sum_arrived_some_running.
    apply generic_sum_rev_gt_0_ex; auto with arith.
    exists i ; repeat split ; auto with arith.
    rewrite leb_le; auto.
  }
  destruct Hrun as (j & Hj & Hrun).
  assert (Hr : r <=r); auto.
  specialize (Hedf  _ _ Hj Hr Hrun); clear Hr.
  apply forall_notbexists.
  intros.
  rewrite andb_false_iff.
  case (Nat.eq_dec i j); intros ; subst.
  *  case (Nat.eq_dec i0 j); intros ; subst.
     + right.
       rewrite NPeano.Nat.ltb_ge ; auto with arith.
     + left.
       case_eq (run  i0 r) ; intros ; auto.
       exfalso; apply n.
       apply at_most_one_runs with (t:=r) ; auto.
  * specialize (Hedf i).
    case_eq (run  i r) ; intros.
     + exfalso; apply n.
       eapply at_most_one_runs; eauto.
     +  
    unfold waiting in Hedf.
    assert (Hded' : deadline (Jobs j) <=  deadline (Jobs i));
      [ apply Hedf; repeat split; auto |].
     case (Nat.eq_dec i0 j); intros ; subst.         
      -  right.
         rewrite NPeano.Nat.ltb_ge ; lia.
      -   case_eq (run i0 r) ; intros ; auto.
       exfalso; apply n.
       assert (j = i0); [eapply at_most_one_runs; eauto |]; subst; lia.
  Qed.

  
  Definition feasible := forall l r,l <= r -> DBF l r <= r - l.


  
  Theorem EdfPolicyMainTheorem :
    feasible ->
    forall ( i r: nat),
      EdfPolicyUpTo  r -> ~overdue  i r.
  Proof.  
   intros Hsched  i r Hedf Hover.
   generalize (overdue_not_idle  _ _ Hover) ; intro HidleAt.
   generalize (overdue_not_later  _ _ Hover Hedf) ; intro HlaterAt.
   assert (Hr : r <= r)  ; auto.
   generalize (min_eq3  _ _ Hr Hedf) ; intro Hmin.
   destruct Hmin as (l' & Hl'r & Hidleeq & Hlatereq & Hdiff).
   assert (His0: idle  r r = 0) ; [rewrite idle_lem ; auto ; lia |].
   rewrite His0 in Hdiff ; cbn in Hdiff; clear His0.
   assert (His0: later r r r = 0) ; [rewrite later_lem ; auto ; lia |].
   rewrite His0 in Hdiff ; cbn in Hdiff; clear His0.
   generalize (not_idle_not_later_early  _ _ HidleAt HlaterAt); intro Hearly.
   generalize (earlyAt_ctrs_gt_0 _ _ Hearly); intro Hgt.
   specialize (Hsched  _ _ Hl'r).
   lia.
 Qed.

End EdfPolicyMod.       
