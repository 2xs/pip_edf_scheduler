Require Import List.
Require Import Classical.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Lia.

From Coq.Arith Require Import Compare_dec EqNat Gt Le PeanoNat.

From Scheduler.Proof Require Import Lib Assumptions JobsAxioms EdfPolicy.
From Scheduler.Model Require Import PureFunctionModels.
From Scheduler.Model.Interface.Types Require Import TypesModel Jobs.


Module FunctionalEdfImplementsAssumptionsMod (J :JobsAxiomsMod) <: AssumptionsMod J.
Import J.

Definition init : State := mk_State 0 [].


Definition functional_update_entries(s:State) : ((option nat *bool)* State) :=
  let  l :=
     filter (fun j =>  j <? N) (jobs_arriving_at s.(now))  in
let b := 
     match hd_error s.(active) with
     | Some e =>
         let j := Jobs (id e) in
         (cnt e <=? budget j - duration j)
     | None => false
     end
in
let active1 := if b  then tl s.(active) else s.(active) in
let active2 :=
       insert_all Entry
         (fun e1 e2 : Entry =>
          deadline (Jobs (id e1)) <=? deadline (Jobs (id e2)))
         (map
            (fun j  =>
             {|
             id :=  j;
             cnt := budget (Jobs j);
             del :=  (deadline (Jobs j) - (arrival (Jobs j))) |}) l) active1 in
( match active2 with
     | [] => (None, false )
     | e :: _ => (Some (id e), del e =? 0)
  end,  mk_State  s.(now) active2).

Definition decrease_all_del_func(l : list Entry) := map (fun e => {|
      id := e.(id);
      cnt := e.(cnt);
      del := pred e.(del)
     |}) l.

Definition functional_update_counters (s:State) :
  unit * State :=
  let active3 :=
       match s.(active) with
       | [] => []
       | e :: es =>
           {|
           id := id e;
           cnt := Init.Nat.pred (cnt e);
           del := del e |} :: es
       end in
let active4 :=  (decrease_all_del_func active3) in
  (tt, mk_State (S s.(now))  active4 ).




Definition functional_scheduler  (s: State)  :=
  let (r,s')  := functional_update_entries  s in
  let (_,s'') := functional_update_counters  s' in
  (r,s'').


Fixpoint running (t : nat) : (option nat * bool *State) :=
  match t with
    0 => functional_update_entries init
  | S t' => let (_,s') := running  t' in
            let (_,s'') := functional_update_counters  s' in
            functional_update_entries s''
  end.


(* for better controlled rewriting *)
Lemma running_0 :  running  0 = functional_update_entries  init.
Proof.
intros;
reflexivity.
Qed.

Lemma running_S : forall t,
    running (S t) = let (_,s') := running t in
            let (_,s'') := functional_update_counters  s' in
            functional_update_entries  s''.
Proof.
intros; reflexivity.
Qed.

Lemma  update_counters_changes_now :
  forall s o s', functional_update_counters s = (o, s') ->
                   now s' = S (now s).
Proof.
 intros.
 injection H; intros.
 rewrite <- H0; auto.
Qed.

Lemma update_entries_leaves_now :
  forall  s o s', functional_update_entries s = (o, s') ->
                   now s' = now s.
 Proof.
 intros.
 injection H; intros.
 rewrite <- H0; auto.
Qed.

Lemma time_counter_now:
  forall  t o s,  running  t = (o,s) ->  now s = t.
Proof.
  induction t; intros.
  * rewrite running_0 in H.
    remember (functional_update_entries  init) as rbs.
    destruct rbs as ((a & b) & c).
    cbn in H.
    injection H ; intros ; subst ; clear H.
    rewrite surjective_pairing in Heqrbs.
    rewrite pair_equal_spec in Heqrbs.
    destruct Heqrbs as (_ & Hs).
    rewrite Hs; auto.
  * rewrite running_S in H.
    case_eq (running t); intros.
    rewrite H0 in *.
    case_eq (functional_update_counters s0); intros.
    rewrite H1 in H.
    specialize (IHt _ _ (eq_refl _)).
    rewrite <- IHt.
    case_eq (functional_update_entries  s1) ; intros.
    rewrite H2 in H ; cbn in H.
    destruct p.
    injection H ; intros; subst.
    erewrite update_entries_leaves_now; eauto.
    erewrite update_counters_changes_now; eauto.
Qed.

Lemma ids_after_update_entries : forall s o b s' e',
    functional_update_entries s = ((o,b),s') ->
    In e' (active s') ->
       In (id e') ( filter (fun j =>  j <? N) (jobs_arriving_at s.(now)))
         \/
       In e' (active s).
Proof.
intros s o b s' e' Hfss Hin.
unfold functional_update_entries in Hfss.
remember  (insert_all Entry
              (fun e1 e2 : Entry =>
               deadline (Jobs (id e1)) <=? deadline (Jobs (id e2)))
              (map
                 (fun j : CNat =>
                  {|
                  id := j;
                  cnt := budget (Jobs j);
                  del := deadline (Jobs j) - arrival (Jobs j) |})
                 (filter (fun j : nat => j <? N) (jobs_arriving_at (now s))))
              (if
                match hd_error (active s) with
                | Some e =>
                    cnt e <=? budget (Jobs (id e)) - duration (Jobs (id e))
                | None => false
                end
               then tl (active s)
               else active s)) as ins.
destruct ins.
* injection Hfss ; intros; subst; clear Hfss.
   inversion Hin.
* injection Hfss ; intros; subst; clear Hfss.
  cbn [active] in Hin.
  rewrite Heqins in Hin.
  rewrite <- insert_all_contents_iff in Hin;
  destruct Hin as [ Hin | Hin].
 +
   rewrite in_map_iff in Hin.
   destruct Hin as (i & Heqe & Hin).
   apply f_equal with (f := id) in Heqe.
   cbn in Heqe.
   rewrite Heqe in *; auto.
 +
   right.
   remember (active s) as acs.
   destruct acs.
   - inversion Hin.
   - cbn in Hin.
          destruct 
            (cnt e0 <=?
             budget (Jobs (id e0)) - duration (Jobs (id e0))) ; auto.
          apply in_tl ; auto.
Qed.

Lemma ids_after_update_counters : forall s r s' e',
  functional_update_counters s = (r,s') ->
  In e' (active s') ->
   exists e,  In e (active s) /\ id e = id e' /\ del e' = del e - 1.
Proof.
intros s r s' e' Hfss Hin.
unfold functional_update_counters in Hfss.
injection Hfss ; intros ; subst ; clear Hfss.
cbn in Hin.
remember (active s) as as0.
destruct as0.
* inversion Hin.
* cbn in Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as [Heq | (e'' & Heq & Hin)].
  +
     generalize Heq ; intro Heq'.
     apply f_equal with (f := id) in Heq.
     apply f_equal with (f := del) in Heq'.
     cbn in Heq, Heq'.
     exists e; cbn ; repeat split ; auto ; lia.
  +
     generalize Heq ; intro Heq'.
     apply f_equal with (f := id) in Heq.
     apply f_equal with (f := del) in Heq'.
    cbn in Heq, Heq'.
    exists e'' ; cbn ; repeat split ; auto ; lia.
Qed.


Lemma active_from_earlier_arrivals : forall  t o s,
    running t = (o,s) ->
    forall e,
      In e (active s) ->
          exists t', t' <= t /\
                     In (id e)
                        (filter (fun j => j <? N) (jobs_arriving_at t')).
Proof.
induction t; intros (o,b)  s Hrun e Hin.
*
  rewrite running_0 in Hrun.
  exists 0 ; split; auto.
  apply ids_after_update_entries with (e' := e) in Hrun; auto.
  inversion Hrun; auto.
  inversion H.
*
  rewrite running_S in Hrun.
  case_eq (running t) ; intros (o',b') sr Hr; rewrite Hr in *.
  case_eq (functional_update_counters sr) ; intros oc sc Hc; rewrite Hc in *.
  apply ids_after_update_entries with (e' := e) in Hrun ; auto.
  destruct Hrun as [Hin' | Hin'].
 +
   exists (S t) ; split ; auto.
   replace t with (now sr) ; [| apply time_counter_now with (o := (o',b')); auto].
   apply update_counters_changes_now in Hc.
   rewrite <- Hc ; auto.
 +
   apply ids_after_update_counters with (e' := e) in Hc ; auto.
   destruct Hc as (e' & Hin'' & Heqid & _).

   specialize (IHt _ _ (eq_refl _ ) e' Hin'').
   rewrite <- Heqid.
   destruct IHt as (t' & Hle & Hin''').
   exists t' ; split; auto.
Qed.

Definition run(i t : nat) : bool :=
  match  running  t with 
        (None, _,_) => false
       | (Some k, _,_) =>   (Nat.eqb i k)
  end.

Fixpoint c (i t : nat) : nat :=
  match t with
      0 => duration (Jobs i)
    | S t' => if run i t'  then (c i t') - 1 else c  i t'
  end.

Lemma  at_most_one_runs: forall (i j t : nat),
      i < N -> j < N ->
      run i t  = true -> run j t = true -> i = j.
Proof.
  intros  i j t HiN HjN Hruni Hrunj.
  unfold run in *.
  case_eq (running t) ; intros.
  rewrite H in *.
  destruct p.
  destruct o; try discriminate.
  rewrite Nat.eqb_eq in * ; subst ; auto.
Qed.


Lemma ue_return_is_first: forall s n b s',
    functional_update_entries s = (Some n, b, s')  ->
    exists e es,  s'.(active) = e::es  /\ e.(id) = n.
Proof.
intros s n b s' He.
unfold functional_update_entries in He.
remember ( insert_all Entry
            (fun e1 e2 : Entry =>
             deadline (Jobs (id e1)) <=? deadline (Jobs (id e2)))
            (map
               (fun j : CNat =>
                {|
                id := j;
                cnt := budget (Jobs j);
                del := deadline (Jobs j) - arrival (Jobs j) |})
               (filter (fun j : nat => j <? N) (jobs_arriving_at (now s))))
            (if
              match hd_error (active s) with
              | Some e =>
                  cnt e <=? budget (Jobs (id e)) - duration (Jobs (id e))
              | None => false
              end
             then tl (active s)
             else active s)) as ins.
destruct ins.
* inversion He.
* inversion He ; subst ; clear He.
  exists e, ins; repeat split; auto.
Qed.

Lemma running_is_first: forall t n b s,
    running  t = (Some n, b, s)  ->
    exists e es,  s.(active) = e::es  /\ e.(id) = n.
Proof.
 intros t n b s Hrun.
destruct t.
* rewrite running_0 in Hrun.
  eapply ue_return_is_first; eauto.
*
  rewrite running_S in Hrun.
  remember (running t) as rs ; destruct rs as ((o' & b') & s').
  remember (functional_update_counters s') as rs ; destruct rs as (r & s'').
   eapply ue_return_is_first; eauto.
Qed.


Lemma run_after_arrival :
  forall ( i t : nat), i < N ->
         run i t = true -> arrival (Jobs i) <= t.
Proof.
intros i t HiN Hrun.
unfold run in Hrun.
case_eq (running t) ; intros o' s Hrunning.
rewrite Hrunning in Hrun.
destruct o'; destruct o ; try discriminate.
rewrite Nat.eqb_eq in Hrun.
rewrite <- Hrun in *; clear Hrun.
destruct ( running_is_first  _ _ _ _ Hrunning) as (e & es & Heqe & Hine).
rewrite <- Hine in *; clear Hine.
generalize (in_eq e es) ; intro Hin.
rewrite <- Heqe in Hin.
destruct (active_from_earlier_arrivals  _ _ _ Hrunning _ Hin)
  as (t' & Hle' & Hin').
rewrite filter_In in Hin'.
destruct Hin' as (Hin' & Hlt).
rewrite jobs_arriving_at_prop in Hin'; rewrite Hin' ; auto.
Qed.

Lemma c_is_duration_upto_arrival :
  forall (i t : nat), i < N ->  t <= arrival (Jobs i) ->
                        c  i t = duration (Jobs i).
Proof.
  intros i.
  induction t ; intros HiN Ht.
  * reflexivity.
  * cbn.
    case_eq (run i t) ; intros Hcas.
  +  exfalso.
     specialize (run_after_arrival  _ _ HiN Hcas); intro Hge;lia.
  +  rewrite IHt; auto  ; lia.
Qed.


Lemma uc_effect_on_active : forall s s' r',
functional_update_counters s = (r',s') ->
map id (active s') = map id (active s).
Proof.
intros s s' r' Hfss.
unfold functional_update_counters in Hfss.
apply f_equal  with (f := snd) in Hfss ; cbn in Hfss.
remember (active s) as acts.
destruct acts.
* destruct s' ; cbn in *.
   injection Hfss  ; intros ; subst ; auto.
*  destruct s' ; cbn in *.
   destruct (Init.Nat.pred (cnt e)).
  +
    injection Hfss  ; intros ; subst; clear Hfss.
    cbn in *.
    f_equal.
    rewrite map_map.
    reflexivity.
 +
    assert( Hn : S n <> 0) ; auto.
    rewrite <- Nat.eqb_neq in Hn.
    injection Hfss  ; intros ; subst.
    cbn.
    rewrite map_map.
    reflexivity.
Qed.

Lemma active_id_after_uc_subset  : forall s s' r' e,
    functional_update_counters s = (r',s') ->
    In (id e) (map id (active s')) -> In (id e) (map id (active s)) .
Proof.
intros s s' r' e He Hin.
apply uc_effect_on_active in He.
rewrite He in Hin ; auto.
Qed.


Lemma uc_preserves_unique_id : forall s s' r',
    functional_update_counters s = (r',s') ->
    unique_for id (active s) ->
    unique_for id (active s').
Proof.
intros s s' r' Hc Hu.
unfold unique_for in *.
apply uc_effect_on_active in Hc.
rewrite Hc ; auto.
Qed.

Lemma ue_preserves_unique_id : forall s r s',
  functional_update_entries s = (r,s') ->
  unique_for id (active s) ->
   (forall e,   In (id e)
                   (filter (fun j => j <? N) (jobs_arriving_at (now s)))
                -> ~In (id e) (map id (active s)))
   ->
      unique_for id (active s').
Proof.
  intros s r s' Hue Hu HH.
  unfold functional_update_entries in Hue.
  remember  (insert_all Entry
             (fun e1 e2 : Entry =>
              deadline (Jobs (id e1)) <=? deadline (Jobs (id e2)))
             (map
                (fun j : CNat =>
                 {|
                 id := j;
                 cnt := budget (Jobs j);
                 del := deadline (Jobs j) - arrival (Jobs j) |})
                (filter (fun j : nat => j <? N) (jobs_arriving_at (now s))))
             (if
               match hd_error (active s) with
               | Some e =>
                   cnt e <=? budget (Jobs (id e)) - duration (Jobs (id e))
               | None => false
               end
              then tl (active s)
              else active s)) as ins.
destruct ins.
  * inversion Hue ; subst; clear Hue.
    cbn.
    apply NoDup_nil.
  *
    inversion Hue ; subst; clear Hue.
    cbn.
    rewrite Heqins; clear Heqins e.
    eapply insert_all_unique.
    +
      intros e Hin1 Hin2.
      rewrite map_map in Hin1.
      cbn in Hin1.
      rewrite in_map_iff in Hin1.
      destruct Hin1 as (i & Heqi & Hin1).
      cbn in HH.
      rewrite Heqi in * ; clear Heqi.
      specialize (HH _ Hin1) ; clear Hin1.
      apply HH.
      destruct (active s) ; auto.
      cbn in Hin2.
      destruct ((cnt e0 <=?
                 budget (Jobs (id e0)) - duration (Jobs (id e0)))); auto.
      apply in_tl; auto.
    +
      unfold CNat, unique_for.
      rewrite map_map, map_id.
      apply NoDup_filter.
      rewrite NoDup_nth with (d := 0).
      intros i j Hi Hj Heq.
      destruct (jobs_arriving_at_unique _ _ _ _ Hi Hj Heq); auto.
     +
      destruct (active s) ; auto.
      cbn.
      destruct ((cnt e <=?
                 budget (Jobs (id e)) - duration (Jobs (id e)))); auto.
       inversion Hu ; subst; auto.
Qed.

Lemma active_unique_for_id :
  forall t r s,  running t = (r,s) ->  unique_for id (active s).
Proof.
induction t ; intros (o,b) s Hrun.
* rewrite running_0 in Hrun.
  eapply ue_preserves_unique_id ; eauto.
  apply NoDup_nil.
* 
  rewrite running_S in Hrun.
  case_eq  (running  t); intros (o'&b')  s' Hr.
  rewrite Hr in Hrun.
  case_eq (functional_update_counters s'); intros o'' s'' Hc.
  rewrite Hc in Hrun.
  remember (functional_update_entries  s'') as rbs.
  rewrite Hrun in * ; clear Hrun.
  symmetry in Heqrbs.
  specialize (IHt _ _ Hr).
  generalize Hc ; intro Hc'.
  generalize (active_from_earlier_arrivals  _ _ _ Hr) ; intros He. 
  eapply uc_preserves_unique_id in Hc; eauto.
  eapply ue_preserves_unique_id in Hc; eauto.
  intros e Hin Hin'.
  rewrite in_map_iff in Hin'.
  destruct Hin' as (e' & Heqid & Hin').
  apply in_map with (f := id) in Hin'.
  eapply  active_id_after_uc_subset in Hin' ; eauto.
  rewrite Heqid in *; clear Heqid e'.
  rewrite in_map_iff in Hin'.
  destruct Hin' as (e' & Heqid & Hin').
  destruct (He _ Hin') as (t' & Hle & Hin''); clear He.
  apply time_counter_now in Hr.
  apply update_counters_changes_now in Hc'.
  rewrite Hr in Hc'.
  rewrite Hc' in Hin.
  rewrite Heqid in *.
  rewrite filter_In in Hin, Hin''.
  destruct Hin as (Hin & _).
  destruct Hin'' as (Hin'' & _).
  apply In_nth  with (d := 0) in Hin.
  apply In_nth  with (d := 0) in Hin''.
  destruct Hin as (i & Hlen & Hnth).
  destruct Hin'' as (i' & Hlen' & Hnth'').
  rewrite <- Hnth'' in Hnth.
  destruct (jobs_arriving_at_unique _ _ _ _ Hlen Hlen' Hnth); lia.
Qed.



Lemma ue_preserves_sorted_entries : forall s o b s',
    functional_update_entries s = ((o,b),s') ->
     is_sorted _ (fun x y : Entry =>
                 deadline (Jobs (id x)) <=? deadline (Jobs (id y)))
               (active s) ->
      is_sorted _ (fun x y : Entry =>
                 deadline (Jobs (id x)) <=? deadline (Jobs (id y)))
                             (active s').
Proof.
intros s o b s' Hfss Hsor.
unfold functional_update_entries in Hfss.
remember ( insert_all Entry
              (fun e1 e2 : Entry =>
               deadline (Jobs (id e1)) <=? deadline (Jobs (id e2)))
              (map
                 (fun j : CNat =>
                  {|
                  id := j;
                  cnt := budget (Jobs j);
                  del := deadline (Jobs j) - arrival (Jobs j) |})
                 (filter (fun j : nat => j <? N) (jobs_arriving_at (now s))))
              (if
                match hd_error (active s) with
                | Some e =>
                    cnt e <=? budget (Jobs (id e)) - duration (Jobs (id e))
                | None => false
                end
               then tl (active s)
               else active s)) as ins.
destruct ins.
*
  injection Hfss ; intros ; subst ; clear Hfss.
  constructor.
*
  injection Hfss ; intros ; subst ; clear Hfss.
  cbn.
  rewrite Heqins.
  apply insert_all_sorted ; auto.
 +
   intros a b; destruct a, b.
   cbn.
   case (le_gt_dec (deadline (Jobs id)) (deadline (Jobs id0))) ; intro Hcas.
   -
     left.
     rewrite Nat.leb_le ; auto.
   -
     right.
      rewrite Nat.leb_le ; lia.
 +
   remember (active s) as acs.
   destruct acs.
   -
     constructor.
   -
     cbn.
     destruct ((cnt e0 <=?
       budget (Jobs (id e0)) - duration (Jobs (id e0)))); auto.
       eapply is_sorted_tail; eauto.
Qed.


Lemma uc_preserves_sorted_entries : forall s r  s',
    functional_update_counters s = (r,s') ->
     is_sorted _ (fun x y : Entry =>
                 deadline (Jobs (id x)) <=? deadline (Jobs (id y)))
               (active s) ->
      is_sorted _ (fun x y : Entry =>
                 deadline (Jobs (id x)) <=? deadline (Jobs (id y)))
                             (active s').
Proof.
intros s r s' Hc Hsor.
unfold functional_update_counters in Hc.
injection Hc ; intros Hr Hs ; subst; clear Hc.
cbn.
remember (active s) as acs.
destruct acs.
*
  constructor.
*
  apply is_sorted_map.
  cbn in *.
  inversion Hsor ; subst;constructor ; auto.
Qed.

Lemma active_sorted : forall t r s,
    running  t  =  (r,s) ->
    is_sorted _ (fun x y : Entry =>
                 deadline (Jobs (id x)) <=? deadline (Jobs (id y)))
                             (active s).
Proof.
    induction t; intros (o,b) s Hf.
    *
      rewrite running_0 in Hf.
      eapply ue_preserves_sorted_entries in Hf; eauto.
      constructor.
    *
      rewrite running_S in Hf.
      remember (running t) as rbs.
      destruct rbs as ((r' & b') & s').
      remember (functional_update_counters s') as rs.
      destruct rs as (r'' & s'').
      symmetry in Heqrs, Heqrbs.
      eapply ue_preserves_sorted_entries ; eauto.
      eapply uc_preserves_sorted_entries ; eauto.
Qed.



Lemma ue_effect_on_cnt : forall s o b s',
    functional_update_entries s = (o,b,s') ->
   (forall e,  In e  (tl (active s) )->
            cnt e > budget (Jobs (id e)) - duration (Jobs (id e))) ->
   forall e',  In e' (active s')->
                 cnt e' > budget (Jobs (id e')) - duration (Jobs (id e')).
Proof.
intros s o b s' Hfss Hcnt e' Hin'.
unfold functional_update_entries in Hfss.
remember ( insert_all Entry
              (fun e1 e2 : Entry =>
               deadline (Jobs (id e1)) <=? deadline (Jobs (id e2)))
              (map
                 (fun j : CNat =>
                  {|
                  id := j;
                  cnt := budget (Jobs j);
                  del := deadline (Jobs j) - arrival (Jobs j) |})
                 (filter (fun j : nat => j <? N) (jobs_arriving_at (now s))))
              (if
                match hd_error (active s) with
                | Some e =>
                    cnt e <=? budget (Jobs (id e)) - duration (Jobs (id e))
                | None => false
                end
               then tl (active s)
               else active s))
         as ins.
destruct ins;  injection Hfss; intros; subst ; clear Hfss  ; [inversion Hin' | ].
cbn [active] in Hin'.
rewrite Heqins in Hin'.
rewrite <- insert_all_contents_iff in Hin'.
destruct Hin' as [Hin' | Hin'].
*
  rewrite in_map_iff in Hin'.
  destruct Hin' as (i & Heqi & _).
  generalize Heqi ; intro Heqi'.
  apply f_equal with (f := id) in Heqi ; cbn in Heqi.
  apply f_equal with (f := cnt) in Heqi' ; cbn in Heqi'.
  rewrite Heqi in * ; clear Heqi.
  rewrite <- Heqi'; clear Heqi'.
  generalize (job_duration_gt_0 (id e')), (job_budget_enough (id e')) ;
        intros;  lia.
*
  remember (active s) as acs.
  destruct acs ; [inversion Hin'|].
  cbn [hd_error tl] in *.
  remember (cnt e0 <=? budget (Jobs (id e0)) - duration (Jobs (id e0))) as b.
  destruct b.
  +
    apply Hcnt ; auto.
  +
    symmetry in Heqb.
    rewrite Nat.leb_gt in Heqb.
    inversion Hin' ; subst  ; auto.
Qed.


Lemma uc_effect_on_cnt: forall s r s',
  functional_update_counters s = (r,s') ->
   (forall e,  In e  (active s) ->
                 cnt e > budget (Jobs (id e)) - duration (Jobs (id e)))
  -> (forall e',  In e' (tl (active s'))->
                 cnt e' > budget (Jobs (id e')) - duration (Jobs (id e'))).
Proof.
intros s r s' Hfc Hcnt e' Hin'.
unfold functional_update_counters in Hfc.
injection Hfc ; intros Hs' _ ; clear Hfc.
rewrite <- Hs' in Hin' ; clear Hs' s' ; cbn [active]  in Hin'.
remember (active s) as acs.
destruct acs ; [inversion Hin' |].
unfold decrease_all_del_func in Hin'.
cbn in Hin'.
rewrite in_map_iff in Hin'.
destruct Hin' as (e'' & Heqi & Hin').
cbn in Hin'.
generalize Heqi ; intro Heqi'.
apply f_equal with (f := cnt) in Heqi ; cbn in Heqi.
apply f_equal with (f := id) in Heqi' ; cbn in Heqi'.
rewrite <- Heqi, <- Heqi' in * ; clear Heqi Heqi'.
 apply Hcnt.
 constructor 2 ; auto.
Qed.

Lemma in_active_gt_budget_min_duration : forall  t s r,
    running t = (r,s) ->
    forall e,
      In e (active s) -> cnt e > budget (Jobs (id e)) - duration (Jobs (id e)).
Proof.
induction t ; intros s (o,b) Hrun e Hin.
*
  rewrite running_0 in Hrun.
  generalize Hrun ; intro Hrun'.
  eapply  ue_effect_on_cnt ; eauto ; intros e0 Hin' ; inversion Hin'.
*
  rewrite running_S in Hrun.
  remember (running t) as rbs.
  destruct rbs as ((o' & b') & s').
  remember (functional_update_counters s') as rs.
  destruct rs as (r & s'').
  symmetry in Heqrs, Heqrbs.
  eapply ue_effect_on_cnt ; eauto.
  eapply uc_effect_on_cnt; eauto.
Qed.

Lemma running_is_first': forall t r  b s e es,
    running  t = ((r,b),s)  ->
    s.(active) = e::es -> r = Some (id e).
Proof.
  intros  t r b' s e es  Hrun Hact.
  destruct t.
  *
    rewrite running_0 in Hrun.
    remember (functional_update_entries init) as rbs.
    destruct rbs as ((r' & b) & s').
    injection Hrun ; intros Hs Ho ; rewrite <- Hs in *;
      clear Hs Hrun; cbn.
    rewrite surjective_pairing in Heqrbs.
    rewrite pair_equal_spec in Heqrbs.
    destruct Heqrbs as (Hr & Hs).
    rewrite Hs in *.
    cbn in *.  
    rewrite Hact in *; auto.
    injection Hr  ; intros ; subst ; auto.
  *
    rewrite running_S in Hrun.
    case_eq  (running  t); intros o s' Hr.
    rewrite Hr in Hrun.
    case_eq (functional_update_counters  s'); intros o'' s'' Hc.
    rewrite Hc in Hrun.
    remember (functional_update_entries  s'') as rbs.
    destruct rbs as ((r' & b) & s''').
    injection Hrun ; intros Hs Ho ; rewrite <- Hs in *;
      clear Hs Hrun; cbn.
    rewrite surjective_pairing in Heqrbs.
    rewrite pair_equal_spec in Heqrbs.
    destruct Heqrbs as (Hr' & Hs).
    rewrite Hs in *.
    cbn in *.
    rewrite Hact in *; auto.
    injection Hr' ; intros ; subst ; auto.
Qed.

Lemma ue_preserves_c_prop : forall s o b s',
    functional_update_entries s = (o,b,s') ->
    (forall e,
        In e (active s) ->
        cnt e  =  c (id e) (now s) + (budget (Jobs (id e)) - duration (Jobs (id e)))) ->
    forall e',
      In e' (active s') ->
        cnt e'  =  c (id e') (now s') + (budget (Jobs (id e')) - duration (Jobs (id e'))).
Proof.
intros s o b s' Hfss Hcnt e' Hin'.
erewrite update_entries_leaves_now ; eauto.
unfold functional_update_entries in Hfss.
remember (insert_all Entry
              (fun e1 e2 : Entry =>
               deadline (Jobs (id e1)) <=? deadline (Jobs (id e2)))
              (map
                 (fun j : CNat =>
                  {|
                  id := j;
                  cnt := budget (Jobs j);
                  del := deadline (Jobs j) - arrival (Jobs j) |})
                 (filter (fun j : nat => j <? N) (jobs_arriving_at (now s))))
              (if
                match hd_error (active s) with
                | Some e =>
                    cnt e <=? budget (Jobs (id e)) - duration (Jobs (id e))
                | None => false
                end
               then tl (active s)
               else active s)) as ins.
destruct ins ;  injection Hfss ; intros ; subst ; clear Hfss ; [inversion Hin'|].
cbn [active] in Hin'.
rewrite Heqins in Hin' ; clear Heqins.
rewrite <- insert_all_contents_iff in Hin'.
destruct Hin' as [Hin' | Hin'].
*
  rewrite in_map_iff in Hin'.
  destruct Hin' as (i & Heqi & Hin').
  generalize Heqi ; intro Heqi'.
  apply f_equal with (f := id) in Heqi ; cbn in Heqi.
  apply f_equal with (f := cnt) in Heqi'; cbn in Heqi'.
  rewrite <- Heqi, <- Heqi' in * ; clear Heqi Heqi'.
  rewrite filter_In in Hin'.
  destruct Hin' as  (Hin' & HiN).
  rewrite jobs_arriving_at_prop in Hin'.
  rewrite NPeano.Nat.ltb_lt in HiN.
  generalize (job_budget_enough i) ; intros Hen.
  rewrite c_is_duration_upto_arrival; auto; lia.
*
  apply Hcnt.
  remember (active s) as acs ; destruct acs; [inversion Hin' |].
  cbn [hd_error] in Hin'.
  destruct (cnt e0 <=? budget (Jobs (id e0)) - duration (Jobs (id e0))) ; auto.
  apply in_tl ; auto.
Qed.

Lemma uc_preserves_c_prop : forall s r s',
    functional_update_counters s = (r,s') ->
    (forall e ,  hd_error (active s) = Some e -> run (id e) (now s) = true) ->
    (forall e ,  In e  (tl (active s )) -> run (id e) (now s) = false) ->
    (forall e ,  In e (active s) -> cnt e > budget (Jobs (id e)) - duration (Jobs (id e))) -> 
    (forall e,
        In e (active s) ->
        cnt e  =  c (id e) (now s) + (budget (Jobs (id e)) - duration (Jobs (id e)))) ->
    forall e',
      In e' (active s') ->
        cnt e'  =  c (id e') (now s') + (budget (Jobs (id e')) - duration (Jobs (id e'))).
Proof.
intros s r s'  Hc Hhd Htl Hinv Hcnt e' Hin'.
erewrite update_counters_changes_now ; eauto.
unfold functional_update_counters in Hc.
injection Hc  ; intros Hr  Hs ; subst; clear Hc.
cbn [active] in Hin'.
unfold decrease_all_del_func in Hin'.
rewrite in_map_iff in Hin'.
destruct Hin' as (e & Heqe & Hin').
generalize Heqe ; intro Heqe'.
apply f_equal with (f := id) in Heqe; cbn in Heqe.
apply f_equal with (f := cnt) in Heqe'; cbn in Heqe'.
rewrite <- Heqe, <- Heqe' ; clear Heqe Heqe'.
remember (active s) as acs  ; destruct acs ; inversion Hin' ; subst; cbn ; clear Hin'.
*
  specialize (Hcnt _ (in_eq _ _)).
  specialize (Hinv _ (in_eq _ _)).
  specialize (Hhd _ (eq_refl _)).
  rewrite Hhd.
  lia.
*
  specialize (Htl _ H).
  rewrite Htl.
  apply Hcnt.
  constructor 2; auto.
Qed.

  Lemma in_active_cnt_c: forall t s r b, 
    running  t = ((r,b),s) ->
    forall e,
      In e (active s) ->  cnt e  =  c (id e) t + (budget (Jobs (id e)) - duration (Jobs (id e))).
Proof.
induction t ; intros s r b0 Hrun e Hin.
*
  replace 0 with (now s) ; [| erewrite time_counter_now; eauto].
  rewrite running_0 in Hrun.
  eapply ue_preserves_c_prop ; eauto.
  intros e0 Hin' ; inversion Hin'.
*
   replace (S t) with (now s) ; [| erewrite time_counter_now; eauto].
   rewrite running_S in Hrun.
   remember (running t) as rbs.
   destruct rbs as ((o' & b') & s').
   symmetry in Heqrbs.
   remember (functional_update_counters s') as rs.
   destruct rs as (r' & s'').
   symmetry in Heqrs.
   eapply ue_preserves_c_prop ; eauto.
   intros e' Hin'.
   specialize (IHt _ _ _ (eq_refl _)).
   eapply uc_preserves_c_prop ; eauto.
  +
    intros e0 Hhd.
    destruct  (ids_after_update_counters  _ _ _ _ Heqrs Hin') as (e'' & Hin'' & Heq'' & _).
    remember (active s') as acs ; destruct acs  ; [inversion Hin''|].
    injection Hhd ; intros ; subst ; clear Hhd.
    unfold run.
    erewrite time_counter_now; eauto.
    rewrite Heqrbs.

    symmetry in Heqacs.
    generalize (running_is_first' _ _ _ _ _ _ Heqrbs Heqacs) ; intro Hsom.
    rewrite Hsom.
    apply Nat.eqb_refl.
  +
    intros e0 Htl.
    destruct  (ids_after_update_counters  _ _ _ _ Heqrs Hin') as (e'' & Hin'' & Heq'' & _).
     unfold run.
     erewrite time_counter_now; eauto.
     rewrite Heqrbs.
     remember (active s') as acs ; destruct acs  ; [inversion Hin''|].
     generalize (running_is_first' _ _ _ _ _ _ Heqrbs (sym_eq Heqacs)) ; intro Hsom.
     cbn in Htl.
     rewrite Hsom, Nat.eqb_neq.
     generalize  (active_unique_for_id _ _ _ Heqrbs) ; intro Hun.
     rewrite <- Heqacs in Hun.
     inversion Hun ; subst.
     intro Heq.
     apply H1 ; clear H1.
     rewrite <- Heq.
     rewrite in_map_iff.
     now exists e0.
  +
    eapply in_active_gt_budget_min_duration;  eauto.
  +
    intros e0 Hin0.
     erewrite time_counter_now; eauto.
Qed.


(* in_active_cnt_c *)
Lemma in_active_c_gt_0: forall t s r b,
    running  t = (r,b,s) ->
    forall e,
      In e (active s) ->  c  (id e) t > 0.
Proof.
  intros  t s r b Hrun e Hin.
  specialize (in_active_cnt_c  _ _ _ _ Hrun _ Hin); intro Hnct.
  specialize (in_active_gt_budget_min_duration   _ _ _ Hrun _ Hin);
    intro Hgt.
  lia.
Qed.


Lemma notrunning_when_c_0 :  forall  i t,  i < N ->
                                            c i t = 0 -> run  i t = false.
 Proof.
 intros  i t HiN Hc0.
 unfold run.
 case_eq (running t); intros (r,o) s Hr.
 destruct r ; auto.
 rewrite Nat.eqb_neq.
 intro Heq ; subst.
 destruct (running_is_first  _ _ _ _ Hr) as (e & es & Hact & Heq).
 rewrite <- Heq in * ; clear Heq.
 assert (Hin : In e (active s)) ; [rewrite Hact ; constructor ; auto |].
 generalize (in_active_c_gt_0  _ _ _ _ Hr _ Hin); intro; lia.
Qed.

Lemma c_decreases_when_running : forall (i t : nat), i < N ->
      run i t  = true -> (c  i t  > 0 /\
                        c i (S t)  = c  i t - 1).
Proof.
  intros  i t HiN Hrun.
  case (le_gt_dec t (arrival (Jobs i))); intros Hcas.
  *apply  c_is_duration_upto_arrival  in Hcas; auto.
   split.
   + generalize (job_duration_gt_0 i); intro Hgt; lia.
   + cbn.
         rewrite Hcas.
         rewrite Hrun; auto.
  * case_eq (c i t) ; intros.
       + 
          apply notrunning_when_c_0  in H ; auto.
          rewrite H in Hrun ; discriminate.
       + repeat split ; auto with arith.
         cbn.
         rewrite H, Hrun; lia.
Qed.


Lemma c_constant_when_not_running : forall (i t : nat), i < N ->
      run  i t  = false -> c i (S t) = c i t.
Proof.
intros  i t HiN Hrun. 
cbn.
rewrite Hrun; auto.
Qed.


Lemma fss_arrived_now_in_next_active :
forall s  r b s' i,
  functional_update_entries s = (r, b, s') ->
  i < N ->
  arrival (Jobs i) = (now s') -> 
  exists e : Entry, In e (active s') /\ id e = i.
Proof.
intros s r b s' i Hfss HiN Harr.
erewrite  update_entries_leaves_now in Harr ;eauto.
rewrite <- jobs_arriving_at_prop in Harr.
rewrite <- Nat.ltb_lt in HiN.
assert (Hfil :  In i (filter (fun j : nat => j <? N) (jobs_arriving_at (now s))));
  [rewrite filter_In; auto| clear Harr].
exists {|  id := i ; cnt := budget (Jobs i);   del := deadline (Jobs i) - arrival (Jobs i) |};
  split ; auto.
remember ( (if
                match hd_error (active s) with
                | Some e =>
                    cnt e <=? budget (Jobs (id e)) - duration (Jobs (id e))
                | None => false
                end
               then tl (active s)
               else active s)) as l.
remember (insert_all Entry
              (fun e1 e2 : Entry =>
               deadline (Jobs (id e1)) <=? deadline (Jobs (id e2)))
              (map
                 (fun j : CNat =>
                  {|
                  id := j;
                  cnt := budget (Jobs j);
                  del := deadline (Jobs j) - arrival (Jobs j) |})
                 (filter (fun j : nat => j <? N) (jobs_arriving_at (now s))))
              l) as ins.
unfold functional_update_entries in Hfss.
rewrite <- Heql, <- Heqins in Hfss.
replace (active s') with ins.
*
  rewrite Heqins.
  rewrite <- insert_all_contents_iff.
  left.
  rewrite in_map_iff.
  now exists i.
*
  destruct ins;  injection Hfss; intros ; subst; auto.
Qed.

  Lemma ids_after_update_counters_rev :
    forall t o b (s : State) (r : unit) (s' : State) (e : Entry),
       running t = (o,b,s) ->
       functional_update_counters s = (r, s') ->
       In e (active s) ->
       exists e' : Entry,
         In e' (active s') /\
         id e = id e' /\
         (run (id e) (now s) = true -> cnt e' = pred (cnt e)) /\
         (run (id e) (now s) = false -> cnt e = cnt e').
Proof.
intros t o b s r s' e Hrun Hc Hin.
unfold functional_update_counters in Hc.
injection Hc ; intros Hs Hr ; clear Hc Hr.
rewrite <- Hs; cbn ; clear Hs.
unfold decrease_all_del_func.
remember (active s) as acs.
destruct acs ; inversion Hin; subst ; cbn.
*
  exists ({|
     id := id e;
     cnt := Init.Nat.pred (cnt e);
     del := Init.Nat.pred (del e) |}).
  cbn.
  repeat split ; auto ; intro Hr; try lia.
  exfalso.
  symmetry in Heqacs.
  generalize (running_is_first' _ _ _ _ _  _ Hrun Heqacs); intro Hsom.
  unfold run in Hr.
  erewrite  time_counter_now in Hr ; eauto.
  rewrite Hrun in Hr.
  rewrite Hsom in Hr.
  apply beq_nat_false in Hr.
  apply Hr ; auto.
*
  symmetry in Heqacs.
  generalize (running_is_first' _ _ _ _ _  _ Hrun Heqacs); intro Hsom.
  exists ({|
              id := id e;
     cnt :=  (cnt e);
     del := Init.Nat.pred (del e) |}).
  cbn.
  repeat split ; auto; try lia.
  +

    right.
    rewrite in_map_iff.
    now exists e.
  +
    intro Hr.
    exfalso.
   unfold run in Hr.
   erewrite  time_counter_now in Hr ; eauto.
   rewrite Hrun in Hr.
   rewrite Hsom in Hr.
   rewrite Nat.eqb_eq in Hr.
   apply active_unique_for_id in Hrun.
   unfold unique_for in Hrun.
   rewrite Heqacs in Hrun.
   cbn in Hrun.
   rewrite NoDup_cons_iff in Hrun.
   destruct Hrun as (Hin' & _).
   apply Hin'.
   rewrite in_map_iff.
   now exists e.
Qed.


Lemma ue_keeps_entries_with_enough_cnt : forall s o b s' e,
functional_update_entries s = (o, b, s') ->
In e (active s) ->
cnt  e >  (budget (Jobs (id e)) - duration (Jobs (id e)))
 ->
 In e (active s').
Proof.
intros s o b s' e Hfss Hin Hnct.
unfold functional_update_entries in Hfss.
remember (insert_all Entry
              (fun e1 e2 : Entry =>
               deadline (Jobs (id e1)) <=? deadline (Jobs (id e2)))
              (map
                 (fun j : CNat =>
                  {|
                  id := j;
                  cnt := budget (Jobs j);
                  del := deadline (Jobs j) - arrival (Jobs j) |})
                 (filter (fun j : nat => j <? N) (jobs_arriving_at (now s))))
              (if
                match hd_error (active s) with
                | Some e =>
                    cnt e <=? budget (Jobs (id e)) - duration (Jobs (id e))
                | None => false
                end
               then tl (active s)
               else active s)) as ins.
destruct ins.
*
 remember (active s) as acs.
 destruct acs ; inversion Hin ; subst.
 +
   cbn [hd_error  tl] in Hfss, Heqins.
   unfold gt in Hnct.
   rewrite <- Nat.leb_gt in Hnct.
   rewrite Hnct in *.
   exfalso.
   generalize  (in_nil) ; intro Hnil.
   generalize (Hnil Entry e) ; intro Hin' ; apply Hin'.
   rewrite Heqins.
   rewrite <- insert_all_contents_iff.
   right ; auto.
 + 
   cbn [hd_error  tl] in Hfss, Heqins.
   exfalso.
   generalize  (in_nil) ; intro Hnil.
   generalize (Hnil Entry e) ; intro Hin' ; apply Hin'.
   rewrite Heqins.
   rewrite <- insert_all_contents_iff.
   right ; auto.
   destruct (cnt e0 <=? budget (Jobs (id e0)) - duration (Jobs (id e0))); auto.

 * injection Hfss ; intros ; subst; clear Hfss.
   cbn [active].
   rewrite Heqins  ; clear Heqins.
   rewrite <- insert_all_contents_iff.
   right.
   destruct (active s) ; inversion Hin; subst.
   +
     cbn [hd_error  tl].
      unfold gt in Hnct.
      rewrite <- Nat.leb_gt in Hnct.
      rewrite Hnct ; auto.
   +
     cbn [hd_error  tl].
     destruct (cnt e1 <=? budget (Jobs (id e1)) - duration (Jobs (id e1))); auto.
Qed.

   Lemma arrived_now_active : forall  t i,
      i < N -> arrival (Jobs i) <= t -> c  i t > 0 ->
      forall r s b , running  t = (r,b,s) ->
                   exists e, In e (active s) /\ id e = i.
Proof.
induction t ; intros i HiN Harr Hcgt r s b Hr.
*
  assert (Harr' : arrival (Jobs i) = 0) ; [lia | clear Harr ; rename Harr' into Harr].
  erewrite <- time_counter_now in Harr ; eauto.
  eapply fss_arrived_now_in_next_active ; eauto.
*
  generalize (time_counter_now _ _ _ Hr) ; intro Hnow.
  rewrite running_S in Hr.
  remember (running t) as rbs.
  destruct rbs as ((r' & b') & s').
  remember (functional_update_counters s') as rs.
  destruct rs as  (r'' & s'').
  symmetry in Heqrbs, Heqrs.
  apply le_lt_eq_dec in Harr.
  destruct Harr as [Hlt | Heq].
  +
    apply le_S_n in Hlt.
    specialize (IHt _ HiN Hlt).
    cbn in Hcgt.
    remember (c i t) as cit.
    destruct cit.
    -
      destruct (run i t) ; lia.
    -
      cbn in Hcgt.
      replace (cit - 0) with cit in Hcgt ; try lia.
      specialize (IHt (gt_Sn_O _) _ _ _ (eq_refl _)).
      destruct IHt as (e' & Hin' & Heq').
      destruct (ids_after_update_counters_rev  _ _ _ _ _ _ _ Heqrbs Heqrs Hin') as
          (e'' & Hin'' & Heq'' & Hle & Hle').
      erewrite time_counter_now in Hle, Hle'; eauto.
      exists e'' ; split ; try congruence.
      rewrite Heqcit in Hcgt.
      remember (run i t) as runit.
      destruct runit ; symmetry in Heqrunit.
      **
        generalize (in_active_cnt_c _ _ _ _ Heqrbs _ Hin') ; intro Hcnt.
        eapply ue_keeps_entries_with_enough_cnt; eauto.
        rewrite <- Heq'',Heq' in *.
        specialize (Hle Heqrunit).
        rewrite <- Heqcit in Hcnt.
        lia.
      **
         generalize (in_active_cnt_c _ _ _ _ Heqrbs _ Hin') ; intro Hcnt.
         eapply ue_keeps_entries_with_enough_cnt; eauto.
        rewrite <- Heq'',Heq' in *.
        specialize (Hle' Heqrunit).
        rewrite <- Heqcit in Hcnt.
        lia.
  +
    eapply  fss_arrived_now_in_next_active ; eauto.
    rewrite Hnow; auto.
Qed.

Lemma in_active_id_lt_N : forall t r s,
  running t = (r,s) -> 
   forall e, In e (active s) -> id e < N.
Proof.
  intros t r s Hrun e Hin.
  destruct (active_from_earlier_arrivals  _ _ _ Hrun _ Hin)
    as (t' &  _  & Hin').
  rewrite filter_In in Hin'.
  destruct Hin' as (_ & Hide).
  rewrite Nat.ltb_lt in Hide; auto.
Qed.

  Lemma all_arrived_some_running :  forall  t i,
      i < N -> arrival (Jobs i) <= t -> c  i t > 0 ->
      exists j, j < N /\ run  j t = true.
Proof.
  intros t i HiN Harr Hc.
  case_eq (running  t) ; intros (r,b') s Hr.
  destruct (arrived_now_active  _ _ HiN Harr Hc _ _ _ Hr)
    as (e & Hin & _).
  unfold run.
  rewrite Hr.
  remember (active s) as acts.
  destruct acts; [inversion Hin | ].
  symmetry in Heqacts.
  rewrite (running_is_first'  _ _ _ _ _ _ Hr Heqacts) in *.
  exists (id e0) ; split ; auto;  [| rewrite Nat.eqb_eq; auto].
  eapply in_active_id_lt_N; eauto.
  rewrite  Heqacts ; constructor ; auto.
Qed.

Definition sum_counters_arrived( t : nat) :=
    generic_sum
      (fun i  => c i t)
        (fun i  => arrival(Jobs i) <=? t)
        0 N.

Lemma sum_arrived_some_running : forall  t,
      sum_counters_arrived  t > 0 ->
      exists j, j < N /\ run j t = true.
  Proof.
  intros  t Hsum.
  apply generic_sum_gt_0_ex in Hsum; auto with arith.
  destruct Hsum as (k & HkN & Harr & Hc).
  rewrite Nat.leb_le in Harr.
  apply all_arrived_some_running with (i := k); auto.
  Qed.




End FunctionalEdfImplementsAssumptionsMod.




Module FunctionalEdfIsCorrectMod (J : JobsAxiomsMod).

Import J.
Module Alg := FunctionalEdfImplementsAssumptionsMod J.
Module Pol :=  EdfPolicyMod J Alg.
Import Alg. 
Import Pol.

Fixpoint functional_scheduler_star (t: nat):=
  match t with
    0 => ((None,false),init)
  |S t' =>
   let (_,s') := functional_scheduler_star  t' in
   functional_scheduler  s'
  end.

Lemma functional_scheduler_star_0 : 
    functional_scheduler_star 0 = ((None,false),init).
Proof.
reflexivity.
Qed.

Lemma functional_scheduler_star_S : forall  t,
    functional_scheduler_star (S t) =
     let (_,s') := functional_scheduler_star t in
     functional_scheduler s'.
Proof.
reflexivity.
Qed.



Lemma fss_running : forall t,
    functional_scheduler_star (S t) =
    let (r,s) := running t in
    let (_,s') := functional_update_counters s  in (r,s').
Proof.
  induction t.
* case_eq (running 0) ; intros r s Hr.
  case_eq (functional_update_counters  s) ; intros o s' Hc.
  rewrite running_0 in Hr.
  rewrite functional_scheduler_star_S,functional_scheduler_star_0.
  unfold functional_scheduler.
  remember (functional_update_entries init) as rbs.
  destruct rbs as ((r' & b) & s'').
  injection Hr ; intros ; subst ; clear Hr.
  cbn.
  rewrite pair_equal_spec; split; auto.
  injection Hc ; intros Hs _ ; rewrite <- Hs in * ; auto.
* repeat rewrite functional_scheduler_star_S in *.
  (* rewrite IHt; clear IHt.*)
  rewrite running_S.
  case_eq (running  t) ; intros r s Hr.
  rewrite Hr in *.
  case_eq (functional_update_counters  s) ; intros o s' Hc.
  rewrite Hc in *.
  case_eq (functional_scheduler_star  t);intros o' s''' Hfs.
  rewrite Hfs in *.
  case_eq (functional_scheduler  s''') ; intros (o'' & b) s_ Hf.
  rewrite Hf in *.
  injection IHt ; intros ; subst.

  unfold functional_scheduler ; auto.
Qed.

Lemma run_scheduler_star : forall  i t,
  run i t = true ->
   fst (fst ((functional_scheduler_star (S t)))) = Some i.
Proof.
  intros  i t Hrun.
  case_eq (functional_scheduler_star  (S t)) ;
    intros (r & b) s Hfss.
  generalize (fss_running t); rewrite Hfss; intro Hd.
  case_eq (running t) ; intros r' s' Hr.
  rewrite Hr in *.
  case_eq (functional_update_counters  s'); intros u s'' Hc.
  rewrite Hc in *.
  cbn.
  injection Hd ; intros ; subst.
  unfold run in Hrun.
  rewrite Hr in *.
  destruct r; try discriminate.
  rewrite Nat.eqb_eq in Hrun ; subst; auto.
Qed.


Lemma scheduler_star_run : forall i t,
    fst (fst (functional_scheduler_star (S t))) = Some i ->
    run i t = true.
Proof.
  intros i t Hfss.
  case_eq (functional_scheduler_star  (S t)) ;
    intros (r & b) s Hfss'.
  rewrite Hfss' in Hfss.
  cbn in Hfss ; subst.
  generalize (fss_running  t); rewrite Hfss'; intro Hd.
case_eq (running t) ; intros (r,b')  s' Hr.
unfold run.
rewrite Hr in *.
destruct r; try discriminate.
rewrite Nat.eqb_eq.
case_eq (functional_update_counters  s') ; intros o s'' Hc.
rewrite Hc in Hd.
injection Hd; intros ; auto.
Qed.

Lemma run_iff_scheduler_star : forall i t,
    run i t = true <->
    fst (fst ((functional_scheduler_star (S t)))) = Some i.
Proof.
 split; intros.
 * apply run_scheduler_star; auto.
 * apply scheduler_star_run; auto.
Qed.


Lemma functional_scheduler_implements_policy :
  forall t o s,
 functional_scheduler_star  t = (o,s)  ->
  EdfPolicyUpTo (now s).
 Proof.
   intros  t o s Hfss.
   unfold  EdfPolicyUpTo.
   intros i t0 HiN0 Ht0now Hrun j Hw.
   destruct (Nat.eq_dec i j); subst; auto.
   destruct Hw as (HjN & Harrj  & Hcj & Hrj).
   rewrite  run_iff_scheduler_star in Hrun.
   case_eq (functional_scheduler_star  (S t0)) ;
    intros (r & b) s' Hfss'.
   rewrite Hfss' in Hrun.
   cbn in Hrun; subst.
  (*  injection Hrun ; intros; subst.  *) 
    generalize (fss_running  t0); rewrite Hfss'; intro Hd.
   (*rewrite fss_running in Hrun.*)

   case_eq (running  t0) ; intros r' s'' Hr.
   rewrite Hr in Hd.
   case_eq (functional_update_counters s'') ; intros o' s''' Hc.
   rewrite Hc in Hd.
   cbn in Hd.
   injection Hd ;intros ; subst; clear Hd.
   destruct (running_is_first  _ _ _ _ Hr)
       as (e & es & Hact & Hid).
   rewrite <- Hid in * ; clear Hid.
   destruct (arrived_now_active  _ _ HjN Harrj Hcj _ _ _ Hr)
       as (e' & Hin & Hid').
   rewrite <- Hid' in * ; clear Hid'.
   rewrite Hact in Hin.
   inversion Hin.
     * exfalso ; apply n ; subst ; auto.
     * rewrite <- Nat.leb_le.
       generalize (active_sorted  _ _ _ Hr); intros Hsorted.
       rewrite Hact in *. 
       apply
         (is_sorted_R_forall
            Entry
            (fun x y : Entry =>
               deadline (Jobs (id x)) <=? deadline (Jobs (id y))))
         with (l := es); auto.
       intros a b' c ; destruct a, b', c ; cbn.
       repeat rewrite Nat.leb_le.
       intros.
       eapply le_trans ; eauto.
 Qed.

Lemma functional_scheduler_correct :
  feasible ->  forall (t i: nat) r s ,
    functional_scheduler_star t = (r,s) ->
    i < N -> ~overdue  i (now s).
Proof.
intros Hf t i r s Hfss HiN.
apply  EdfPolicyMainTheorem; auto.
eapply  functional_scheduler_implements_policy; eauto.
Qed.

End FunctionalEdfIsCorrectMod.


Module FunctionalEdfErrorHandlingMod(J : JobsAxiomsMod).
 Import J.
Module Alg := FunctionalEdfImplementsAssumptionsMod J.
Module Pol :=  EdfPolicyMod J Alg.
Module Cor := FunctionalEdfIsCorrectMod J.
Import Alg.
Import Pol.
Import Cor.

Lemma update_entries_del_0 :
forall s e s',
  functional_update_entries s = (Some (id e), true,s') ->
  exists e' l,  active s' = e' :: l /\ id e' = id e /\ del e' = 0.
Proof.
  intros s e s' Hfss.
  unfold functional_update_entries in Hfss.
  remember ( insert_all Entry
              (fun e1 e2 : Entry =>
               deadline (Jobs (id e1)) <=?
               deadline (Jobs (id e2)))
              (map
                 (fun j : CNat =>
                  {|
                  id := j;
                  cnt := budget (Jobs j);
                  del := deadline (Jobs j) - arrival (Jobs j) |})
                 (filter (fun j : nat => j <? N)
                    (jobs_arriving_at (now s))))
              (if
                match hd_error (active s) with
                | Some e =>
                    cnt e <=?
                    budget (Jobs (id e)) -
                    duration (Jobs (id e))
                | None => false
                end
               then tl (active s)
               else active s)) as ins.
    destruct ins.
  *  injection Hfss ; intros ; discriminate.
  * cbn in Hfss.  injection Hfss; intros ; subst.
    cbn in *.
    exists e0, ins ; repeat split ; auto.
    apply beq_nat_eq ; auto.
Qed.


Lemma del_counts_to_deadline :  forall t o b s,
    running  t  =  (o, b ,s)  ->
       forall e,  In e (active s) ->
             del e = deadline (Jobs (id e)) - t.
Proof.
induction t  ; intros o b s  Hrun e Hin.
*  rewrite running_0 in Hrun.
   cbn in *.
   unfold functional_update_entries, init in Hrun.
   cbn in Hrun.
   remember ( insert_all Entry
              (fun e1 e2 : Entry =>
               deadline (Jobs (id e1)) <=?
               deadline (Jobs (id e2)))
              (map
                 (fun j : CNat =>
                  {|
                  id := j;
                  cnt := budget (Jobs j);
                  del := deadline (Jobs j) - arrival (Jobs j) |})
                 (filter
                    (fun j : nat =>
                     match N with
                     | 0 => false
                     | S m' => j <=? m'
                     end) (jobs_arriving_at 0))) []) as ins.
   destruct ins.
   + injection Hrun  ; intros ; subst.
       inversion Hin.
   +
      injection Hrun ; intros; subst.
      clear Hrun.
      cbn [active ]in Hin.
      rewrite Heqins in Hin.
      clear Heqins.
      rewrite <- insert_all_contents_iff in Hin.
      destruct Hin as [Hin | Habs]; [| inversion Habs].
      rewrite in_map_iff in Hin.
      destruct Hin as (i & Heq & Hin).
      rewrite <- Heq ; cbn.
      rewrite filter_In in Hin.
      destruct Hin as (Hin & _ ).
      rewrite  jobs_arriving_at_prop in Hin.
      rewrite Hin; auto.
*
  generalize Hrun; intro Hrun_cp.
  apply time_counter_now in Hrun_cp.
  rewrite <- Hrun_cp.
  clear Hrun_cp.
  rewrite running_S in Hrun.
  remember (running t) as rs.
  destruct rs as ((o',b'),s').
  remember (functional_update_counters s') as rs.
  destruct rs as (r'',s'').
  specialize (IHt _ _ _ (eq_refl _ )).
  symmetry in Heqrs, Heqrs0.
  generalize Heqrs; intro Hrun'.
  apply time_counter_now in Heqrs.
  rewrite <- Heqrs in IHt.
  clear Heqrs.
  unfold functional_update_entries in Hrun.
  remember (insert_all Entry
              (fun e1 e2 : Entry =>
               deadline (Jobs (id e1)) <=?
               deadline (Jobs (id e2)))
              (map
                 (fun j : CNat =>
                  {|
                  id := j;
                  cnt := budget (Jobs j);
                  del := deadline (Jobs j) - arrival (Jobs j) |})
                 (filter (fun j : nat => j <? N)
                    (jobs_arriving_at (now s''))))
              (if
                match hd_error (active s'') with
                | Some e =>
                    cnt e <=?
                    budget (Jobs (id e)) -
                    duration (Jobs (id e))
                | None => false
                end
               then tl (active s'')
               else active s'')) as ins.
  destruct ins.
   +
     injection Hrun ; intros ; subst.
     inversion Hin.
  +
     injection Hrun ; intros ; subst.
     cbn [active] in Hin.
     clear Hrun.
     cbn.
     rewrite Heqins in Hin.

     rewrite <- insert_all_contents_iff in Hin.
     destruct Hin as [Hin | Hin].
     -
      rewrite in_map_iff in Hin.
      destruct Hin as (i & Heq & Hin).
      rewrite <- Heq ; cbn.
      rewrite filter_In in Hin.
      destruct Hin as (Hin & _ ).
      rewrite  jobs_arriving_at_prop in Hin.
      rewrite Hin; auto.
    - assert (Hin'' : In e (active s'')).
      {
        destruct (active s'') ; auto.
        cbn in Hin.
        destruct ((cnt e1 <=?
             budget (Jobs (id e1)) -
             duration (Jobs (id e1)))) ; auto.
        constructor 2; auto.
      }

    destruct  (ids_after_update_counters _ _ _ _ Heqrs0  Hin'') as (e' & Hin' & Heq' & Hdel).
    specialize (IHt _ Hin').
    rewrite Heq' in *.
    generalize Heqrs0 ; intro Hfc.
    apply  update_counters_changes_now in Heqrs0.
    rewrite Heqrs0.
    rewrite  IHt in Hdel.
    lia.
Qed.

 Lemma running_overdue : forall t o b s i,
    running  t  =  ( (o, b) ,s) -> b = true -> o = Some i ->
    overdue i (now s).
Proof.
intros t o b s i Hrun Hb Ho.
unfold overdue.
rewrite Ho in Hrun.
destruct (running_is_first _ _ _ _ Hrun) as (e & l & Hact & Heq).
rewrite <- Heq in *.
repeat split.
* eapply in_active_id_lt_N  ; eauto.
   rewrite Hact ; constructor; auto.  
* erewrite time_counter_now with (t :=t) ; eauto.
  eapply in_active_c_gt_0 ; eauto.
  rewrite Hact ; constructor; auto.
*  erewrite time_counter_now with (t :=t) ; eauto.
   assert (Hin : In e (e ::l)) ; [constructor; auto|].
    rewrite <- Hact in Hin.   
    generalize (del_counts_to_deadline _ _ _ _ Hrun _ Hin); intro Hdel.
    destruct t .
+  rewrite running_0, Hb in Hrun.
     destruct (update_entries_del_0 _ _ _ Hrun) as (e' & l' & Hact'  & Hid & Hdel0).
     rewrite Hact in Hact'.
     injection Hact' ; intros ; subst.
     rewrite Hdel0 in Hdel.
     lia.
+  rewrite running_S, Hb in Hrun.
     remember (running t) as rs.
     destruct rs as (r',s').
     remember (functional_update_counters s') as rs.
     destruct rs as (r'',s'').
     destruct (update_entries_del_0 _ _ _ Hrun) as (e' & l' & Hact'  & Hid & Hdel0).
     rewrite Hact in Hact'.
     injection Hact' ; intros ; subst.
     rewrite Hdel0 in Hdel.
     lia.
Qed.

Lemma functional_scheduler_star_overdue : forall t o b s i,
    functional_scheduler_star  t  =  ( (o, b) ,s) -> b = true -> o = Some i ->
    overdue i ( now s  -1).
Proof.
intros t o b s i Hfss Hb Ho.
destruct t.
* cbn in Hfss.
  rewrite Hb in Hfss.
  inversion Hfss.
* rewrite fss_running in Hfss.
  remember (Alg.running t) as rs.
  destruct rs as ((o' & b') & s').
  remember (Alg.functional_update_counters s') as rs.
  destruct rs as (r  & s'').
  symmetry in Heqrs, Heqrs0.
  injection Hfss; intros; subst; clear Hfss.
  generalize Heqrs ; intro Hrun.
  apply running_overdue with (i := i) in Heqrs; auto.
  apply time_counter_now in Hrun.
  apply  update_counters_changes_now in Heqrs0.
  rewrite Heqrs0,  Hrun in *.
  replace (S t -1) with t ; auto ; lia.
Qed.

End  FunctionalEdfErrorHandlingMod.
