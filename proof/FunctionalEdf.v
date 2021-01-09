Require Import List.
Require Import Classical.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Omega.
Require Import Lia.
From Scheduler.Proof Require Import Lib Assumptions JobsAxioms EdfPolicy.
From Scheduler.Model Require Import AbstractTypes AbstractFunctions.
From Scheduler.SchedulerMockup Require Import Jobs.


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
let b' :=  match hd_error s.(active) with
     | Some e =>
         cnt e =? 0
     | None => false
           end
in  
let active1 := if b && (negb b') then tl s.(active) else s.(active) in
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
let active4 :=
       match active3 with
       | [] => []
       | e :: es => if cnt e =? 0 then es else e :: es
       end in
let active5 :=  (decrease_all_del_func active4) in
  (tt, mk_State (S s.(now))  active5 ).




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
remember  ( insert_all Entry
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
                    budget (Jobs (id e)) - duration (Jobs (id e))
                | None => false
                end &&
                negb
                  match hd_error (active s) with
                  | Some e => cnt e =? 0
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
            ((cnt e0 <=?
             budget (Jobs (id e0)) - duration (Jobs (id e0))) &&
            negb (cnt e0 =? 0)) ; auto.
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
  destruct Hin as (e'' & Heq & Hin).
  generalize Heq ; intro Heq'.
  apply f_equal with (f := id) in Heq.
  apply f_equal with (f := del) in Heq'.
  cbn in Heq, Heq'.
  destruct (Init.Nat.pred (cnt e)).
  + rewrite Nat.eqb_refl in Hin.
      exists e'' ; cbn ; repeat split ; auto ; lia.
  + 
    assert( Hn : S n <> 0) ; auto.
    rewrite <- Nat.eqb_neq in Hn.    
    rewrite Hn in Hin; clear Hn.
    inversion Hin ; subst.
    - cbn in Heq, Heq'.  
      exists e ; cbn ; repeat split ; auto.
      lia.
    -  exists  e'' ; cbn ; repeat split ; auto.
       lia.
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
                  (jobs_arriving_at (now s))))
            (if
              match hd_error (active s) with
              | Some e =>
                  cnt e <=?
                  budget (Jobs (id e)) -
                  duration (Jobs (id e))
              | None => false
              end &&
              negb
                match hd_error (active s) with
                | Some e => cnt e =? 0
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
map id (active s') = map id (active s) \/
map id (active s') = tl (map id (active s)).
Proof.
intros s s' r' Hfss.
unfold functional_update_counters in Hfss.
apply f_equal  with (f := snd) in Hfss ; cbn in Hfss.
remember (active s) as acts.
destruct acts.
* destruct s' ; cbn in *.
   injection Hfss  ; intros ; subst.
   right ; auto.
* destruct s' ; cbn in *.
   destruct (Init.Nat.pred (cnt e)).
  + rewrite Nat.eqb_refl in Hfss.
    injection Hfss  ; intros ; subst.
    rewrite map_map.
    right.
    reflexivity.
 +   
    assert( Hn : S n <> 0) ; auto.
    rewrite <- Nat.eqb_neq in Hn.    
    rewrite Hn in Hfss; clear Hn.
    cbn in Hfss.
    injection Hfss  ; intros ; subst.
    left; cbn.
    rewrite map_map.
    reflexivity.
Qed.

Lemma active_id_after_uc_subset  : forall s s' r' e, 
    functional_update_counters s = (r',s') ->
    In (id e) (map id (active s')) -> In (id e) (map id (active s)) .
Proof.
intros s s' r' e He Hin.  
apply uc_effect_on_active in He.
destruct He as [He | He]; rewrite He in Hin ; auto.  
apply in_tl; auto.
Qed.


Lemma uc_preserves_unique_id : forall s s' r', 
    functional_update_counters s = (r',s') ->
    unique_for id (active s) ->
    unique_for id (active s').
Proof.
intros s s' r' Hc Hu.
unfold unique_for in *.  
apply uc_effect_on_active in Hc.
destruct Hc as [Hc | Hc] ; rewrite Hc ; auto. 
apply NoDup_tl ; auto.
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
                (filter (fun j : nat => j <? N)
                   (jobs_arriving_at (now s))))
             (if
               match hd_error (active s) with
               | Some e =>
                   cnt e <=?
                   budget (Jobs (id e)) - duration (Jobs (id e))
               | None => false
               end &&
               negb
                 match hd_error (active s) with
                 | Some e => cnt e =? 0
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
                 budget (Jobs (id e0)) - duration (Jobs (id e0))) &&
                negb (cnt e0 =? 0)); auto.
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
                 budget (Jobs (id e)) - duration (Jobs (id e))) &&
                negb (cnt e =? 0)); auto.
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
               deadline (Jobs (id e1)) <=?
               deadline (Jobs (id e2)))
              (map
                 (fun j : CNat =>
                  {|
                  id := j;
                  cnt := budget (Jobs j);
                  del := deadline (Jobs j) -
                         arrival (Jobs j) |})
                 (filter (fun j : nat => j <? N)
                    (jobs_arriving_at (now s))))
              (if
                match hd_error (active s) with
                | Some e =>
                    cnt e <=?
                    budget (Jobs (id e)) -
                    duration (Jobs (id e))
                | None => false
                end &&
                negb
                  match hd_error (active s) with
                  | Some e => cnt e =? 0
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
       budget (Jobs (id e0)) - duration (Jobs (id e0))) &&
               negb (cnt e0 =? 0)); auto.
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
  cbn.  
  destruct ( Init.Nat.pred (cnt e) =? 0).
  +
    eapply is_sorted_tail ; eauto.
  +
    destruct acs.
    -
      apply is_sorted_singleton.
    -
      inversion Hsor ; subst.
      constructor ; auto.
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
    (forall e,  hd_error (active s) = Some e ->  cnt e > budget (Jobs (id e)) - duration (Jobs (id e))
                \/ (cnt e <= budget (Jobs (id e)) - duration (Jobs (id e)))  /\ cnt e > 0) ->
   (forall e,  In e  (tl (active s) )->
            cnt e > budget (Jobs (id e)) - duration (Jobs (id e))) ->
   forall e',  In e' (active s')->
                 cnt e' > budget (Jobs (id e')) - duration (Jobs (id e')).
Proof.
intros s o b s' Hfss Hhd Hcnt e' Hin'.
unfold functional_update_entries in Hfss.
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
                    (jobs_arriving_at (now s))))
              (if
                match hd_error (active s) with
                | Some e =>
                    cnt e <=?
                    budget (Jobs (id e)) -
                    duration (Jobs (id e))
                | None => false
                end &&
                negb
                  match hd_error (active s) with
                  | Some e => cnt e =? 0
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
destruct (Hhd _ (eq_refl _)) as [Hgt | (Hle & Hgt)]; clear Hhd.
 +
  
  unfold gt in Hgt.
  rewrite <- Nat.leb_gt in Hgt.
  rewrite Hgt in Hin'.
  inversion Hin' ; subst.
  -
   rewrite Nat.leb_gt in Hgt; auto.
  -
    apply Hcnt ; auto.
 +  
    rewrite   <- Nat.leb_le in Hle.
    rewrite Hle in Hin'.
    unfold gt in Hgt.
    destruct (cnt e0) ; try lia.
    cbn in Hin'.
    apply Hcnt ; auto.
Qed.

Lemma uc_effect_on_cnt_hd: forall s r s',
  functional_update_counters s = (r,s') ->
   (forall e,  In e  (active s) ->
                 cnt e > budget (Jobs (id e)) - duration (Jobs (id e)))
  -> (forall e',  hd_error (active s') = Some e' ->
                  cnt e' > budget (Jobs (id e')) - duration (Jobs (id e')) \/
                   ((cnt e' <= budget (Jobs (id e')) - duration (Jobs (id e')))  /\ cnt e' > 0) ).
Proof.
intros s r s' Hfc Hcnt e' Hin'.
unfold functional_update_counters in Hfc.
injection Hfc ; intros Hs' _ ; clear Hfc.
rewrite <- Hs' in Hin' ; clear Hs' s' ; cbn [active]  in Hin'.
remember (active s) as acs.
destruct acs ; [inversion Hin' |].
unfold decrease_all_del_func in Hin'.
cbn in Hin'.
apply map_hd in Hin'.
destruct Hin' as (e0 & Heqi & Hh).
generalize Heqi ; intro Heqi'.
apply f_equal with (f := cnt) in Heqi ; cbn in Heqi.
apply f_equal with (f := id) in Heqi' ; cbn in Heqi'.
 rewrite <- Heqi, <- Heqi' ; clear Heqi Heqi'.
remember  (cnt e) as  c ; destruct c.
*
  specialize (Hcnt _ (in_eq _ _)) ; lia.
*
  cbn in Hh.
  remember (c0 =? 0) as b.
  destruct  b.
 + 
   left.  
   apply Hcnt.
   constructor 2.
   apply hd_in ; auto.
 +   
   injection Hh ; intros ; subst ; clear Hh.
  cbn.
  destruct c0 ; try discriminate.
  lia.
Qed.



Lemma uc_effect_on_cnt_tl : forall s r s',
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
rewrite <- map_tl in Hin'.
rewrite in_map_iff in Hin'.
destruct Hin' as (e'' & Heqi & Hin').
cbn in Hin'.
generalize Heqi ; intro Heqi'.
apply f_equal with (f := cnt) in Heqi ; cbn in Heqi.
apply f_equal with (f := id) in Heqi' ; cbn in Heqi'.
rewrite <- Heqi, <- Heqi' in * ; clear Heqi Heqi'.
remember  (cnt e) as  c ; destruct c.
* 
  cbn in Hin'.
  apply Hcnt.
  constructor 2.
  apply in_tl  ; auto.
* cbn in Hin'.
  remember (c0 =? 0) as b.
  destruct  b.
    +
       apply Hcnt.
       constructor 2.
      apply in_tl ; auto.       
    + 
      cbn in Hin'.
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
  + eapply uc_effect_on_cnt_hd ; eauto.
  + eapply uc_effect_on_cnt_tl ; eauto.
Qed.

Lemma running_is_first': forall t r  b s e es,
    running  t = ((r,b),s)  ->
    s.(active) = e::es -> r = Some (id e).
Proof.
  intros  t r b' s e es  Hrun Hact.
  destruct t.
  * rewrite running_0 in Hrun.
  remember (functional_update_entries init) as rbs.
    destruct rbs as ((r' & b) & s').
    injection Hrun ; intros Hs Ho ; rewrite <- Hs in *;
      clear Hs Hrun; cbn.
     rewrite surjective_pairing in Heqrbs.
    rewrite pair_equal_spec in Heqrbs.
    destruct Heqrbs as (Hr & Hs).
    rewrite Hs in *.
    cbn in *.  
    (*injection Hrun ; intros Hs Ho ; rewrite <- Hs in *;
      clear Hs Hrun; cbn in *.*)
    rewrite Hact in *; auto.
    injection Hr  ; intros ; subst ; auto.
* rewrite running_S in Hrun.
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
  (*injection Hrun ; intros Hs Ho; rewrite <- Hs in * ; cbn in *;
    clear Hs Hrun.*)
    rewrite Hact in *; auto.
    injection Hr' ; intros ; subst ; auto.    
Qed.
 
Lemma in_active_cnt_aux :
forall  t o b r b' s' s'',
running  t = ((o,b),s') ->
running  (S t) = ((r,b'),s'') ->
forall e'', In e'' (active s'') ->
           (((exists e', In e' (active s') /\ id e' = id e'' /\
                       (o = Some (id e') -> cnt e' > 0 /\ cnt e'' = cnt e' - 1) /\
                       (o <> Some (id e') -> cnt e'' = cnt e'))                         
            ) \/
            In (id e'')
               (filter (fun j => j <? N)(jobs_arriving_at (now s''))) /\
            cnt e'' = budget (Jobs (id e''))).
Proof.
  intros  t o b0 r b1  s' s'' Hrun Hrun1 e'' Hin''.
  rewrite running_S in Hrun1.
  rewrite Hrun in Hrun1.
  case_eq (functional_update_counters  s') ; intros o'  s_ Hc.
  rewrite Hc in Hrun1.
   remember (functional_update_entries  s_) as rbs.
    destruct rbs as ((r' & b) & s''').
    injection Hrun1 ; intros Hs Ho ; rewrite <- Hs in *;
      clear Hs Hrun1; cbn.
     rewrite surjective_pairing in Heqrbs.
    rewrite pair_equal_spec in Heqrbs.
    destruct Heqrbs as (Hr' & Hs).
    rewrite Hs in *.
    cbn in *.    
  (*injection Hrun1 ; intros Hs Ho ; rewrite <- Hs in Hin''  ; cbn in
      Hin''.*)
  rewrite <- insert_all_contents_iff in Hin''.
  rewrite in_map_iff in Hin''.
  destruct Hin'' as [(i & He'' & Hin'') | Hin''].
  * rewrite <- He'' ; cbn.
    right.
    split ; auto.
  * assert (Hin_ : In e'' (active s_)).
    {
      destruct (match hd_error (active s_) with
             | Some e =>
                 cnt e <=?
                 budget (Jobs (id e)) - duration (Jobs (id e))
             | None => false
             end &&
             negb
               match hd_error (active s_) with
               | Some e => cnt e =? 0
               | None => false
               end); auto.
      apply in_tl; auto.
    }  
   clear Hin''.
    injection Hc ; intros Hsc Hso ; rewrite <- Hsc in Hin_.
    cbn in Hin_.
    unfold decrease_all_del_func in Hin_.
    rewrite in_map_iff in Hin_.
    destruct Hin_ as (e' & Heq'' & Hin_).
    rewrite <- Heq''; cbn.
    remember (active s') as as'.
    destruct as' ; [inversion Hin_ | ].
    clear Hso ; cbn in Hin_.
    remember (pred (cnt e) =? 0) as pce0.
    
    destruct pce0.
    
    - left.
       assert (Hin : In e' (active s')).
       {
        rewrite <- Heqas' ; constructor 2 ; auto.
        }
    
     + exists e' ; repeat split; intros ; auto.
      ** constructor 2 ; auto.
      ** generalize (in_active_gt_budget_min_duration  _ _ _ Hrun _ Hin);
          intro ; lia.
      ** exfalso.
         rewrite H0 in Hrun.
         destruct ( running_is_first  _ _ _ _ Hrun) as
             (e_ & es'' & Heq & Heqid).
         rewrite Heq in Heqas' ; injection Heqas' ; intros Heq1 Heq2.
         rewrite <- Heq1, <- Heq2 in *.
         clear Heq1 Heq2.
         rewrite Heqid in *.
         apply active_unique_for_id in Hrun.
         assert (Hin' : In e (active s')).
         {
            rewrite Heq ; constructor; auto.           
         }
        
         generalize
         (unique_for_In _ _ (mk_Entry 0 0 0) _ _ Hrun Hin' Hin Heqid);
           intros Heqe; rewrite Heqe in *.
         unfold unique_for in Hrun.
         apply NoDup_map_inv in Hrun.
         rewrite Heq in *.
         rewrite NoDup_cons_iff in Hrun; intuition.
    - left.
      inversion Hin_.
      + rewrite <- H0 ; cbn.
        exists e ; repeat split; intros ; auto.
        ** assert (Hin : In e (active s')) ;
             [rewrite <- Heqas'; constructor; auto|].
           generalize
             (in_active_gt_budget_min_duration _ _ _ Hrun _ Hin);
          intro ; lia.
        ** lia.
        ** exfalso.
           destruct o.
           ++ 
           apply H1; clear H1.
           
            destruct ( running_is_first  _ _ _ _ Hrun) as
               (e_ & es'' & Heq & Heqid).
            rewrite Heq in Heqas'.
            injection Heqas' ; intros _ Hinj2; rewrite  Hinj2, Heqid;auto.
            
           ++ symmetry in Heqas'.
              rewrite (running_is_first'  _ _ _ _ _ _  Hrun Heqas') in H1;
                intuition.
      + exists e' ; repeat split; intros ; auto.
        ** constructor 2 ; auto.
        ** assert (Hin : In e' (active s')).
       {
        rewrite <- Heqas' ; constructor 2 ; auto.

       }
       generalize
             (in_active_gt_budget_min_duration  _ _ _ Hrun _ Hin);
          intro ; lia.
        ** exfalso.
           rewrite H1 in Hrun.
           destruct ( running_is_first  _ _ _ _ Hrun) as
             (e_ & es'' & Heq & Heqid).
         rewrite Heq in Heqas' ; injection Heqas' ; intros Heq1 Heq2.
         rewrite <- Heq1, <- Heq2 in *.
         clear Heq1 Heq2.
         rewrite Heqid in *.
        assert (Hin' : In e (active s')).
         {
            rewrite Heq ; constructor; auto.           
         }
       assert (Hin : In e' (active s')).
         {
            rewrite Heq ; constructor 2 ; auto.           
         }
       apply active_unique_for_id in Hrun.

         generalize
         (unique_for_In _ _ (mk_Entry 0 0 0) _ _ Hrun Hin' Hin Heqid);
           intros Heqe; rewrite Heqe in *.
         unfold unique_for in Hrun.
         apply NoDup_map_inv in Hrun.
         rewrite Heq in *.
         rewrite NoDup_cons_iff in Hrun; intuition.
Qed.

           
Lemma in_active_cnt_c: forall t s r b, 
    running  t = ((r,b),s) ->
    forall e,
      In e (active s) ->  cnt e  =  c (id e) t + (budget (Jobs (id e)) - duration (Jobs (id e))).
Proof.                        
induction t ; intros s r b0 Hrun e Hin.
*  rewrite running_0 in Hrun.
    remember (functional_update_entries  init) as rbs.
    destruct rbs as ((r' & b) & s').
    injection Hrun ; intros Hs Ho Hb  ; rewrite <- Hs , <- Hb, <- Ho in *.
    clear Hs Ho  Hb Hrun; cbn.

     do 2 rewrite surjective_pairing in Heqrbs.
    rewrite pair_equal_spec in Heqrbs.
    destruct Heqrbs as (Hr & Hs).
    rewrite Hs in *.
    cbn in *.    
   (*injection Hrun ; intros Hs _ ; rewrite <- Hs in *; clear Hrun Hs ; cbn in *.*)
   rewrite <- insert_all_contents_iff in Hin; destruct Hin as
      [Hin | Hin]; [| inversion Hin].
  rewrite in_map_iff in Hin.
  destruct Hin as (j & He & Hin').
  rewrite <- He ; cbn.
  generalize (job_duration_gt_0 j), (job_budget_enough j) ; intros;lia.
* generalize Hrun ; intro Hrun'.
  rewrite running_S in Hrun.
  case_eq (running  t) ; intros o' s' Hr.
  rewrite Hr in Hrun.
  case_eq (functional_update_counters s') ; intros o''  s'' Hc.
  rewrite Hc in Hrun.
 destruct o'.  
  specialize (IHt _ _ _ Hr).
  destruct (in_active_cnt_aux  _ _ _ _ _ _ _ Hr Hrun' _ Hin) as
      [(e' & Hin' & Hid' & Hreq &  Hrdiff ) | (Hin' & Hbud)].
 + specialize (IHt _ Hin').
  cbn.
  rewrite <- Hid'.
  unfold run.
  rewrite Hr; cbn.
  destruct o.
  - case (Nat.eq_dec n (id e')) ; intros ; subst. 
     ** rewrite NPeano.Nat.eqb_refl.
       destruct (Hreq (eq_refl _)) as (Hgt & Hreq').
       clear Hreq ; rewrite Hreq' ; auto.
       rewrite IHt.
       assert (Hcgt : c  (id e') t > 0).
       {
         generalize (in_active_gt_budget_min_duration  _ _ _ Hr _ Hin');
        intro ; lia.
       } 
       lia.       
     ** rewrite Hrdiff ;
         [ | intro H ; injection H ; apply n0; subst ; auto].
       rewrite  <- Nat.eqb_neq, Nat.eqb_sym in n0.
       rewrite n0.
       apply IHt.
   - rewrite Hrdiff ;
      [ | intro H ; discriminate].
    apply IHt.
  + rewrite filter_In in Hin'.
    destruct Hin' as (Hin' & Hlt).
    erewrite time_counter_now in Hin' ; eauto.
    rewrite jobs_arriving_at_prop in Hin'.
    rewrite Nat.ltb_lt in Hlt.
    erewrite c_is_duration_upto_arrival ; try rewrite Hin' ; eauto.
    rewrite Hbud.
    generalize (job_budget_enough (id e)) ; intro ; lia.    
Qed.


(* in_active_cnt_c *)
Lemma in_active_c_gt_0: forall t s r b,
    running  t = ((r,b),s) ->
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
 assert (Hin : In e (active s)).
 {
   rewrite Hact ; constructor ; auto.
 }  
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


Lemma arrived_now_active : forall  t i,
      i < N -> arrival (Jobs i) <= t -> c  i t > 0 ->
      forall r s b , running  t = ((r,b),s) ->
                   exists e, In e (active s) /\ id e = i.
Proof.
intros  t i HiN Harr .
remember (arrival (Jobs i)) as t'.
induction Harr ; intros  Hcgt r s b0 Hrun.
* exists (mk_Entry i (budget (Jobs i))
                   (((deadline (Jobs i)) - (arrival (Jobs i))))).
  split ; auto.
  destruct t'.
  + rewrite running_0 in Hrun.
     remember (functional_update_entries init) as rbs.
    destruct rbs as ((r' & b) & s').
    injection Hrun ; intros Hs Ho ; rewrite <- Hs in *;
      clear Hs Hrun; cbn.
     do 2 rewrite surjective_pairing in Heqrbs.
    rewrite pair_equal_spec in Heqrbs.
    destruct Heqrbs as (Hr & Hs).
    rewrite Hs in *.
    cbn in *.    
    (*injection Hrun ; intros Hs Hr ; rewrite <- Hs; clear Hs Hrun ; cbn in *.*)
  
    rewrite <- insert_all_contents_iff ; left.
    rewrite in_map_iff.
    exists i ; split ; auto.
    rewrite filter_In; split.
    -  rewrite jobs_arriving_at_prop, Heqt'; auto.
    - destruct N ; try lia.
      rewrite Nat.leb_le; lia.
 + rewrite running_S in Hrun.
   case_eq (running  t') ; intros o' s' Hr.
   rewrite Hr in Hrun.
   case_eq (functional_update_counters s') ; intros o'' s'' Hc.
   rewrite Hc in Hrun.
   generalize   (time_counter_now  _ _ _ Hr); intro Heq1.
   generalize (update_counters_changes_now   _ _ _ Hc); intro Heq2.
   
   remember (functional_update_entries s'') as rbs.
   destruct rbs as ((r' & b) & s''').
   symmetry in Heqrbs.   
   generalize (update_entries_leaves_now   _ _ _ Heqrbs) ; intro Heq3.
   injection Hrun ; intros Hs _ ; rewrite <- Hs ;
     clear Hs Hrun; cbn.
   injection Heqrbs ; intros Hs _ ; rewrite <- Hs ;
     clear Hs Heqrbs; cbn.
  
   
    rewrite <- insert_all_contents_iff ; left.
    rewrite in_map_iff.
    exists i ; split ; auto.
    rewrite filter_In; split.
    -  subst.
       rewrite jobs_arriving_at_prop.
       congruence.
    - destruct N ; try lia.
      rewrite Nat.leb_le; lia.
* cbn in Hcgt.
  rename m into t.
  case_eq (run i t); intros Hcas.
  +  
    unfold run in Hcas.
    case_eq (running t) ; intros o' s' Hr.
    rewrite Hr in Hcas.
    destruct o', o ; try discriminate.
    rewrite Nat.eqb_eq in Hcas.
    rewrite <- Hcas in * ; clear Hcas.
    destruct (running_is_first  _ _ _ _  Hr)
      as (e & es & Hact & Hide ).
    assert (Hcgt' : c  i t > 0).
  {
    destruct (run  i t) ; lia.  
  }
  specialize (IHHarr Hcgt').
  unfold run in Hcgt.
  rewrite Hr in Hcgt.
  rewrite Nat.eqb_refl in Hcgt.
  clear Hcgt'.
  rewrite <- Hide in *.
  clear IHHarr.
  exists (mk_Entry (id e) (pred (cnt e)) (pred (del e))) ; cbn.
  
  assert (Hcntsafe :
            cnt e >  1 +
             (budget (Jobs (id e))- (duration (Jobs (id e))))).
  {
    assert (Hin : In e (active s')) ;
      [rewrite Hact; constructor ; auto | ].
    rewrite (in_active_cnt_c   _ _ _ _  Hr _ Hin).
    lia.
  }
  
  rewrite running_S in Hrun.
  rewrite Hr in Hrun.
  case_eq (functional_update_counters  s') ; intros o'' s'' Hc.
  rewrite Hc in Hrun.
  remember (functional_update_entries  s'') as rbs.
  destruct rbs as ((r' & b') & s''').
  injection Hrun ; intros Hs Ho ; rewrite <- Hs in *;
      clear Hs Hrun; cbn.
   do 2 rewrite surjective_pairing in Heqrbs.
    rewrite pair_equal_spec in Heqrbs.
    destruct Heqrbs as (Hr' & Hs).
    rewrite Hs in *.
    cbn in *.    
  (*generalize   (time_counter_now _ _ _ _ Hr); intro Heq1.
  generalize (update_counters_changes_now  _ _ _ _ Hc); intro Heq2.
  generalize (update_entries_leaves_now  _ _ _ _ Heqrs) ; intro Heq3.
  rewrite Heq1 in Heq2.
  rewrite Heq2 in Heq3.*)
  
 (*. 
  injection Hrun ; intros Hs _ ; rewrite <- Hs ; cbn ; clear Hrun Hs.
  cbn.*)
  rewrite <- insert_all_contents_iff.
  rewrite in_map_iff.
  split ; auto.
  (*repeat rewrite snd_dadf_map.*)
   right.
    remember (active s'') as as''.
    destruct as''.
    - cbn.
      
      injection Hc ; intros Hs''' _ ; rewrite <- Hs''' in Heqas''
      ; cbn in * ; clear Hc Hs'''.
      unfold decrease_all_del_func in Heqas''.
      symmetry in Heqas''.
      apply map_eq_nil in Heqas''.
      remember (active s') as as'.
      destruct as'; try discriminate.
      injection Hact ; intros Heq Heq' ; rewrite Heq, Heq' in *.
      clear Heq Heq' Hact.
      cbn in Heqas''.
      remember (pred (cnt e)) as pce.
      destruct pce ; try discriminate.
      lia.
   - cbn.        
     injection Hc ; intros Hs' _ ; rewrite <- Hs' in * ; cbn ; clear Hc Hs' ; cbn in *.
     rewrite Hact in Heqas''.
     cbn in Heqas''.
     remember (pred (cnt e)) as pce.
     destruct pce ; try   lia.
     cbn in Heqas''.
     injection Heqas'' ; intros _ Heqe  ; rewrite  Heqe in *;
       cbn in *.
     rewrite andb_true_r.
     remember ( budget (Jobs (id e)) - duration (Jobs (id e))) as d.
     destruct d; [constructor ; auto | ].
     assert (Hpcegt : pce >  d); try lia.
     case_eq (pce <=? d); intros Hintr;
       [rewrite Nat.leb_le in Hintr; lia |].
     constructor; auto.
  + rewrite Hcas in Hcgt.
    specialize (IHHarr Hcgt). 
    unfold run in Hcas.
    case_eq (running  t) ; intros (o', b'') s' Hr.
    rewrite Hr in Hcas.
    destruct (IHHarr _ _ _  Hr) as (e & Hin & Hide).
    clear IHHarr.
    rewrite <- Hide in *.
    assert (Hosomei : o' <> Some (id e)).
    {
      intro H; rewrite H in *.
      rewrite Nat.eqb_refl in Hcas; discriminate.
    }  
    clear Hcas Hide.
    remember (active s') as as'.
    destruct as'; inversion Hin.
   - rewrite H in *;  clear H Hin.
     symmetry in Heqas'.
     generalize (running_is_first'   _ _ _ _ _ _ Hr Heqas');
       intros ; subst.
     exfalso ; apply Hosomei; auto.
   - clear Hin Hosomei.             
     rewrite running_S in Hrun.
     rewrite Hr in Hrun.
     case_eq (functional_update_counters s') ; intros o'' s'' Hc.
     rewrite Hc in Hrun.
     destruct (in_split _ _  H) as (l1 & l2 & Hcns).
     clear H.
     rewrite Hcns in Heqas'; clear Hcns.
          
     injection Hc ; intros Hs _; clear Hc.
     rewrite <- Heqas' in Hs ; cbn in Hs.
     
        (* injection Hrun ; intros Hs' _; clear Hrun.
     rewrite <- Hs' in Heqacts ; cbn in Heqacts ; clear Hs'.*)
     cbn in Hs.
     remember (pred (cnt e0)) as pce0.
     destruct pce0.
     **
       cbn in Hs.
       rewrite map_app in Hs.
       cbn in Hs.
       exists ({|
                         id := id e;
                         cnt := cnt e;
                         del := Init.Nat.pred (del e) |}); split; auto.
       
      remember (active s'') as as''. 
      (*rewrite <- Hs in Heqas''; cbn in Heqas''; clear Hs.*)
      remember (functional_update_entries  s'') as rbs.
      destruct rbs as ((r' & b) & s''').
      injection Hrun ; intros Hs'' Ho ; rewrite <- Hs'' in *;
      clear Hs'' Hrun; cbn.
      rewrite surjective_pairing in Heqrbs.
      rewrite pair_equal_spec in Heqrbs.
      destruct Heqrbs as (Hr' & Hs'').
      rewrite Hs'' in *.
      (* cbn in *.  
      injection Hrun ; intros Hs' _; clear Hrun.*)
      rewrite <- Hs ; cbn; clear Hs'' Hs.
      cbn.
      rewrite <- insert_all_contents_iff.
      right.
      cbn.
      assert (Hhd  : exists ee,
              ( hd_error
          (map
             (fun e1 : Entry =>
              {|
              id := id e1;
              cnt := cnt e1;
              del := Init.Nat.pred (del e1) |}) l1 ++
           {| id := id e; cnt := cnt e; del := Init.Nat.pred (del e) |}
           :: map
                (fun e1 : Entry =>
                 {|
                 id := id e1;
                 cnt := cnt e1;
                 del := Init.Nat.pred (del e1) |}) l2) =
                Some ee));
        [apply in_hd_error_some | ]; auto.
      destruct Hhd as (ee & Heqhd); rewrite Heqhd.
      assert (Hgt : (cnt ee <=? budget (Jobs (id ee)) - duration (Jobs (id ee))) = false).
      {
        destruct l1.
        * cbn in Heqhd.
          injection Heqhd ; intros; subst; cbn in *.
          assert (Hin : In e (active s')).
          {
            rewrite <- Heqas'; constructor 2; constructor; auto.
          }
          apply leb_correct_conv.
          generalize (in_active_gt_budget_min_duration  _ _ _ Hr _ Hin) ; intro Hgt ; lia.
        * cbn in *.
           injection Heqhd ; intros; subst; cbn in *.
          assert (Hin : In e1 (active s')).
          {
            rewrite <- Heqas'; constructor 2; constructor; auto.
          }
          apply leb_correct_conv.
          generalize (in_active_gt_budget_min_duration  _ _ _ Hr _ Hin) ; intro Hgt ; lia.
      }
      rewrite Hgt, andb_false_l.
      apply in_or_app.
      right ; constructor ; auto.
     ** case_eq (S pce0 =? 0); intros Hcas;
          [rewrite Nat.eqb_eq in Hcas; discriminate |].
       rewrite Hcas in Hs ; clear Hcas.
        cbn in Hs.
       rewrite map_app in Hs.
       cbn in Hs.
       exists ({|
                         id := id e;
                         cnt := cnt e;
                         del := Init.Nat.pred (del e) |}); split; auto.
       
      remember (active s'') as as''. 
      (*rewrite <- Hs in Heqas''; cbn in Heqas''; clear Hs.*)
      remember (functional_update_entries  s'') as rbs.
      destruct rbs as ((r' & b) & s''').
      injection Hrun ; intros Hs'' Ho ; rewrite <- Hs'' in *;
      clear Hs'' Hrun; cbn.
      rewrite surjective_pairing in Heqrbs.
      rewrite pair_equal_spec in Heqrbs.
      destruct Heqrbs as (Hr' & Hs'').
      rewrite Hs'' in *.
   (*    cbn in *.  
      injection Hrun ; intros Hs' _; clear Hrun.*)
      rewrite <- Hs ; cbn; clear Hs'' Hs.
      rewrite <- insert_all_contents_iff.
      right.
      rewrite andb_true_r.
      destruct (  match budget (Jobs (id e0)) - duration (Jobs (id e0)) with
      | 0 => false
      | S m' => pce0 <=? m'
                  end).
     ++ apply in_or_app.
      right ; constructor ; auto.
     ++ constructor 2;apply in_or_app.
      right ; constructor ; auto.
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

(*
Lemma fss_in_active_id_lt_N : forall t  s,
  snd (functional_scheduler_star t) = s  -> 
  forall e, In e (active s) -> id e < N.
Proof.
 intros t s Hs e Hin.
 destruct t.
 *
   cbn in Hs.
   rewrite <- Hs in Hin.
   inversion Hin.
* (* rewrite snd_drop_snd in Hs.*)
  rewrite  fss_running in Hs.
  remember (running t) as rs ; destruct rs as (r,s').
  remember (functional_update_counters s') as rs ; destruct rs as (r',s'').
  cbn in * ; subst.
  symmetry in Heqrs, Heqrs0.
  destruct (ids_after_update_counters _ _ _ _ Heqrs0 Hin) as (e' & Hin' & Heq & _ ).
  rewrite <- Heq.
  eapply in_active_id_lt_N ; eauto.
Qed.

  
Lemma fss_active_unique_for_id : forall t  s,
  snd (functional_scheduler_star t) = s  -> unique_for id (active s).
Proof.
intros t s Hs.  
destruct t.
* cbn in Hs.
  rewrite <- Hs.
  unfold unique_for.
  cbn.
  apply NoDup_nil.
*  
  rewrite  fss_running in Hs.
  remember (running t) as rs ; destruct rs as (r,s').
  remember (functional_update_counters s') as rs ; destruct rs as (r',s'').
  cbn in Hs  ;  subst.
  symmetry in Heqrs, Heqrs0.
  unfold unique_for.
  destruct (update_counters_effect_on_active _ _ _ Heqrs0) as [Ha | Ha].
  + rewrite Ha.
      eapply active_unique_for_id ; eauto.
  + rewrite Ha.
      apply NoDup_tl.
      eapply active_unique_for_id ; eauto.
 Qed.
     *)
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
  remember (
            insert_all Entry
              (fun e1 e2 : Entry =>
               deadline (Jobs (id e1)) <=?
               deadline (Jobs (id e2)))
              (map
                 (fun j : CNat =>
                  {|
                  id := j;
                  cnt := budget (Jobs j);
                  del := deadline (Jobs j) -
                         arrival (Jobs j) |})
                 (filter (fun j : nat => j <? N)
                    (jobs_arriving_at (now s))))
              (if
                match hd_error (active s) with
                | Some e =>
                    cnt e <=?
                    budget (Jobs (id e)) -
                    duration (Jobs (id e))
                | None => false
                end &&
                negb
                  match hd_error (active s) with
                  | Some e => cnt e =? 0
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
    running  t  =  ( (o, b) ,s)  ->
       forall e,  In e (active s) ->
             del e = deadline (Jobs (id e)) - t.
Proof.
induction t  ; intros o b s  Hrun e Hin.
*  rewrite running_0 in Hrun.
   cbn in *.
   unfold functional_update_entries, init in Hrun.
   cbn in Hrun.
   remember (insert_all Entry
              (fun e1 e2 : Entry =>
               deadline (Jobs (id e1)) <=?
               deadline (Jobs (id e2)))
              (map
                 (fun j : CNat =>
                  {|
                  id := j;
                  cnt := budget (Jobs j);
                  del := deadline (Jobs j) -
                         arrival (Jobs j) |})
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
  remember (  insert_all _  (fun e1 e2 : Entry =>
               deadline (Jobs (id e1)) <=?
               deadline (Jobs (id e2)))
              (map
                 (fun j : CNat =>
                  {|
                  id := j;
                  cnt := budget (Jobs j);
                  del := deadline (Jobs j) -
                         arrival (Jobs j) |})
                 (filter (fun j : nat => j <? N)
                    (jobs_arriving_at (now s''))))
              (if
                match hd_error (active s'') with
                | Some e =>
                    cnt e <=?
                    budget (Jobs (id e)) -
                    duration (Jobs (id e))
                | None => false
                end &&
                negb
                  match hd_error (active s'') with
                  | Some e => cnt e =? 0
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
             duration (Jobs (id e1))) &&
                  negb (cnt e1 =? 0)) ; auto.
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
