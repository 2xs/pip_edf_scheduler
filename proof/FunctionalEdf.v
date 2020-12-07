Require Import List.
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
let b'' :=  match hd_error s.(active) with
     | Some e =>
         del e =? 0
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
             del := S (deadline (Jobs j) - (arrival (Jobs j))) |}) l) active1 in

( match active2 with
     | [] => (None,b'')
     | e :: _ => (Some (id e), b'')
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
  

  

Fixpoint running (t : nat) : (option nat * State) :=
  match t with
    0 => drop_snd (functional_update_entries init)
  | S t' => let (_,s') := running  t' in
            let (_,s'') := functional_update_counters  s' in
            drop_snd (functional_update_entries s'')
  end.                                    


(* for better controlled rewriting *)
Lemma running_0 :  running  0 = drop_snd (functional_update_entries  init).
Proof.  
intros;  
reflexivity.
Qed.

Lemma running_S : forall t,
    running (S t) = let (_,s') := running t in
            let (_,s'') := functional_update_counters  s' in
            drop_snd (functional_update_entries  s'').
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

Lemma active_from_earlier_arrivals : forall  t o s,
    running t = (o,s) ->
    forall e,
      In e (active s) ->
          exists t', t' <= t /\
                     In (id e)
                        (filter (fun j => j <? N) (jobs_arriving_at t')).
Proof.
  induction t; intros o s Hrun e Hin.    
  * rewrite running_0 in Hrun.
    exists 0 ; split; auto.
    remember (functional_update_entries  init) as rbs.
    destruct rbs as ((r & b) & s').
    injection Hrun ; intros Hs _.
    rewrite <- Hs in Hin ; cbn in Hin; clear Hs.
    rewrite surjective_pairing in Heqrbs.
    rewrite pair_equal_spec in Heqrbs.
    destruct Heqrbs as (_ & Hs).
    rewrite Hs in *.
    cbn in Hin.
    rewrite <- insert_all_contents_iff in Hin;
      destruct Hin as [ Hin | Hin]; [|inversion Hin].
    rewrite in_map_iff in Hin.
    destruct Hin as (i & Heqe & Hin).
    rewrite <- Heqe; auto.
  *  rewrite running_S in Hrun.
     case_eq (running t) ; intros or sr Hr; rewrite Hr in *.
     specialize (IHt  _ _ (eq_refl _)).
     case_eq (functional_update_counters sr) ; intros oc sc Hc; rewrite Hc in *.
       remember (functional_update_entries sc) as rbs.
       destruct rbs as ((r & b) & s').
     injection Hrun ; intros Hs _.
     rewrite <- Hs in Hin; cbn in Hin; clear Hs.
     rewrite surjective_pairing in Heqrbs.
    rewrite pair_equal_spec in Heqrbs.
    destruct Heqrbs as (_ & Hs).
    rewrite Hs in *.
    cbn in Hin.
     rewrite <- insert_all_contents_iff in Hin;
        destruct Hin as [ Hin | Hin].
     + rewrite in_map_iff in Hin.
       destruct Hin as (i & Heqe & Hin).
       rewrite <- Heqe in*; auto ; cbn.    
       exists (now sc); split; auto.
       injection Hc ; intros Hsc _.
       rewrite <- Hsc; cbn ; clear Hsc.
       erewrite  time_counter_now  ; eauto.
     + assert (Hin' : In e (active sc)).
       - destruct (hd_error (active sc)); auto.
          ** destruct ((cnt e0 <=?
             budget (Jobs (id e0)) -
             duration (Jobs (id e0))) && negb (cnt e0 =? 0))
            ; auto.
           destruct (active sc); auto; constructor 2 ; auto.
       - clear Hin.
          injection Hc ; intros Hsc _.
          rewrite <- Hsc in Hin'; cbn in Hin'; clear Hsc.
          unfold decrease_all_del_func in Hin'.
          rewrite in_map_iff in Hin'.
          destruct Hin' as (e' & Heqe' & Hin').
          destruct (active sr) ; [inversion Hin' | ].
          cbn in *.
          destruct (pred (cnt e0)); cbn in *.
         ** specialize (IHt _ (or_intror Hin')).
            destruct IHt as (t' & Hle & Hin).
            exists t' ; split ; auto.
            rewrite <- Heqe' ; auto.
         ** destruct Hin' as [Heqe'' | Hin'].
           ++  specialize (IHt _ (or_introl (eq_refl _))).
               destruct IHt as (t' & Hle & Hin).
               exists t' ; split ; auto.
               rewrite <- Heqe', <-Heqe'' ; auto.
           ++ specialize (IHt _ (or_intror Hin')).
            destruct IHt as (t' & Hle & Hin).
            exists t' ; split ; auto.
            rewrite <- Heqe' ; auto.  
Qed.

 
Definition run(i t : nat) : bool :=
  match  running  t with 
        (None, _) => false
       | (Some k, _) =>   (Nat.eqb i k)
      end.


  Fixpoint c (i t : nat) : nat :=
      match t with
        0 => duration (Jobs i)
      |S t' => if run i t'  then (c i t') - 1 else c  i t'                
      end.

Lemma  at_most_one_runs: forall (i j t : nat),
      i < N -> j < N ->
      run i t  = true -> run j t = true -> i = j.
Proof.  
  intros  i j t HiN HjN Hruni Hrunj.
  unfold run in *.
  case_eq (running t) ; intros.
  rewrite H in *.
  destruct o; try discriminate.
  rewrite Nat.eqb_eq in * ; subst ; auto.
Qed.

Lemma running_is_first: forall t n s,
    running  t = (Some n,s)  ->
    exists e es,  s.(active) = e::es  /\ e.(id) = n.
Proof.
  intros  t n s Hrun.
  destruct t.
  * rewrite running_0 in Hrun.
    remember (functional_update_entries init) as rbs.
    destruct rbs as ((r & b) & s').
    injection Hrun ; intros Hs Ho ; rewrite <- Hs in *;
      clear Hs Hrun; cbn.
     rewrite surjective_pairing in Heqrbs.
    rewrite pair_equal_spec in Heqrbs.
    destruct Heqrbs as (Hr & Hs).
    rewrite Hs in *.
    cbn in *.    
  case_eq ( insert_all Entry
           (fun e1 e2 : Entry =>
            deadline (Jobs (id e1)) <=? deadline (Jobs (id e2)))
           (map
              (fun j : CNat =>
               {|
               id := j;
               cnt := budget (Jobs j);
               del := S (deadline (Jobs j) - arrival (Jobs j)) |})
              (filter (fun j : nat => j <? N) (jobs_arriving_at 0))) []); intros.
  + cbn in H. rewrite H in *.
    injection Hr  ; intros ; subst.
    discriminate.
  +  cbn in H.
     rewrite H in *.
       injection Hr ; intros Hinj Heq; rewrite Hinj in * ; clear Hr.
       exists e,l; split ; auto.
       rewrite Ho in Heq; injection Heq;
         intros ; auto.
* rewrite running_S in Hrun.
  case_eq  (running t); intros o s' Hr.
  rewrite Hr in Hrun.
  case_eq (functional_update_counters  s'); intros o'' s'' Hc.
  rewrite Hc in Hrun.
   remember (functional_update_entries  s'') as rbs.
    destruct rbs as ((r & b) & s''').
    injection Hrun ; intros Hs Ho ; rewrite <- Hs in *;
      clear Hs Hrun; cbn.
     rewrite surjective_pairing in Heqrbs.
    rewrite pair_equal_spec in Heqrbs.
    destruct Heqrbs as (Hr' & Hs).
    rewrite Hs in *.
    cbn in *.
  (*injection Hrun ; intros Hs Ho; rewrite <- Hs in * ; cbn in *;
    clear Hs Hrun.*)
  case_eq (insert_all Entry
      (fun e1 e2 : Entry =>
       deadline (Jobs (id e1)) <=? deadline (Jobs (id e2)))
      (map
         (fun j : CNat =>
          {|
          id := j;
          cnt := budget (Jobs j);
          del := S (deadline (Jobs j) - arrival (Jobs j)) |})
         (filter
            (fun j : nat =>
             match N with
             | 0 => false
             | S m' => j <=? m'
             end) (jobs_arriving_at (now s''))))
      (if
        match hd_error (active s'') with
        | Some e0 =>
            cnt e0 <=?
            budget (Jobs (id e0)) - duration (Jobs (id e0))
        | None => false
        end &&
        negb
          match hd_error (active s'') with
          | Some e0 => cnt e0 =? 0
          | None => false
          end
       then tl (active s'')
       else active s'')) ; intros.
  + cbn in H.  rewrite H in *.
    injection Hr' ; intros ; subst.
    discriminate.
  + rewrite H in *.
    exists e,l ; split ; auto.
    injection Hr' ; intros ; subst.
    injection H1 ; intros ; subst; auto.
Qed.

Lemma run_after_arrival :
  forall ( i t : nat), i < N ->
         run i t = true -> arrival (Jobs i) <= t.
Proof.
intros i t HiN Hrun.
unfold run in Hrun.
case_eq (running t) ; intros o s Hrunning.
rewrite Hrunning in Hrun.
destruct o; try discriminate.
rewrite Nat.eqb_eq in Hrun.
rewrite <- Hrun in *; clear Hrun.
destruct ( running_is_first  _ _ _ Hrunning) as (e & es & Heqe & Hine).
rewrite <- Hine in *; clear Hine.
assert (Hin : In e (active s)).
{
  rewrite Heqe ; constructor; auto.
}
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



Lemma in_active_gt_budget_min_duration : forall  t s r,
    running t = (r,s) ->
    forall e,
      In e (active s) -> cnt e > budget (Jobs (id e)) - duration (Jobs (id e)).
Proof.
induction t ; intros s r Hrun e Hin.
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
  (*injection Hrun ; intros Hs _ ; rewrite <- Hs in *; cbn in *;
    clear Hs Hrun. *)
  rewrite <- insert_all_contents_iff in Hin; destruct Hin as
      [Hin | Hin]; [| inversion Hin].
  rewrite in_map_iff in Hin.
  destruct Hin as (i & He & Hin').
  rewrite <- He ; cbn.
  generalize (job_duration_gt_0 i), (job_budget_enough i) ; intros;lia.
* rewrite running_S in Hrun.
  case_eq (running  t) ; intros o' s' Hr.
  rewrite Hr in Hrun.
  case_eq (functional_update_counters s') ; intros o''  s'' Hc.
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
  (*injection Hrun ; intros Hs _ ; rewrite <- Hs in * ; clear Hs Hrun.
  cbn in Hin.*)
   rewrite <- insert_all_contents_iff in Hin; destruct Hin as
       [Hin | Hin].
   + rewrite in_map_iff in Hin.
     destruct Hin as (i & He & Hin').
      rewrite <- He ; cbn.
      generalize (job_duration_gt_0 i), (job_budget_enough i) ;
        intros; lia.
   + remember (match hd_error (active s'') with
            | Some e =>
                cnt e <=?
                budget (Jobs (id e)) - duration (Jobs (id e))
            | None => false
            end &&
            negb
              match hd_error (active s'') with
              | Some e => cnt e =? 0
              | None => false
              end) as b'.
     symmetry in Heqb'.
     destruct b'.
   - case_eq (hd_error (active s'')); intros.
     ** 
(*rewrite H in Heqb.
        rewrite andb_true_iff in Heqb.
        destruct Heqb as (Hineq1 & Heq2).*)
       clear H Heqb'.        
        injection Hc ; intros Hsc _ ; rewrite <- Hsc in * ; clear Hc Hsc.
        cbn in Hin.
        unfold decrease_all_del_func in Hin.
       cbn in Hin.
      remember (active s') as as'.
      destruct as' ; [inversion Hin | ].
      cbn in Hin.
      remember (pred (cnt e1)) as pc1.
      destruct pc1 ; cbn in Hin.
       ++ apply in_tl in Hin.
           rewrite in_map_iff in Hin.
            destruct Hin as (i & He & Hin').
            rewrite <- He ; cbn.
            eapply IHt ; eauto.
            rewrite <- Heqas'.
            constructor 2 ; auto.
      ++  rewrite in_map_iff in Hin.
            destruct Hin as (i & He & Hin').
            rewrite <- He ; cbn.
            eapply IHt ; eauto.
            rewrite <- Heqas'.
            constructor 2 ; auto.
          ** rewrite H in Heqb'; discriminate.
   - destruct (in_hd_or_tl _ _ Hin).
     ** rewrite H in Heqb'.
        rewrite andb_false_iff in Heqb'.
        destruct Heqb' as [Hcnt1 | Hcnt2].
       ++ rewrite Nat.leb_gt in Hcnt1; auto.
       ++ assert (cnt e = 0).
          {
            destruct (cnt e) ; auto ; discriminate.
          }
          clear Hcnt2.
          exfalso.
          injection Hc ; intros Hsc _ ;
            rewrite <- Hsc in * ; clear Hsc Hc H;
              cbn in *.
          unfold decrease_all_del_func in Hin.
          rewrite in_map_iff in Hin.
          destruct Hin as (i & He & Hin').
          rewrite <- He in H0; cbn in H0; clear He.
          remember (active s') as as'.
          destruct as' ; [inversion Hin' | ].
           --  cbn in Hin'.
                remember (pred (cnt e0)) as pc0.
                destruct pc0 ; cbn in Hin'.
                *** assert (Hin : In i (active s')).
                    {
                      rewrite <- Heqas' ;
                      constructor 2; auto.
                    }
                    specialize (IHt _  _ Hr _ Hin);
                      lia.
                ***
                  destruct Hin'.
               +++ rewrite <- H in H0;cbn in H0;
                     lia.
               +++   assert (Hin : In i (active s')).
                    {
                      rewrite <- Heqas' ;
                      constructor 2; auto.
                    }
                    specialize (IHt _  _ Hr _ Hin);
                      lia.
       ** clear Hin; rename H into Hin.
          clear Heqb'.
          {
           injection Hc ; intros Hsc _ ; rewrite <- Hsc in * ; clear Hc Hsc.
           cbn in Hin.
           unfold decrease_all_del_func in Hin.
           cbn in Hin.
           remember (active s') as as'.
           destruct as' ; [inversion Hin | ].
           cbn in Hin.
           remember (pred (cnt e0)) as pc1.
           destruct pc1 ; cbn in Hin.
           ++ apply in_tl in Hin.
           rewrite in_map_iff in Hin.
            destruct Hin as (i & He & Hin').
            rewrite <- He ; cbn.
            eapply IHt ; eauto.
            rewrite <- Heqas'.
            constructor 2 ; auto.
      ++  rewrite in_map_iff in Hin.
            destruct Hin as (i & He & Hin').
            rewrite <- He ; cbn.
            eapply IHt ; eauto.
            rewrite <- Heqas'.
            constructor 2 ; auto.
      }     
Qed.


Lemma active_unique_for_id :
  forall t r s,
  running t = (r,s) ->
  unique_for id (active s).
Proof.
induction t ; intros r s Hrun.  
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
  (*injection Hrun; intros Hs _ ; rewrite <- Hs ; cbn.*)
  eapply  insert_all_unique ; eauto.
  + unfold unique_for.
    rewrite map_map, map_id.
    apply NoDup_filter.
    rewrite NoDup_nth with (d := 0).
    intros.
    generalize (jobs_arriving_at_unique _ _ _ _ H H0 H1); intuition.
  +  apply NoDup_nil.
* rewrite running_S in Hrun.
  case_eq  (running  t); intros o s' Hr.
  rewrite Hr in Hrun.
  case_eq (functional_update_counters s'); intros o'' s'' Hc.
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
  case_eq ( insert_all Entry
       (fun e1 e2 : Entry =>
        deadline (Jobs (id e1)) <=? deadline (Jobs (id e2)))
       (map
          (fun j : CNat =>
           {|
           id := j;
           cnt := budget (Jobs j);
           del := S (deadline (Jobs j) - arrival (Jobs j)) |})
          (filter
             (fun j : nat =>
              match N with
              | 0 => false
              | S m' => j <=? m'
              end) (jobs_arriving_at (now s''))))
       (if
         match hd_error (active s'') with
         | Some e =>
             cnt e <=?
             budget (Jobs (id e)) - duration (Jobs (id e))
         | None => false
         end &&
         negb
           match hd_error (active s'') with
           | Some e => cnt e =? 0
           | None => false
           end
        then tl (active s'')
        else active s'')) ; intros; try apply NoDup_nil.
    rewrite <- H ; clear H Ho.
    eapply insert_all_unique; eauto.
    + rewrite map_map, map_id.
      intros e' Hin Hin'.
      rewrite in_map_iff in Hin'.
      destruct Hin' as (e'' & Heq'' & Hin').
      rewrite filter_In in Hin.
      destruct Hin as (Hin & HN).
      destruct N; try discriminate.
      erewrite update_counters_changes_now in Hin ; eauto.
      erewrite time_counter_now in Hin ; eauto.
      rewrite jobs_arriving_at_prop in Hin.
      assert (Hin'' : In e'' (active s'')).
      {
        destruct ( match hd_error (active s'') with
             | Some e =>
                 cnt e <=?
                 budget (Jobs (id e)) - duration (Jobs (id e))
             | None => false
             end &&
             negb
               match hd_error (active s'') with
               | Some e => cnt e =? 0
               | None => false
               end) ; intros; auto.
       apply in_tl ; auto.        
      }
    clear Hin'.  
    injection Hc ; intros Hs' _ ; rewrite <- Hs' in *; clear Hs' Hc.
    cbn in Hin''.
    unfold decrease_all_del_func in Hin''.
    rewrite in_map_iff in Hin''.
    destruct Hin'' as (e_ & He'' & Hin'').
    rewrite <- He'' in *; cbn in *; clear He''.
    rewrite <- Heq'' in *; clear Heq''.
    remember (active s') as as'.
    destruct as'; [inversion Hin'' | ].
    remember (pred (cnt e0)) as pc0.
    destruct pc0.
    - cbn in *.
      assert (Hin' : In e_ (active s')).
      {
        rewrite <- Heqas'; constructor 2; auto.
      }
      destruct (active_from_earlier_arrivals  _ _ _ Hr _ Hin')
        as (t' & Ht' & Hin''').
      rewrite filter_In in Hin'''.      
      destruct Hin''' as (Hin''' & _).
      rewrite jobs_arriving_at_prop in Hin'''.
      lia.
    -  cbn in Hin''.
       destruct Hin'' as [Heq | Hin'''].
       **
         rewrite <- Heq in *; clear Heq; cbn in *.
          assert (Hin' : In e0 (active s')).
          {
           rewrite <- Heqas'; constructor; auto.
          }
                 
      destruct (active_from_earlier_arrivals  _ _ _ Hr _ Hin')
        as (t' & Ht' & Hin''').
      rewrite filter_In in Hin'''.      
      destruct Hin''' as (Hin''' & _).
      rewrite jobs_arriving_at_prop in Hin'''.
      lia.
      **  cbn in *.
      assert (Hin' : In e_ (active s')).
      {
        rewrite <- Heqas'; constructor 2; auto.
      }
      destruct (active_from_earlier_arrivals  _ _ _ Hr _ Hin')
        as (t' & Ht' & Hin'').
      rewrite filter_In in Hin''.      
      destruct Hin'' as (Hin'' & _).
      rewrite jobs_arriving_at_prop in Hin''.
      lia.
   + unfold unique_for.
     rewrite map_map, map_id.
     apply NoDup_filter.
     rewrite NoDup_nth with (d := 0).
     intros.
     generalize (jobs_arriving_at_unique _ _ _ _ H H0 H1); intuition.
   + unfold unique_for in *.
     assert (Hnod'' : NoDup (map id (active s''))).
     {
       injection Hc; intros Hs' _ ; rewrite <- Hs' in *; clear Hs' Hc ; cbn.
       unfold decrease_all_del_func.
       rewrite map_map.
    remember (active s') as as'; cbn.
    destruct as'.
    *  apply NoDup_nil.
    *  cbn.
    remember (pred (cnt e0)) as pc0.
    destruct pc0.
    - cbn in *.
      specialize (IHt _ _ Hr).
      rewrite <- Heqas' in IHt.
      cbn in IHt.
      rewrite NoDup_cons_iff in IHt; intuition.
    - cbn.
      specialize (IHt _ _ Hr).
      rewrite <- Heqas' in IHt; auto.
   }   

   destruct ( match hd_error (active s'') with
         | Some e0 =>
             cnt e0 <=?
             budget (Jobs (id e0)) - duration (Jobs (id e0))
         | None => false
         end &&
         negb
           match hd_error (active s'') with
           | Some e0 => cnt e0 =? 0
           | None => false
           end); intros; auto.
     destruct (active s'') ; auto.
     cbn in *.
     rewrite NoDup_cons_iff in Hnod'' ; intuition.
Qed.


Lemma running_is_first': forall t r s e es,
    running  t = (r,s)  ->
    s.(active) = e::es -> r = Some (id e).
Proof.
  intros  t r s e es  Hrun Hact.
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
forall  t o r s' s'',
running  t = (o,s') ->
running  (S t) = (r,s'') ->
forall e'', In e'' (active s'') ->
           (((exists e', In e' (active s') /\ id e' = id e'' /\
                       (o = Some (id e') -> cnt e' > 0 /\ cnt e'' = cnt e' - 1) /\
                       (o <> Some (id e') -> cnt e'' = cnt e'))                         
            ) \/
            In (id e'')
               (filter (fun j => j <? N)(jobs_arriving_at (now s''))) /\
            cnt e'' = budget (Jobs (id e''))).
Proof.
  intros  t o r s' s'' Hrun Hrun1 e'' Hin''.
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
         rewrite H in Hrun.
         destruct ( running_is_first  _ _ _ Hrun) as
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
      + rewrite <- H ; cbn.
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
           apply H0; clear H0.
           
            destruct ( running_is_first  _ _ _ Hrun) as
               (e_ & es'' & Heq & Heqid).
            rewrite Heq in Heqas'.
            injection Heqas' ; intros _ Hinj2; rewrite  Hinj2, Heqid;auto.
            
           ++ symmetry in Heqas'.
              rewrite (running_is_first'  _ _ _ _ _ Hrun Heqas') in H0;
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
           rewrite H0 in Hrun.
           destruct ( running_is_first  _ _ _ Hrun) as
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

           
Lemma in_active_cnt_c: forall t s r,
    running  t = (r,s) ->
    forall e,
      In e (active s) ->  cnt e  =  c (id e) t + (budget (Jobs (id e)) - duration (Jobs (id e))).
Proof.                        
induction t ; intros s r Hrun e Hin.
*  rewrite running_0 in Hrun.
    remember (functional_update_entries  init) as rbs.
    destruct rbs as ((r' & b) & s').
    injection Hrun ; intros Hs Ho ; rewrite <- Hs in *;
      clear Hs Hrun; cbn.
     rewrite surjective_pairing in Heqrbs.
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
  
  specialize (IHt _ _ Hr).
  destruct (in_active_cnt_aux  _ _ _ _ _ Hr Hrun' _ Hin) as
      [(e' & Hin' & Hid' & Hreq &  Hrdiff ) | (Hin' & Hbud)].
 + specialize (IHt _ Hin').
  cbn.
  rewrite <- Hid'.
  unfold run.
  rewrite Hr; cbn.
  destruct o'.
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
Lemma in_active_c_gt_0: forall t s r,
    running  t = (r,s) ->
    forall e,
      In e (active s) ->  c  (id e) t > 0.
Proof.
  intros  t s r Hrun e Hin.
  specialize (in_active_cnt_c  _ _ _ Hrun _ Hin); intro Hnct.
  specialize (in_active_gt_budget_min_duration   _ _ _ Hrun _ Hin);
    intro Hgt.
  lia.
Qed.


Lemma notrunning_when_c_0 :  forall  i t,  i < N ->
                                            c i t = 0 -> run  i t = false.
 Proof.
 intros  i t HiN Hc0.   
 unfold run.
 case_eq (running t); intros o s Hr.
 destruct o ; auto.
 rewrite Nat.eqb_neq.
 intro Heq ; subst.
 destruct (running_is_first  _ _ _ Hr) as (e & es & Hact & Heq).
 rewrite <- Heq in * ; clear Heq.
 assert (Hin : In e (active s)).
 {
   rewrite Hact ; constructor ; auto.
 }  
 generalize (in_active_c_gt_0  _ _ _ Hr _ Hin); intro; lia.
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
      forall r s , running  t = (r,s) ->
                   exists e, In e (active s) /\ id e = i.
Proof.
intros  t i HiN Harr .
remember (arrival (Jobs i)) as t'.
induction Harr ; intros  Hcgt r s  Hrun.
* exists (mk_Entry i (budget (Jobs i))
                   (S((deadline (Jobs i)) - (arrival (Jobs i))))).
  split ; auto.
  destruct t'.
  + rewrite running_0 in Hrun.
     remember (functional_update_entries init) as rbs.
    destruct rbs as ((r' & b) & s').
    injection Hrun ; intros Hs Ho ; rewrite <- Hs in *;
      clear Hs Hrun; cbn.
     rewrite surjective_pairing in Heqrbs.
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
    destruct o' ; try discriminate.
    rewrite Nat.eqb_eq in Hcas.
    rewrite <- Hcas in * ; clear Hcas.
    destruct (running_is_first  _ _ _ Hr)
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
    rewrite (in_active_cnt_c   _ _ _ Hr _ Hin).
    lia.
  }
  
  rewrite running_S in Hrun.
  rewrite Hr in Hrun.
  case_eq (functional_update_counters  s') ; intros o'' s'' Hc.
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
     case_eq (pce <=? d); intros ;
       [rewrite Nat.leb_le in H; lia |].
     constructor; auto.
  + rewrite Hcas in Hcgt.
    specialize (IHHarr Hcgt). 
    unfold run in Hcas.
    case_eq (running  t) ; intros o s' Hr.
    rewrite Hr in Hcas.
    destruct (IHHarr _ _ Hr) as (e & Hin & Hide).
    clear IHHarr.
    rewrite <- Hide in *.
    assert (Hosomei : o <> Some (id e)).
    {
      intro H; rewrite H in *.
      rewrite Nat.eqb_refl in Hcas; discriminate.
    }  
    clear Hcas Hide.
    remember (active s') as as'.
    destruct as'; inversion Hin.
   - rewrite H in *;  clear H Hin.
     symmetry in Heqas'.
     generalize (running_is_first'   _ _ _ _ _ Hr Heqas');
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
  case_eq (running  t) ; intros r s Hr.
  destruct (arrived_now_active  _ _ HiN Harr Hc _ _ Hr)
    as (e & Hin & _).
  unfold run.
  rewrite Hr.
  remember (active s) as acts.
  destruct acts; [inversion Hin | ].
  symmetry in Heqacts.  
  rewrite (running_is_first'  _ _ _ _ _ Hr Heqacts) in *.
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



  
Lemma active_sorted : forall t r s,
    running  t  =  (r,s) ->
    is_sorted _ (fun x y : Entry =>
                 deadline (Jobs (id x)) <=? deadline (Jobs (id y)))
                             (active s).
Proof.
    induction t; intros r s Hf.
    * rewrite running_0 in Hf.
      remember (functional_update_entries init) as rbs.
      destruct rbs as ((r' & b) & s''').
      injection Hf ; intros Hs Ho ; rewrite <- Hs in *;
      clear Hs Hf; cbn.
      rewrite surjective_pairing in Heqrbs.
      rewrite pair_equal_spec in Heqrbs.
      destruct Heqrbs as (Hr' & Hs).
      rewrite Hs in *.
      cbn.
     (* injection Hf; intros ; subst; cbn.*)
      apply insert_all_sorted.
        +intros a b' ; destruct a,b'; cbn.
          do 2 rewrite Nat.leb_le.
          lia.
     + constructor.
    * rewrite running_S in Hf.
      case_eq (running t) ; intros o s' Hf'.
      rewrite Hf' in Hf.
      specialize (IHt _ _ Hf').
      unfold functional_scheduler in Hf.
      
      case_eq (functional_update_counters s') ; intros o' s'' Hc.
      rewrite Hc in Hf.
      clear Hf'.
      assert (Hse'' : is_sorted Entry
              (fun x y : Entry =>
                deadline (Jobs (id x)) <=? deadline (Jobs (id y))) 
              (active s'')).


      {
        
         injection Hc ; intros Hs _ ; rewrite <- Hs ; clear Hs.
         cbn.
         unfold decrease_all_del_func.
          remember (active s') as as'.
          destruct as'.
          * constructor.
          * cbn.
            remember (pred (cnt e)) as pce.
            destruct pce.
            + cbn.
              apply is_sorted_map; cbn; auto.
               apply is_sorted_tail with (a :=e); auto.
            + apply is_sorted_map ; auto.
              cbn.
              destruct as'.
                - constructor.
                - inversion IHt ; constructor ; auto.
        }  
      {
        clear IHt Hc.
        remember (functional_update_entries  s'') as rbs.
        destruct rbs as ((r' & b) & s''').
        injection Hf ; intros Hs Ho ; rewrite <- Hs in *;
         clear Hs Hf; cbn.
         rewrite surjective_pairing in Heqrbs.
         rewrite pair_equal_spec in Heqrbs.
         destruct Heqrbs as (Hr' & Hs).
         rewrite Hs in *.
       (* injection Hf ; intros Hs _ ; rewrite <- Hs ; clear Hs Hf.*)
        cbn.
        apply insert_all_sorted.
        {
          intros a b' ; destruct a,b'; cbn.
          do 2 rewrite Nat.leb_le.
          lia.
        }  
        {
          remember (active s'') as as''.
          destruct as''.
          * constructor.
          * cbn.
            case_eq
              ((cnt e <=?
                budget (Jobs (id e)) - duration (Jobs (id e))) &&
                     negb (cnt e =? 0)) ; intros Hcas; auto.
            eapply is_sorted_tail; eauto.
        }
     }   
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
    drop_snd (functional_scheduler_star (S t)) =
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
  case_eq ( functional_update_entries s') ; intros.
  case_eq (functional_update_counters  s0) ; intros.
  destruct p.
  cbn.
  rewrite pair_equal_spec; split; auto.
    injection H0 ; intros Hs _ ; rewrite <- Hs in * ; auto.
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
  destruct r' ; try discriminate.
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
case_eq (running t) ; intros r s' Hr.
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
   destruct (running_is_first  _ _ _ Hr)
       as (e & es & Hact & Hid).
   rewrite <- Hid in * ; clear Hid.
   destruct (arrived_now_active  _ _ HjN Harrj Hcj _ _ Hr)
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

Lemma ids_after_update_counters : forall s r s' e',
  functional_update_counters s = (r,s') ->
  In e' (active s') -> exists e,  In e (active s) /\ id e = id e'.
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
  apply f_equal with (f := id) in Heq.
  cbn in Heq.
  destruct (Init.Nat.pred (cnt e)).
  + rewrite Nat.eqb_refl in Hin.
      exists e'' ; cbn ; split ; auto.
  + 
    assert( Hn : S n <> 0) ; auto.
    rewrite <- Nat.eqb_neq in Hn.    
    rewrite Hn in Hin; clear Hn.
    inversion Hin ; subst.
    - cbn in Heq.  
      exists e ; cbn ; split ; auto.    
    -  exists  e'' ; cbn ; split ; auto.    
Qed.

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
* rewrite snd_drop_snd in Hs.
  rewrite  fss_running in Hs.
  remember (running t) as rs ; destruct rs as (r,s').
  remember (functional_update_counters s') as rs ; destruct rs as (r',s'').
  cbn in * ; subst.
  symmetry in Heqrs, Heqrs0.
  destruct (ids_after_update_counters _ _ _ _ Heqrs0 Hin) as (e' & Hin' & Heq).
  rewrite <- Heq.
  eapply in_active_id_lt_N ; eauto.
Qed.

Lemma update_counters_effect_on_active : forall s s' r', 
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
*  rewrite snd_drop_snd in Hs.
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
     
End FunctionalEdfIsCorrectMod.

