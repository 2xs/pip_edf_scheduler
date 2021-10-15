Require Import List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Omega.
Require Import Lia.
Require Import FunctionalExtensionality.
From Scheduler.Proof Require Import Lib Assumptions JobsAxioms EdfPolicy FunctionalEdf Hoare EdfPolicy.
From Scheduler.Model Require Import Monad  PureFunctionModels.
From Scheduler.Model.Interface Require Import Oracles.
From Scheduler.Model.Interface.Types Require Import TypesModel Jobs Entry JobSet CNat CBool CRet State.
From Scheduler Require Import ElectionFunction.


Module FunctionalEdfWithFuelMod(J : JobsAxiomsMod).
Import J.

Module F:= FunctionalEdfImplementsAssumptionsMod J.
Import F.

Module S :=  FunctionalEdfIsCorrectMod J.
Import S.

Fixpoint functional_insert_new_entries_fuel(timeout : nat) (new_jobs : list nat)(active : list Entry) : list Entry :=
  match timeout with
    0 => active
  | S timeout1  =>
    match new_jobs with
      [] => active
    |  new_job_id :: remaining_jobs =>
      let new_entry :=  mk_Entry
            new_job_id
            (budget (Jobs new_job_id))
            ((deadline (Jobs new_job_id) - (arrival (Jobs new_job_id)))) in
      let active1 := insert _
         (fun e1 e2 : Entry =>
            deadline (Jobs (id e1)) <=? deadline (Jobs (id e2)))
         new_entry active in
      functional_insert_new_entries_fuel timeout1 remaining_jobs active1
    end
  end.

Lemma functional_insert_new_entries_enough_fuel :
  forall  l n  l' ,
    length l <= n ->
    functional_insert_new_entries_fuel n  l l'  =
    insert_all _
               (fun e1 e2 : Entry =>
                                         deadline (Jobs (id e1)) <=? deadline (Jobs (id e2)))
            (map
             (fun j  =>
             {|
             id :=  j;
             cnt := budget (Jobs j);
             del := (deadline (Jobs j) - (arrival (Jobs j))) |}) l)
            l'.
Proof.
induction l ; intros n l' Hlen.
*   cbn.
    destruct n ; auto.
*  cbn.
   cbn in Hlen.
   destruct n ; try lia.
   rewrite <- IHl with ( n:= n) ; auto ; try lia.
Qed.

Definition functional_update_entries_fuel(s:State) : ((option nat *bool)* State) :=
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
       functional_insert_new_entries_fuel N  l  active1  in

( match active2 with
     | [] => (None,false)
     | e :: _ => (Some (id e), del e =? 0)
  end,  mk_State  s.(now) active2).


Lemma  functional_update_entries_enough_fuel : forall s, 
  functional_update_entries s = functional_update_entries_fuel s.
Proof.
intros s.
unfold functional_update_entries, functional_update_entries_fuel.
rewrite functional_insert_new_entries_enough_fuel; auto.
apply pigeon_hole.
*  apply NoDup_filter.
   rewrite NoDup_nth.
   intros i j Hi Hj Heq.
   destruct (jobs_arriving_at_unique _ _ _ _ Hi Hj Heq); auto.
* intros i Hin.
  rewrite filter_In in Hin.
  destruct Hin as (_ & Hlt).
  rewrite NPeano.Nat.ltb_lt in Hlt ; auto.
Qed.


Definition functional_scheduler_fuel  (s: State)  :=
  let (r,s')  := functional_update_entries_fuel  s in
  let (_,s'') := functional_update_counters  s' in
  (r,s'').                

Lemma functional_scheduler_enough_fuel  : forall s,
    functional_scheduler_fuel s = functional_scheduler s.
Proof.
intros s.
unfold functional_scheduler, functional_scheduler_fuel.
rewrite functional_update_entries_enough_fuel ; auto.
Qed.

Fixpoint functional_scheduler_star_fuel (t: nat):=
  match t with
    0 => ((None,false),init)
  |S t' =>
   let (_,s') := functional_scheduler_star_fuel  t' in
   functional_scheduler_fuel  s'
  end.


Lemma functional_scheduler_star_fuel_S : forall  t,
    functional_scheduler_star_fuel (S t) =
     let (_,s') := functional_scheduler_star_fuel t in
     functional_scheduler_fuel s'.
Proof.
reflexivity.
Qed.

Lemma functional_scheduler_star_enough_fuel : forall t,
     functional_scheduler_star_fuel t =  functional_scheduler_star t.
Proof.
induction t ; auto.
rewrite functional_scheduler_star_S,functional_scheduler_star_fuel_S.
rewrite IHt.
remember (functional_scheduler_star t) as rs ; destruct rs as (r,s).
unfold functional_scheduler_fuel, Alg.functional_scheduler.
rewrite functional_update_entries_enough_fuel ; auto.
Qed.

End FunctionalEdfWithFuelMod.

Module RefinementMod (J :JobsAxiomsMod).
 Import J.
  
Module F:= FunctionalEdfImplementsAssumptionsMod J.
Import F. 

Module FF := FunctionalEdfWithFuelMod J.
Import FF.

Definition E :  Env := (fun k =>
                           (map (fun j =>
                                  mk_Job
                                    j
                                    (Jobs j).(arrival)
                                    (Jobs j).(duration)
                                    (Jobs j).(budget)
                                    (Jobs j).(deadline))          
                                (jobs_arriving_at k))).
(* decomposing the update_entry function in 3 smaller units *)


Definition read_inputs  :=
  do new_jobs <- jobs_arriving N ; (* get all jobs arriving at current time, having id < N *)
  do finished <- job_terminating;  (* does a job finish at current time ? *)
  do expired <- job_expired;       (* is the job expired ? *)
  ret (new_jobs, finished,expired).

Lemma read_inputs_redundancy : forall s l b b' s',  read_inputs E s = ((l,b,b'), s') -> b || b' = b.
Proof.
intros s l b b' s' Hri.
unfold read_inputs,jobs_arriving,job_terminating,job_expired,get_first_active_entry,get_entry_counter,is_active_list_empty, bind,ret  in Hri.
remember (active s) as acs.
destruct acs.
* injection Hri ; intros ; subst; auto.
*rewrite <- Heqacs in Hri.
  cbn in Hri.  
  injection Hri ; intros ; subst.
  remember ( (cnt e =? zero) ) as b'.
  destruct b' ; symmetry in Heqb'.
  +
    apply beq_nat_true in Heqb'.
    rewrite Heqb'.
    assert (Hle : zero <= budget (Jobs (id e)) - duration (Jobs (id e))) ; unfold zero ; try lia.
    apply leb_correct in Hle.
    unfold zero in Hle.
    rewrite Hle; auto.
  +
    apply orb_false_r.
Qed.

    
  Definition update_first_entry (finished expired : CBool) :=
  do finished_or_expired <- or finished expired ;
  (if finished_or_expired then (* i remove its entry (NB the first one) from active list*)
    remove_first_active_entry
  else
    ret tt).



Definition write_output :=
  do no_active_entry <- is_active_list_empty;
  do late <- job_late ;            (* did the current job exceed its deadline ?*)
  (if no_active_entry then
    do ret_value <- make_ret_type false late default_nat ;
    ret ret_value
  else
    do running_entry_id <- get_running ; (* obtain id of the running job from head of active list *)
    do ret_value <- make_ret_type true late running_entry_id ;
    ret ret_value
  ).


Definition decomposed_update_entries :=
  do tuple <- read_inputs;
  match tuple with (new_jobs, finished,expired) =>
    update_first_entry finished expired ;;
    insert_new_entries new_jobs ;;
    write_output
  end.
 

Lemma decomposition_correct :
     update_entries = decomposed_update_entries .
Proof.
 unfold decomposed_update_entries, update_entries, read_inputs, update_first_entry, insert_new_entries, write_output in *.
 rewrite bind_bind.
 f_equal.
 extensionality new_jobs.
 rewrite bind_bind.
 f_equal.
 extensionality finished.
 rewrite bind_bind.
 f_equal.
Qed.

Definition functional_read_inputs (s : State) :=
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
( (l,b,b'), s).

Definition functional_update_first_entry (s : State) (b b' : bool) :=
  let active1 := if b then tl s.(active) else s.(active) in
  (tt,mk_State s.(now) active1).

Definition functional_add_new_entries_fuel(s:State) (l : list nat) :=
 let active2 :=
       functional_insert_new_entries_fuel  N l s.(active) in
 (tt,mk_State s.(now) active2).





Definition functional_write_output (s : State) :=
   (match s.(active) with
     | [] => (None, false)
     | e :: _ => (Some (id e), del e =? 0)
  end,  mk_State  s.(now) s.(active)).

Definition functional_decomposed_update_entries(s : State) :=
  let (tuple,s') :=  functional_read_inputs s in
  match tuple with (l, b,b') =>
    let (_,s'') := functional_update_first_entry  s' b  b' in
    let (_,s''') := functional_add_new_entries_fuel s'' l in
    functional_write_output s'''
  end.


Lemma functional_decomposition_correct :
     functional_update_entries_fuel = functional_decomposed_update_entries .
Proof.
  auto.
Qed.



Lemma read_inputs_refinement :  forall r s0 s,
    read_inputs E s0 = (r,s) ->  functional_read_inputs s0 = (r,s).
Proof.
intros r s0 s Hr.
unfold read_inputs, bind,ret in Hr.
unfold functional_read_inputs.
remember (jobs_arriving N E s0) as rs ; destruct rs as (l,s').
remember (job_terminating E s') as rs ; destruct rs as (b,s'').
remember (job_expired E s'') as rs ; destruct rs as (b',s''').
remember (job_late E s''') as rs ; destruct rs as (b'',s'''').
rewrite <- Hr ; clear r Hr.
unfold jobs_arriving , E, CNat in Heqrs.
rewrite map_map in Heqrs.
rewrite map_id in Heqrs.
injection Heqrs ; intros ; subst; clear Heqrs.
unfold job_terminating in Heqrs0.
injection Heqrs0 ; intros ; subst; clear Heqrs0.
unfold job_expired in Heqrs1.
unfold is_active_list_empty, get_first_active_entry, get_entry_counter,bind,ret in Heqrs1.
remember (active s0) as as0.
unfold job_late in Heqrs2.
  unfold is_active_list_empty, get_first_active_entry, get_entry_delete,eqb,bind,ret in *.
repeat f_equal ; auto.

*    destruct as0.
   +
    injection Heqrs1 ; intros ; auto.
   + cbn in *.
      rewrite <- Heqas0 in Heqrs1.
      injection Heqrs1; intros ; subst ; auto.
* 
   destruct as0.
   + injection Heqrs1 ; intros ; subst.
     cbn in *.
     rewrite <- Heqas0 in Heqrs2.
     injection Heqrs2 ; intros ; subst; auto.   
   +  
     cbn in *.
      rewrite <- Heqas0 in *.     
      injection Heqrs1; intros ; subst.
      repeat rewrite <- Heqas0 in *.
      cbn in *.
      injection Heqrs2; intros ; subst; auto.
Qed.



Lemma update_first_entry_refinement :  forall b b' r s0 s,
    b || b' = b  -> update_first_entry b b' E s0 = (r,s) ->
    functional_update_first_entry s0 b b'  = (r,s).
Proof.  
intros b b'  r s0 s Hbb' Hu.
unfold update_first_entry,  or, bind, ret in Hu.  
unfold functional_update_first_entry.
rewrite Hbb' in Hu.
destruct r.
f_equal ; auto.
unfold or, remove_first_active_entry, bind, ret in Hu.
case_eq b; intros Hcas ; rewrite Hcas in *  ; injection Hu ; intros ; subst ; auto.
destruct s ; auto.
Qed.


Lemma insert_new_entries_now :   forall l r s0 s,
    insert_new_entries_aux N  l  E s0 = (r,s) -> now s0 = now s.
Proof.
  induction N ; intros l r s0 s Hins.  
  * cbn in Hins.
    injection Hins ; intros  ; subst ; auto.
  *  cbn in Hins.
     destruct l.
  +
    injection Hins ; intros ; subst; auto.
  + 
     unfold get_first_job_id,  get_remaining_jobs, create_entry_from_job_id, get_job_from_job_id,
    get_budget, get_deadline, get_arrival, make_entry, sub, succ,
    cmp_entry_deadline,insert_new_active_entry,ret,bind in Hins.
    cbn [tl] in Hins.    
    remember  {|
           now := now s0;
           active := insert_Entry_aux
                       {|
                       id := c1;
                       cnt := budget (Jobs c1);
                       del := 
                                (deadline (Jobs c1) -
                                 arrival (Jobs c1)) |}
                       (active s0)
                       (fun entry1 entry2 : Entry =>
                        deadline (Jobs (id entry1)) <=?
                        deadline (Jobs (id entry2))) |} as s1.
    rewrite <-  (IHc0  _ _ _ _  Hins), Heqs1 ; auto.    
Qed.

Lemma insert_entry_active : forall e l,
   insert_Entry_aux
    e
    l
    (fun entry1 entry2 : Entry =>
     deadline (Jobs (id entry1)) <=? deadline (Jobs (id entry2))) =
  insert Entry
    (fun e1 e2 : Entry =>
     deadline (Jobs (id e1)) <=? deadline (Jobs (id e2)))
    e
    l.
Proof.
induction l ; auto.
cbn.
case (deadline (Jobs (id e)) <=? deadline (Jobs (id a))) ; auto.
rewrite IHl ; auto.
Qed.

Lemma insert_new_entries_active :   forall l r s0 s,
    insert_new_entries_aux N  l E s0 = (r,s) ->
    active s = functional_insert_new_entries_fuel N l
    (active s0).
Proof.
  induction N; intros l r s0 s Hins.
* cbn in *.
  injection Hins ; intros ; subst;auto.
* cbn in Hins.
  destruct l.
  +  
        injection Hins ; intros ; subst ; auto.
  +
    
    unfold get_first_job_id,  get_remaining_jobs, create_entry_from_job_id, get_job_from_job_id,
    get_budget, get_deadline, get_arrival, make_entry, sub, succ,
    cmp_entry_deadline,insert_new_active_entry,ret,bind in Hins.
    cbn [tl] in Hins.
    remember  {|
           now := now s0;
           active := insert_Entry_aux
                       {|
                       id := c1;
                       cnt := budget (Jobs c1);
                       del := 
                                (deadline (Jobs c1) -
                                 arrival (Jobs c1)) |}
                       (active s0)
                       (fun entry1 entry2 : Entry =>
                        deadline (Jobs (id entry1)) <=?
                        deadline (Jobs (id entry2))) |} as s1.
    rewrite (IHc0  _ _ _ _  Hins).
    cbn.
    f_equal ; auto.
    rewrite Heqs1.
    cbn.
    apply insert_entry_active.
Qed.
    
Lemma add_new_entries_refinement :  forall l r s0 s,
    insert_new_entries l E s0 = (r,s) ->
    functional_add_new_entries_fuel s0 l  = (r,s).
Proof.
intros l r s0 s Ha.
destruct r.  
unfold functional_add_new_entries_fuel.
f_equal.
unfold insert_new_entries,
bind,ret in Ha.
replace s with {| now := s.(now) ; active := s.(active) |} ; [ | destruct s ; auto].
f_equal.
* eapply insert_new_entries_now; eauto.
* symmetry.
  erewrite insert_new_entries_active ; eauto.
Qed.


Lemma write_output_refinement :  forall r s0 s,
    write_output E s0 = (r,s) ->
    functional_write_output s0   = (r,s).
Proof.
intros  r s0 s Hw.
unfold functional_write_output.  
unfold write_output, is_active_list_empty,make_ret_type,get_running ,get_first_active_entry, job_late, is_active_list_empty, get_first_active_entry, eqb,get_entry_delete,get_entry_id,bind,ret  in Hw.
remember (active s0) as as0.
destruct as0.

* rewrite <- Heqas0 in Hw.
  injection Hw ; intros ; subst.
  repeat (apply f_equal).
  destruct s ; f_equal ; auto.
*   
  repeat rewrite <- Heqas0 in Hw.
  cbn in Hw.
  repeat rewrite <- Heqas0 in Hw.
   injection Hw ; intros ; subst.
  repeat (apply f_equal).
  destruct s ; f_equal ; auto.
Qed.

Lemma update_entries_refinement :  forall r s0 s,
   update_entries E s0 = (r,s) ->  functional_update_entries_fuel s0 = (r,s).
Proof.
intros r s0 s Hu.  
rewrite decomposition_correct in Hu.
rewrite functional_decomposition_correct.
unfold  decomposed_update_entries, bind, ret in Hu.
unfold functional_decomposed_update_entries.
rewrite <- Hu.
clear Hu r s. 
remember (functional_read_inputs s0) as fri.
destruct fri as (r,s).
remember (read_inputs E s0) as ri.
destruct ri as (r',s').
symmetry in Heqri.
generalize Heqri  ; intro Heqri_cp.
rewrite <- read_inputs_refinement with (s0 := s0) in Heqri ; auto.
assert (Heq  : (r,s) = (r',s') ) ; [congruence | ].
injection Heq ; intros ; subst.
clear  Heq Heqri Heqfri.
destruct r' as ((l & b) & b').
apply read_inputs_redundancy in Heqri_cp.
rename Heqri_cp into Hbb'.
remember (functional_update_first_entry s' b b') as fri.
destruct fri as (r,s).
remember (update_first_entry b b' E s') as ri.
destruct ri as (r'',s'').
symmetry in Heqri.
generalize Heqri  ; intro Heqri_cp.
erewrite <- update_first_entry_refinement with (s0 := s') in Heqri ; eauto.
assert (Heq  : (r,s) = (r'',s'') ) ; [congruence | ].
injection Heq ; intros ; subst.
clear s' Heq Heqri Heqri_cp Heqfri r''.

remember (functional_add_new_entries_fuel s'' l) as fri.
destruct fri as (r,s).
remember (insert_new_entries l E s'') as ri.
destruct ri as (r',s').
symmetry in Heqri.
generalize Heqri  ; intro Heqri_cp.
erewrite <- add_new_entries_refinement with (s0 := s'') in Heqri ; eauto.
assert (Heq  : (r,s) = (r',s') ) ; [congruence | ].
injection Heq ; intros ; subst.
remember (write_output E s') as ri.
destruct ri as (r'',s''').
erewrite write_output_refinement; eauto.
Qed.


Lemma update_counters_refinement :  forall r s0 s,
   update_counters E s0 = (r,s) ->  functional_update_counters s0 = (r,s).
Proof.
unfold update_counters, functional_update_counters.
intros r  s0 s Hs.
destruct r.
f_equal.
unfold bind in Hs.
cbn in Hs.
unfold State.set_time_counter in Hs.
injection Hs ; intros ; subst.
f_equal.
unfold Entry.decrease_del, decrease_all_del_func, decrease_cnt.
f_equal.
clear Hs.
remember (active s0) as as0.
destruct as0; auto.
Qed.


Lemma edf_refinement_fuel :  forall r s0 s,
   scheduler E s0 = (r,s) ->  functional_scheduler_fuel s0 = (r,s).
Proof.
unfold scheduler, functional_scheduler_fuel.  
intros r s0 s Hs.
remember (functional_update_entries_fuel s0) as fe.
destruct fe as (r0,s').
remember  (F.functional_update_counters s') as fc.
destruct fc.
unfold bind, ret in Hs.
remember (update_entries E s0) as as'.
destruct as' as (a',s'').
remember (update_counters E s'') as as'.
destruct as'.
injection Hs ; intros ; subst ; clear Hs.
rewrite update_entries_refinement
  with (r := r) (s := s'')in Heqfe ; [ | rewrite Heqas'; reflexivity].
injection Heqfe ; intros ; subst. 
rewrite  update_counters_refinement
  with (r := u0)(s := s) in Heqfc ; [ | rewrite Heqas'0; reflexivity].
injection Heqfc; intros; subst.
reflexivity.
Qed.


Lemma edf_refinement :  forall r s0 s,
   scheduler E s0 = (r,s) ->  functional_scheduler s0 = (r,s).
Proof.
 intros r s0 s Hs.
apply edf_refinement_fuel in Hs.  
rewrite <- functional_scheduler_enough_fuel ; auto. 
Qed.

End RefinementMod.
