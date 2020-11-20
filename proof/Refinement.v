Require Import List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Omega.
Require Import Lia.
Require Import FunctionalExtensionality.
From Scheduler.Proof Require Import Lib Assumptions JobsAxioms EdfPolicy FunctionalEdf Hoare EdfPolicy.
From Scheduler.Model Require Import Monad AbstractTypes AbstractFunctions.
From Scheduler.SchedulerMockup Require Import Jobs Entry JobSet CNat CBool CRet State.
From Scheduler.PartitionMockup Require  Import Primitives.
From Scheduler Require  Import EDF.


Module RefinementMod (J :JobsAxiomsMod).
 Import J.
  
Module F:= FunctionalEdfImplementsAssumptionsMod J.
Import F. 


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
  do late <- job_late ;            (* did the job exceed its deadline ?*)
  ret (new_jobs, finished,expired,late).

Definition update_first_entry (finished expired : CBool) :=
  do not_expired <- not expired;
  do finished_and_not_expired <- and finished not_expired ;
  (if finished_and_not_expired then (* i remove its entry (NB the first one) from active list*)
    remove_first_active_entry
  else
    ret tt).

Definition add_new_entries (new_jobs : JobSet) :=  
  do new_jobs_length <- get_length new_jobs ;
  insert_new_entries new_jobs new_jobs_length.

Definition write_output (late : CBool) :=
  do running_entry_id <- get_running ; (* obtain id of the running job (possibly none) from head of active list*)
  do no_running_entry <- is_default_nat running_entry_id ;
  do ret_value <- make_ret_type no_running_entry late running_entry_id ;
  ret ret_value.


Definition decomposed_update_entries :=
  do tuple <- read_inputs;
  match tuple with (new_jobs, finished,expired,late) =>
    update_first_entry finished expired ;;
    add_new_entries new_jobs ;;
    write_output late
  end.
 

Lemma decomposition_correct :
     update_entries = decomposed_update_entries .
Proof.
 unfold decomposed_update_entries, update_entries, read_inputs, update_first_entry, add_new_entries, write_output in *.
 rewrite bind_bind.
 f_equal.
 extensionality new_jobs.
 rewrite bind_bind.
 f_equal.
 extensionality finished.
 rewrite bind_bind.
 f_equal.
 extensionality expired.
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
let b'' :=  match hd_error s.(active) with
     | Some e =>
         del e =? 0
     | None => false
           end
in
( (l,b,b',b''), s).

Definition functional_update_first_entry (s : State) (b b' : bool) :=
  let active1 := if b && (negb b') then tl s.(active) else s.(active) in
  (tt,mk_State s.(now) active1).

Definition functional_add_new_entries(s:State) (l : list nat) :=
 let active2 :=
       insert_all _
         (fun e1 e2 : Entry =>
          deadline (Jobs (id e1)) <=? deadline (Jobs (id e2)))
         (map
            (fun j  =>
             {|
             id :=  j;
             cnt := budget (Jobs j);
             del := S (deadline (Jobs j) - (arrival (Jobs j))) |}) l) s.(active) in
 (tt,mk_State s.(now) active2).


Definition functional_write_output (s : State) (b'' : bool) :=
   (match s.(active) with
     | [] => (None,b'')
     | e :: _ => (Some (id e), b'')
  end,  mk_State  s.(now) s.(active)).

Definition functional_decomposed_update_entries(s : State) :=
  let (tuple,s') :=  functional_read_inputs s in
  match tuple with (l, b,b',b'') =>
    let (_,s'') := functional_update_first_entry  s' b b' in
    let (_,s''') := functional_add_new_entries s'' l in
    functional_write_output s''' b'' 
  end.


Lemma functional_decomposition_correct :
     functional_update_entries = functional_decomposed_update_entries .
Proof.
  auto.
Qed.



Lemma functional_read_inputs_refines_monadic :  forall r s0 s,
   read_inputs E s0 = (r,s) ->  functional_read_inputs s0 = (r,s).
Admitted.


Lemma functional_update_first_entry_refines_monadic :  forall b b' r s0 s,
    update_first_entry b b' E s0 = (r,s) ->
    functional_update_first_entry s0 b b'  = (r,s).
Admitted.


Lemma functional_add_new_entries_refines_monadic :  forall l r s0 s,
    add_new_entries l E s0 = (r,s) ->
    functional_add_new_entries s0 l  = (r,s).
Admitted.


Lemma functional_write_output_refines_monadic :  forall b'' r s0 s,
    write_output b'' E s0 = (r,s) ->
    functional_write_output s0 b''  = (r,s).
Admitted.


Lemma functional_update_entries_refines_monadic :  forall r s0 s,
   update_entries E s0 = (r,s) ->  functional_update_entries s0 = (r,s).
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
rewrite <- functional_read_inputs_refines_monadic with (s0 := s0) in Heqri ; auto.
assert (Heq  : (r,s) = (r',s') ) ; [congruence | ].
injection Heq ; intros ; subst.
clear s0 Heq Heqri Heqri_cp Heqfri.
destruct r' as (((l & b) & b') & b'').
remember (functional_update_first_entry s' b b') as fri.
destruct fri as (r,s).
remember (update_first_entry b b' E s') as ri.
destruct ri as (r'',s'').
symmetry in Heqri.
generalize Heqri  ; intro Heqri_cp.
erewrite <- functional_update_first_entry_refines_monadic with (s0 := s') in Heqri ; eauto.
assert (Heq  : (r,s) = (r'',s'') ) ; [congruence | ].
injection Heq ; intros ; subst.
clear s' Heq Heqri Heqri_cp Heqfri r''.

remember (functional_add_new_entries s'' l) as fri.
destruct fri as (r,s).
remember (add_new_entries l E s'') as ri.
destruct ri as (r',s').
symmetry in Heqri.
generalize Heqri  ; intro Heqri_cp.
erewrite <- functional_add_new_entries_refines_monadic with (s0 := s'') in Heqri ; eauto.
assert (Heq  : (r,s) = (r',s') ) ; [congruence | ].
injection Heq ; intros ; subst.
clear  Heq Heqri Heqri_cp Heqfri r' s'' b b' l.


remember (write_output b'' E s') as ri.
destruct ri as (r'',s'').
erewrite functional_write_output_refines_monadic; eauto.
Qed.


Lemma functional_update_counters_refines_monadic :  forall r s0 s,
   update_counters E s0 = (r,s) ->  functional_update_counters s0 = (r,s).
Proof.
unfold update_counters, functional_update_counters.
intros r  s0 s Hs.
destruct r.
f_equal.
unfold bind in Hs.
cbn in Hs.
remember (remove_first_if_expired E  {|
            now := now s0;
            active := match hd_error (active s0) with
                      | Some entry =>
                          Entry.decrease_cnt entry
                          :: tl (active s0)
                      | None => []
                      end |}) as _s'.
destruct _s' as (u,s').
unfold State.set_time_counter in Hs.
injection Hs ; intros ; subst.
f_equal.
2 : {
  unfold Entry.decrease_del, decrease_all_del_func.
  f_equal.
  clear Hs.
  remember (active s0) as as0.
  destruct as0.
  2 : {
    cbn in *.
    unfold CNat.zero in *.
    case_eq (Init.Nat.pred (cnt e) =? 0); intro Hcas; rewrite Hcas in *.
    * unfold State.remove_first_active_entry in *.
      injection Heq_s' ; intros ; subst.
      auto.
    *  unfold ret in *.
       injection Heq_s' ; intros ; subst.
      auto.
  }
  cbn in *.
  unfold CNat.zero in *.
  case_eq ( (cnt Entry.default_entry) =? 0); intro Hcas; rewrite Hcas in *.
  2 :{
    unfold ret in *.
    injection Heq_s' ; intros; subst.
    auto.
  }
  unfold State.remove_first_active_entry in *.
  injection Heq_s' ; intros ; subst.
  auto.
}
f_equal.
unfold State.remove_first_active_entry, remove_first_if_expired in *.
unfold bind, ret in *.
unfold State.get_first_active_entry in *.
cbn in *.
 remember (active s0) as as0.
 destruct as0.
* cbn in *.
  clear Hs.
   unfold CNat.zero in *.
  case_eq ( (cnt Entry.default_entry) =? 0); intro Hcas; rewrite Hcas in *.
  2 :{
    unfold ret in *.
    injection Heq_s' ; intros; subst.
    auto.
  }
  unfold State.remove_first_active_entry in *.
  injection Heq_s' ; intros ; subst.
  auto.
* cbn in *.
  clear Hs.
   unfold CNat.zero in *.
  case_eq ( Init.Nat.pred (cnt e) =? 0); intro Hcas; rewrite Hcas in *.
  2 :{
    injection Heq_s' ; intros; subst.
    auto.
  }
  unfold State.remove_first_active_entry in *.
  injection Heq_s' ; intros ; subst.
  auto.
Qed.


Lemma functional_edf_refines_monadic :  forall r s0 s,
   scheduler E s0 = (r,s) ->  functional_scheduler s0 = (r,s).
Proof.
unfold scheduler, functional_scheduler.  
intros r s0 s Hs.
remember (functional_update_entries s0) as fe.
destruct fe as (r0,s').
remember  (functional_update_counters s') as fc.
destruct fc.
unfold bind, ret in Hs.
remember (update_entries E s0) as as'.
destruct as' as (a',s'').
remember (update_counters E s'') as as'.
destruct as'.
injection Hs ; intros ; subst ; clear Hs.
rewrite functional_update_entries_refines_monadic
  with (r := r) (s := s'')in Heqfe ; [ | rewrite Heqas'; reflexivity].
injection Heqfe ; intros ; subst. 
rewrite  functional_update_counters_refines_monadic
  with (r := u0)(s := s) in Heqfc ; [ | rewrite Heqas'0; reflexivity].
injection Heqfc; intros; subst.
reflexivity.
Qed.

End RefinementMod.
