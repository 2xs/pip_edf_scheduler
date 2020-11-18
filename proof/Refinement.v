Require Import List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Omega.
Require Import Lia.
From Scheduler.Proof Require Import Lib Assumptions JobsAxioms EdfPolicy FunctionalEdf Hoare EdfPolicy.
From Scheduler.Model Require Import Monad AbstractTypes AbstractFunctions.
From Scheduler.SchedulerMockup Require Import Jobs.
From Scheduler Require Import EDF.

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

Lemma functional_update_entries_refines_monadic :  forall r s0 s,
   update_entries E s0 = (r,s) ->  functional_update_entries s0 = (r,s).
Admitted.



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
