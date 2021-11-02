Require Import List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Lia.
From Scheduler.Proof Require Import Lib Assumptions JobsAxioms EdfPolicy FunctionalEdf Hoare EdfPolicy Refinement.
From Scheduler.Model Require Import Monad PureFunctionModels.
From Scheduler.Model.Interface.Types Require Import TypesModel Jobs.
From Scheduler Require Import ElectionFunction.

Module MonadicEdfMod (J :JobsAxiomsMod).
Import J.

Module F:= FunctionalEdfImplementsAssumptionsMod J.
Import F. 

Module C := FunctionalEdfIsCorrectMod J.
Import C.

Module P := EdfPolicyMod J F.
Import P.

Module R := RefinementMod J.
Import R.

Module E := FunctionalEdfErrorHandlingMod J.
Import E.

Definition E :  Env := (fun k =>
                           (map (fun j =>
                                  mk_Job
                                    j
                                    (Jobs j).(arrival)
                                    (Jobs j).(duration)
                                    (Jobs j).(budget)
                                    (Jobs j).(deadline))          
                                (jobs_arriving_at k))).


Lemma scheduler_triple : forall s0,
{{
    fun env s => env =  E /\ s = s0 
}}
scheduler 
{{
    fun r s => (r,s) = functional_scheduler  s0

}}.
Proof.
intros  s0 env s (Henv & Hs).
rewrite Hs,Henv; clear Hs Henv.
case_eq (scheduler E s0) ; intros r s' Hs.
rewrite <- edf_refinement with (s0 := s0)  ; auto.
Qed.

Fixpoint scheduler_star (n : nat)  :=
  match n with
    0 => ret (None,false)
  | S m =>
    scheduler_star  m ;;
    do o <- scheduler  ;
    ret o
   end .

Lemma scheduler_star_S : forall n,
    scheduler_star (S n) =  scheduler_star n ;;
    do o <- scheduler  ;
    ret o.
Proof.
  reflexivity.
Qed.  



Lemma scheduler_star_triple : forall n,
{{
    fun env s => env = E /\ s = init
}}
scheduler_star n
{{
  fun o s => functional_scheduler_star n = (o,s)
}}.
Proof.
  intros  t env s (Henv & Hs) ; subst.
  case_eq (scheduler_star  t
      E init); intros o s Hs.
  rewrite <- Hs ; clear Hs o s.
  induction t ; auto.
  rewrite scheduler_star_S,  functional_scheduler_star_S.
  unfold bind, ret.
  case_eq ( functional_scheduler_star  t) ; intros o s Hfss.
  case_eq (scheduler_star  t
      E init); intros o' s' Hss.
  case_eq (scheduler 
       E s'); intros o'' s'' Hs.
  rewrite Hfss, Hss in IHt.
  injection IHt ; intros; subst.
  clear IHt Hfss Hss t.
  clear o'.
 
  specialize (scheduler_triple s' E s').
 unfold CNat in *.
  rewrite Hs.
  intuition.
Qed.
 

Theorem scheduler_correct : feasible ->
forall n, 
{{
      fun env s => env = E /\
      s = init
}}
scheduler_star  n
{{ 
fun _ s  => forall job_id, job_id < N -> ~overdue job_id (now s) 
}}.
Proof.
  intros Hf t.
  eapply strengthen.
  * apply scheduler_star_triple.
  *  cbn.
     intros a s Hfs i HiN.
     eapply functional_scheduler_correct; eauto.
Qed.


Theorem scheduler_error_handling :
  forall n, 
{{
      fun env s => env = E /\
      s = init
}}
scheduler_star  n
{{ 
fun o  s  => let (r,late) := o in forall job_id,  late = true -> r = Some job_id -> overdue job_id (now s -1)
}}.
Proof.
  intros t.
  eapply strengthen.
  * apply scheduler_star_triple.
  *  cbn.
     intros (r,b) s Hfs i Hb Hr.
     eapply functional_scheduler_star_overdue in Hfs; eauto.
Qed.

End MonadicEdfMod.
