Require Import List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Omega.
Require Import Lia.
From Scheduler.Proof Require Import Lib Assumptions JobsAxioms EdfPolicy FunctionalEdf Hoare EdfPolicy Refinement.
From Scheduler.Model Require Import Monad AbstractTypes AbstractFunctions.
From Scheduler.SchedulerMockup Require Import Jobs.
From Scheduler Require Import EDF.

Module MonadicEdfMod (J :JobsAxiomsMod).
 Import J.
  
Module F:= FunctionalEdfImplementsAssumptionsMod J.
Import F. 

Module P := EdfPolicyMod J F.
Import P.

Module R := RefinementMod J.
Import R.
Definition E :  Env := (fun k =>
                           (map (fun j =>
                                  mk_Job
                                    j
                                    (Jobs j).(arrival)
                                    (Jobs j).(duration)
                                    (Jobs j).(budget)
                                    (Jobs j).(deadline))          
                                (jobs_arriving_at k))).


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

(*Lemma edf_refines_functional_edf :  forall r s0 s,
   scheduler E s0 = (r,s) ->  functional_scheduler s0 = (r,s).
Admitted.
*)

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
rewrite <- functional_edf_refines_monadic with (s0 := s0)  ; auto.
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
    fun env s => env = (fun k =>
                           (map (fun j =>
                                  mk_Job
                                    j
                                    (Jobs j).(arrival)
                                    (Jobs j).(duration)
                                    (Jobs j).(budget)
                                    (Jobs j).(deadline))          
                                (jobs_arriving_at k))) /\
      s = init
}}
scheduler_star n
{{
  fun o s => functional_scheduler_star n = (o,s)
}}.
Proof.
  intros  t env s (Henv & Hs) ; subst.
  case_eq (scheduler_star  t
      (fun k : CNat =>
       map
         (fun j : CNat =>
          {|
          jobid := j;
          arrival := arrival (Jobs j);
          duration := duration (Jobs j);
          budget := budget (Jobs j);
          deadline := deadline (Jobs j) |}) 
         (jobs_arriving_at k)) init); intros o s Hs.
  rewrite <- Hs ; clear Hs o s.
  induction t ; auto.
  rewrite scheduler_star_S,  functional_scheduler_star_S.
  unfold bind, ret.
  case_eq ( functional_scheduler_star  t) ; intros o s Hfss.
  case_eq (scheduler_star  t
      (fun k : CNat =>
       map
         (fun j : CNat =>
          {|
          jobid := j;
          arrival := arrival (Jobs j);
          duration := duration (Jobs j);
          budget := budget (Jobs j);
          deadline := deadline (Jobs j) |}) 
         (jobs_arriving_at k)) init); intros o' s' Hss.
  case_eq (scheduler 
       (fun k : CNat =>
        map
          (fun j : CNat =>
           {|
           jobid := j;
           arrival := arrival (Jobs j);
           duration := duration (Jobs j);
           budget := budget (Jobs j);
           deadline := deadline (Jobs j) |}) 
          (jobs_arriving_at k)) s'); intros o'' s'' Hs.
  rewrite Hfss, Hss in IHt.
  injection IHt ; intros; subst.
  clear IHt Hfss Hss t.
  clear o'.
 
  specialize (scheduler_triple s'  (fun k : nat =>
          map
            (fun j :CNat =>
             {|
             jobid := j;
             arrival := arrival (Jobs j);
             duration := duration (Jobs j);
             budget := budget (Jobs j);
             deadline := deadline (Jobs j) |})
            (jobs_arriving_at k)) s').
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
fun _ s  => forall i, i < N -> ~overdue i (now s) 
}}.
Proof.
  intros Hf t.
  eapply strengthen.
  * apply scheduler_star_triple.
  *  cbn.
     intros a s Hfs i HiN.
     eapply functional_scheduler_correct; eauto.
Qed.

End MonadicEdfMod.
