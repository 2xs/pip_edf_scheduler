Require Import List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Omega.
Require Import Lia.
From Scheduler.Proof Require Import Lib Assumptions JobsAxioms EdfPolicy FunctionalEdf Hoare EdfPolicy.
From Scheduler.Model Require Import Monad AbstractTypes AbstractFunctions.
From Scheduler.SchedulerMockup Require Import Jobs.
From Scheduler Require Import EDF.

Module EdfRefinesFunctionalEdfMod (J :JobsAxiomsMod).
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


Lemma edf_refines_functional_edf :  forall r s0 s,
   scheduler E s0 = (r,s) ->  functional_scheduler s0 = (r,s).
Admitted.

End EdfRefinesFunctionalEdfMod.
