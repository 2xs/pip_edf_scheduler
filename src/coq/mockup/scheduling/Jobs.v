(* type for a job  *)
Record Job  :=
  mk_Job
    {
      jobid : nat ;
      arrival : nat ;
      duration : nat ;
      budget : nat ;
      deadline : nat
    }.

Definition def_Job : Job := mk_Job 0 0 0 0 0.

Module Type JobsMod.

  Parameter Jobs : nat -> Job.

  Axiom job_duration_gt_0 : forall n, duration (Jobs n) > 0.

  Axiom job_budget_enough : forall n, budget (Jobs n) >= duration (Jobs n).


  Axiom job_arrival_plus_duration_le_deadline :
    forall i,
      arrival (Jobs i) + duration (Jobs i) <= deadline (Jobs i).

  Axiom jobs_id_index : forall i,   jobid (Jobs i) = i.

  Parameter jobs_arriving_at :
    forall (t:nat), list nat.

  (* In should be defined for C lists ? TODO *)
(*  Axiom jobs_arriving_at_prop : forall  t i,
      In i (jobs_arriving_at t) <-> arrival (Jobs i) = t.*)

  (* nth should be defined for C lists ? TODO *)
(*
  Axiom jobs_arriving_at_unique : forall i i' t t',
      i < length (jobs_arriving_at t) ->  i' < length (jobs_arriving_at t') ->
      nth i (jobs_arriving_at t) 0 = nth i' (jobs_arriving_at t') 0 ->
      (t = t' /\ i = i').
*)

End JobsMod.