From SchedulerMockup Require Import Jobs.

(** Data structures *)

(* type for an entry *)
Record Entry :=
  mk_Entry
    {
      id : nat ;
      cnt : nat ;
      del : nat
    }.

(* type for the state *)
Record State :=
  mk_State
    {
      now : nat ;
      active : list Entry 
    }.


(** Should we merge entry and jobs ? *)

(** We suppose a scheduling plan, where does it come from ? *)
Definition Env : Type := nat -> list Job.


