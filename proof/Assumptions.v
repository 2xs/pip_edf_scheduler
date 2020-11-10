Require Import List.
Import ListNotations.
Require Import Omega.
Require Import Lia.
From Scheduler.Proof Require Import Lib.
From Scheduler.SchedulerMockup Require Import Jobs.

From Scheduler.Model Require Import AbstractFunctions.
From Scheduler.Model Require Import AbstractTypes.
From Scheduler.Proof Require Import JobsAxioms.

        

Module  Type AssumptionsMod (J : JobsMod).
  Import J.
  
  Parameter c : nat -> nat -> nat -> nat.
  Parameter run : nat -> nat -> nat -> bool.


  Axiom at_most_one_runs: forall (N i j t : nat),
      i < N -> j < N ->
      run N i t  = true -> run N j t = true -> i = j.

    Axiom c_is_duration_upto_arrival : forall (N i t : nat), i < N ->
      t <= arrival (Jobs i) -> c N  i t = duration (Jobs i). 

  
  Axiom c_decreases_when_running : forall (N i t : nat), i < N ->
      run N i t  = true -> (c N i t  > 0 /\
                        c N i (S t)  = c N i t - 1).

  Axiom c_constant_when_not_running : forall (N i t : nat), i < N ->
      run N i t  = false -> c N i (S t) = c N i t.

 
  
  Definition sum_counters_arrived(N t : nat) :=
    generic_sum
      (fun i  => c N i t)
        (fun i  => arrival(Jobs i) <=? t)
        0 N.

  Axiom sum_arrived_some_running : forall N t,
      sum_counters_arrived N t > 0 -> exists j, j < N /\ run N j t = true.

End AssumptionsMod.

