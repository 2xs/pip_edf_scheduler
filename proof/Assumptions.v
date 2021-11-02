Require Import List.
Import ListNotations.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.

From Scheduler.Model Require Import PureFunctionModels.
From Scheduler.Model.Interface.Types Require Import TypesModel Jobs.

From Scheduler.Proof Require Import Lib JobsAxioms.

Module  Type AssumptionsMod (J : JobsAxiomsMod).
  Import J.

  Parameter c : nat -> nat -> nat.
  Parameter run : nat -> nat -> bool.


  Axiom at_most_one_runs: forall (i j t : nat),
      i < N -> j < N ->
      run  i t  = true -> run  j t = true -> i = j.

  Axiom c_is_duration_upto_arrival : forall (i t : nat), i < N ->
      t <= arrival (Jobs i) -> c  i t = duration (Jobs i).


  Axiom c_decreases_when_running : forall ( i t : nat), i < N ->
      run  i t  = true -> (c i t  > 0 /\
                        c  i (S t)  = c i t - 1).

  Axiom c_constant_when_not_running : forall ( i t : nat), i < N ->
      run  i t  = false -> c  i (S t) = c  i t.

  Definition sum_counters_arrived( t : nat) :=
    generic_sum
      (fun i  => c  i t)
        (fun i  => arrival(Jobs i) <=? t)
        0 N.

  Axiom sum_arrived_some_running : forall  t,
      sum_counters_arrived t > 0 -> exists j, j < N /\ run  j t = true.

End AssumptionsMod.

