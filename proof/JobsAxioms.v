(* This software is governed by the CeCILL license under French law and
 * abiding by the rules of distribution of free software.  You can  use,
 * modify and/ or redistribute the software under the terms of the CeCILL
 * license as circulated by CEA, CNRS and INRIA at the following URL
 * "http://www.cecill.info".

 * As a counterpart to the access to the source code and  rights to copy,
 * modify and redistribute granted by the license, users are provided only
 * with a limited warranty  and the software's author,  the holder of the
 * economic rights,  and the successive licensors  have only  limited
 * liability.

 * In this respect, the user's attention is drawn to the risks associated
 * with loading,  using,  modifying and/or developing or reproducing the
 * software by the user in light of its specific status of free software,
 * that may mean  that it is complicated to manipulate,  and  that  also
 * therefore means  that it is reserved for developers  and  experienced
 * professionals having in-depth computer knowledge. Users are therefore
 * encouraged to load and test the software's suitability as regards their
 * requirements in conditions enabling the security of their systems and/or
 * data to be ensured and,  more generally, to use and operate it in the
 * same conditions as regards security.

 * The fact that you are presently reading this means that you have had
 * knowledge of the CeCILL license and that you accept its terms.
 *)

(* /!\ Proof related content on Jobs are located in proof/JobsAxioms.v *)

From Scheduler.Model Require Import AbstractFunctions.
From Scheduler.Model Require Import AbstractTypes.
From Scheduler.SchedulerMockup Require Import Jobs.
Require Import List.
Module Type JobsMod.

  (* job_id -> job *)
  (*Parameter Jobs : nat -> Job.*)

  (* oracle from scheduling plan *)
  Parameter jobs_arriving_at :
    forall (t:nat), list nat.

  Axiom job_duration_gt_0 : forall n, duration (Jobs n) > 0.

  Axiom job_budget_enough : forall n, budget (Jobs n) >= duration (Jobs n).


  Axiom job_arrival_plus_duration_le_deadline :
    forall i,
      arrival (Jobs i) + duration (Jobs i) <= deadline (Jobs i).

  Axiom jobs_id_index : forall i,   jobid (Jobs i) = i.


  (* In should be defined for C lists ? TODO *)
 Axiom jobs_arriving_at_prop : forall  t i,
      In i (jobs_arriving_at t) <-> arrival (Jobs i) = t.

  (* nth should be defined for C lists ? TODO *)

  Axiom jobs_arriving_at_unique : forall i i' t t',
      i < length (jobs_arriving_at t) ->  i' < length (jobs_arriving_at t') ->
      nth i (jobs_arriving_at t) 0 = nth i' (jobs_arriving_at t') 0 ->
      (t = t' /\ i = i').

End JobsMod.
