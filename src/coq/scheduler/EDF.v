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

From Scheduler.Model Require Import Monad.
From Scheduler.Model Require Import AbstractTypes.
From Scheduler.SchedulerMockup Require Import Jobs.
From Scheduler.SchedulerMockup Require Import Entry.
From Scheduler.SchedulerMockup Require Import JobSet.
From Scheduler.SchedulerMockup Require Import CNat.
From Scheduler.SchedulerMockup Require Import CBool.
From Scheduler.SchedulerMockup Require Import CRet.
From Scheduler.SchedulerMockup Require Import State.
From Scheduler.PartitionMockup Require Import Primitives.

(** Computations made during the election of the next Job to schedule *)

(** Helper functions *)

(* function that checks if the current job is expired *)
Definition job_expired : RT bool :=
  do no_active_entry <- is_active_list_empty ;
  if no_active_entry then
    ret false
  else
  do first_active_entry <- get_first_active_entry ;
  do first_active_entry_counter <- get_entry_counter first_active_entry ;
  CNat.eqb first_active_entry_counter zero.


(* function that checks if the current job is late *)
Definition job_late : RT bool :=
  do no_active_entry <- is_active_list_empty ;
  if no_active_entry then
    ret false
  else
  do first_active_entry <- get_first_active_entry ;
  do first_active_entry_delete <- get_entry_delete first_active_entry ;
  CNat.eqb first_active_entry_delete zero.


Definition create_entry_from_job_id (job_id : CNat) : RT Entry :=
  do job <- get_job_from_job_id job_id ;
  do job_budget <- get_budget job ;
  do job_deadline <- get_deadline job ;
  do job_arrival <- get_arrival job ;
  do diff_deadline_arrival <- sub job_deadline job_arrival ;
  make_entry job_id job_budget  diff_deadline_arrival.

(* primitive that inserts a list of entries according to its deadline *)
Fixpoint insert_new_entries_aux timeout (new_jobs : JobSet) : RT unit :=
  match timeout with
  | 0 => ret tt
  | S(timeout1) =>
      do no_more_jobs <- is_empty_list new_jobs;
      if no_more_jobs then
        ret tt
      else
      do new_job_id <- get_first_job_id new_jobs ;
      do new_entry <- create_entry_from_job_id new_job_id;
      insert_new_active_entry new_entry cmp_entry_deadline;;
      do remaining_jobs <- get_remaining_jobs new_jobs ;
      insert_new_entries_aux timeout1 remaining_jobs
  end.
 

Definition insert_new_entries (new_jobs : JobSet) : RT unit :=
  insert_new_entries_aux N new_jobs.

Definition get_running : RT CNat :=
  do first_active_entry <- get_first_active_entry ;
  get_entry_id first_active_entry.

(** Updates the list of Entries to schedule (new jobs given by a primitive) *)
Definition update_entries : RT CRet :=
  do new_jobs <- jobs_arriving N ; (* get all jobs arriving at current time, having id < N *)
  do finished <- job_terminating;  (* does a job finish at current time ? *)
  do expired <- job_expired;       (* is the job expired ? *)
  do not_expired <- not expired;
  do finished_and_not_expired <- and finished not_expired ;
  (if finished_and_not_expired then (* i remove its entry (NB the first one) from active list*)
    remove_first_active_entry
  else
    ret tt)
  ;;
  insert_new_entries new_jobs ;;
  do no_active_entry <- is_active_list_empty;
  do late <- job_late ;            (* did the current job exceed its deadline ?*)
  (if no_active_entry then
    do ret_value <- make_ret_type false late default_nat ;
    ret ret_value
  else
    do running_entry_id <- get_running ; (* obtain id of the running job from head of active list *)
    do ret_value <- make_ret_type true late running_entry_id ;
    ret ret_value
  ).
  (*  return the job id (if any) that has beed running, and whether or not the job was late   *)


Definition decrease_cnt_first : RT unit :=
  update_first_active_entry decrease_cnt.


(* primitive that removes the first entry if it exists and has expired *)
Definition remove_first_if_expired : RT unit :=
  do first_active_entry <- get_first_active_entry ;
  do first_active_entry_counter <- get_entry_counter first_active_entry ;
  do first_active_entry_is_expired <- CNat.eqb first_active_entry_counter zero ;
  if first_active_entry_is_expired then
    remove_first_active_entry
  else
    ret tt.

Definition decrease_all_del : RT unit :=
  update_active_entries decrease_del.

(* primitive that increases the time counter *)
Definition inc_time_counter : RT unit :=
  do time_counter <- get_time_counter ;
  do next_time_counter <- succ time_counter ;
  set_time_counter next_time_counter.

Definition update_counters : RT unit :=
  decrease_cnt_first;; (* decrease cnt field of first entry corresponding to the running job*)
  remove_first_if_expired;; (* if field became 0 the budget's job is 0 : remove it from actve list *)
  decrease_all_del ;;
  inc_time_counter.

(** Election function used by the partition *)
Definition scheduler : RT CRet :=
  do p <- update_entries ;
  update_counters ;;
  ret p.
