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

From Model Require Import Monad.
From Model Require Import AbstractTypes.
From SchedulerMockup Require Import Jobs.
From SchedulerMockup Require Import Entry.
From SchedulerMockup Require Import CNat.
From SchedulerMockup Require Import CBool.
From SchedulerMockup Require Import List.
From SchedulerMockup Require Import State.
From PartitionMockup Require Import Primitives.

(** Computations made during the election of the next Job to schedule *)

(** Helper functions *)

(* function that checks if the current job is expired *)
Definition job_expired : RT bool :=
  do active_entries <- get_active_entries ;
  do current_job_entry <- get_EntryList_head active_entries ;
  do no_current_job_entry <- is_default_entry current_job_entry ;
  if no_current_job_entry then
    ret false
  else
  do current_job_entry_counter <- get_entry_counter current_job_entry ;
  CNat.eqb current_job_entry_counter 0.
(*
  fun _ s => ((match head s.(active) with
         None => false
       | Some e =>
           Nat.eqb e.(cnt)  0
         end), s).*)

(* function that checks if the current job is late *)
Definition job_late : RT bool :=
  do active_entries <- get_active_entries ;
  do current_job_entry <- get_EntryList_head active_entries ;
  do no_current_job_entry <- is_default_entry current_job_entry ;
  if no_current_job_entry then
    ret false
  else
  do current_job_entry_delete <- get_entry_delete current_job_entry ;
  CNat.eqb current_job_entry_delete 0.
(*fun _ s => ((match head s.(active) with
         None => false
       | Some e =>
          Nat.eqb  e.(del)  0
         end), s).*)

Definition create_entry_from_job_id (job_id : nat) : RT Entry :=
  do job <- get_job_from_job_id job_id ;
  do job_budget <- get_budget job ;
  do job_deadline <- get_deadline job ;
  do job_arrival <- get_arrival job ;
  do diff_deadline_arrival <- sub job_deadline job_arrival ;
  do entry_del <- succ diff_deadline_arrival ;
  make_entry job_id job_budget entry_del.

(* primitive that inserts a list of entries according to its deadline *)
Definition insert_new_active_entries (new_active_entries : EntryList) : RT unit :=
  do former_active_entries <- get_active_entries ;
  (* insert_entries function destroys new_active_entries AND former_active_entries *)
  (* You should not use either of those variables afterwards *)
  do active_entries <- insert_Entries new_active_entries former_active_entries cmp_entry_deadline ;
  set_active_entries active_entries.
  (*
  fun _ s => (tt, {|
    now := s.(now);
    active := insert_all _ (fun e1 e2 =>
                            (Jobs(e1.(id))).(deadline) <=?
                            (Jobs(e2.(id))).(deadline))
                            l s.(active)
    |}).*)

Definition remove_first : RT unit :=
(*fun _ s =>  (tt, {| now := s.(now); active := tail s.(active) |}).*)
  do active_entries <- get_active_entries ;
  do removed_head_active_entries <- remove_EntryList_head active_entries ;
  set_active_entries removed_head_active_entries.

Definition get_running : RT nat :=
  do active_entries <- get_active_entries ;
  do running_entry <- get_EntryList_head active_entries ;
  get_entry_id running_entry.

(** Updates the list of Entries to schedule (new jobs given by a primitive) *)
Definition update_entries(N : nat) : RT ((option nat)* bool) :=
  do new_jobs <- jobs_arriving N ; (* get all jobs arriving at current time, having id < N *)
  do finished <- job_terminating;  (* does a job finish at current time ? *)
  do expired <- job_expired;       (* is the job expired ? *)
  do late <- job_late ;            (* did the job exceed its deadline ?*)
  do not_expired <- not expired;
  do finished_and_not_expired <- and finished not_expired ;
  (if finished_and_not_expired then (* i remove its entry (NB the first one) from active list*)
    remove_first
  else
    ret tt)
  ;;

  do active_entries <- get_active_entries ;
  do new_entries <- C_map_CNat_Entry create_entry_from_job_id new_jobs ;
  do new_active_entries <- insert_Entries new_entries active_entries cmp_entry_deadline ;
  (*insert_entries (* insert new entries generated from the new incoming jobs in the active list *)
    (map 
      (fun job_id => mk_Entry job_id (Jobs job_id).(budget) (S((Jobs job_id).(deadline)-(Jobs job_id).(arrival)))) 
      new_jobs
    ) ;;
  *)
  do r <- get_running ; (* obtain id of the running job (possibly none) from head of active list*)
  ret (r,late).
  (*  return the job id (if any) that has beed running, and whether or not the job was late   *)

(* Rewrite me, monadic + Clist *)
Definition decrease_cnt_first : RT unit :=
  do active_entries <- get_active_entries ;
  do current_job_entry <- get_EntryList_head active_entries ;
  do decreased_counter_current_job_entry <- decrease_counter current_job_entry ;
  (* This is insane in C - the following operations correspond to identity *)
  (* ALED *)
  do active_entries_tail <- get_EntryList_tail active_entries ;
  do updated_active_entries <- add_EntryList_head decreased_counter_current_job_entry active_entries_tail ;
  set_active_entries updated_active_entries.
(* fun _ s => match s.(active) with
| [] => (tt, s)
| e :: es =>
  (tt, {|
    now := s.(now);
    active := mk_Entry (id e) (pred (cnt e)) (del e) :: es
  |})
end.*)




(* primitive that removes the first entry if it exists and has expired *)
Definition remove_first_if_expired : RT unit :=
  do active_entries <- get_active_entries ;
  do current_job_entry <- get_EntryList_head active_entries ;
  do current_job_entry_counter <- get_counter current_job_entry ;
  do current_job_entry_is_expired <- CNat.eqb current_job_entry_counter 0 ;
  if current_job_is_expired then
    do removed_head_active_entries <- remove_EntryList_head active_entries ;
    set_active_entries removed_head_active_entries
  else
    ret tt.
(* fun _ s => match s.(active) with
| [] => (tt, s)
| e :: es =>
    if ( Nat.eqb (cnt e)   0)
    then (tt, {| now := s.(now); active :=  es |})
    else (tt,s)
end.*)

(* Definition decrease_all_del_func(l : list Entry) :=
  map (fun e => {|
      id := e.(id);
      cnt := e.(cnt);
      del := pred e.(del)
  |}) l. *)

Definition decrease_all_del : RT unit :=
  do active_entries_list <- get_active_entries ;
  decreased_del_active_entries <- C_map_Entrylist decrease_del active_entries_list ;
  set_active_entries decreased_del_active_entries.
(*fun _ s =>
    (tt, {|
    now := s.(now);
    active := decrease_all_del_func s.(active)
    |}).*)

(* primitive that increases the time counter *)
Definition inc_time_counter : RT unit :=
  do time_counter <- get_time_counter ;
  do next_time_counter <- succ time_counter ;
  set_time_counter next_time_counter.

Definition update_counters(N: nat) : RT unit :=
  decrease_cnt_first;; (* decrease cnt field of first entry corresponding to the running job*)
  remove_first_if_expired;; (* if field became 0 the budget's job is 0 : remove it from actve list *)
  decrease_all_del ;;
  inc_time_counter.

(** Election function used by the partition *)
Definition scheduler(N:nat)  : RT ((option nat)*bool) :=
  do p <- update_entries N ;
  update_counters N ;;
  ret p.