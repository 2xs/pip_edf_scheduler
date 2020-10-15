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

From SchedulerMockup Require Import Jobs.
From SchedulerMockup Require Import Entry.
From SchedulerMockup Require Import CNat.
From Model Require Import AbstractTypes.
From Model Require Import AbstractFunctions.
From Model Require Import Monad.

Require Import List.

(** Doit construire un type Liste d'entry 
    et un type liste de Jobs *)

Definition create_JobList : RT JobList :=
  ret nil.

Definition create_EntryList : RT EntryList :=
  ret nil.

Definition create_CNatList : RT CNatList :=
  ret nil.

Definition add_JobList_head (head : Job) (list : JobList) : RT JobList :=
  ret (cons head list).

Definition add_EntryList_head (head : Entry) (list : EntryList) : RT EntryList :=
  ret (cons head list).

Definition add_CNatList_head (head : nat) (list : CNatList) : RT CNatList :=
  ret (cons head list).

Definition get_JobList_head (list : JobList) : RT Job :=
  match list with
  | nil => ret default_Job
  | cons head _ => ret head
  end.

Definition get_EntryList_head (list : EntryList) : RT Entry :=
  match list with
  | nil => ret default_Entry
  | cons head _ => ret head
  end.

Definition get_CNatList_head (list : CNatList) : RT nat :=
  match list with
  | nil => ret default_nat
  | cons head _ => ret head
  end.

Definition get_JobList_tail (list : JobList) : RT JobList :=
  match list with
  | nil => ret nil
  | cons _ tail => ret tail
  end.

Definition get_EntryList_tail (list : EntryList) : RT EntryList :=
  match list with
  | nil => ret nil
  | cons _ tail => ret tail
  end.

Definition get_CNatList_tail (list : CNatList) : RT CNatList :=
  match list with
  | nil => ret nil
  | cons _ tail => ret tail
  end.

Definition remove_JobList_head (list : JobList) : RT JobList :=
  get_JobList_tail list.

Definition remove_EntryList_head (list : EntryList) : RT EntryList :=
  get_EntryList_tail list.

Definition remove_CNatList_head (list : CNatList) : RT CNatList :=
  get_CNatList_tail list.

(* inserts an Entry in an EntryList in a sorted way *)
Definition insert_Entry (entry : Entry)
                        (list  : EntryList)
                        (comp_func : Entry -> Entry -> bool)
                        : RT EntryList :=
  ret (insert_Entry_aux entry list comp_func).

(* inserts a Job in a JobList in a sorted way *)
Definition insert_Job (job  : Job)
                      (list : JobList)
                      (comp_func : Job -> Job -> bool)
                      : RT JobList :=
  ret (insert_Job_aux job list comp_func).

(* inserts several entries in a EntryList in a sorted way *)
Definition insert_Entries (entries : EntryList)
                          (list  : EntryList)
                          (comp_func : Entry -> Entry -> bool)
                          : RT EntryList :=
  ret (insert_Entries_aux
        entries list
        comp_func
      ).

(* inserts several jobs in a JobList in a sorted way *)
Definition insert_Jobs (jobs_to_insert : JobList)
                       (list : JobList)
                       (comp_func : Job -> Job -> bool)
                       : RT JobList :=
  ret (insert_Jobs_aux jobs_to_insert list comp_func).

Definition C_map_Entry_Entry (func : Entry -> RT Entry) (entry_list : EntryList) : RT EntryList :=
  ret (map func entry_list).

Definition insert_active_entry (entry : Entry) (comp_func : Entry -> Entry -> bool) : RT unit :=
  fun _ s => (a, {|
                  now := now s,
                  active_entries := (insert_Entry_aux entry 
                                                      (active_entries s)
                                                      comp_func)
                 |}
             ).

Definition update_entries (func : Entry -> Entry) : RT unit :=
  fun _ s => (a, {|
                  now := now s,
                  active_entries := map func (active_entries s)
                |}).

Definition C_map_CNat_Entry (func : nat -> Entry) (nat_list : CNatList) : RT EntryList :=
  ret (map func nat_list).