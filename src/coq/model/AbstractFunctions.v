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

(* primitive *)
Parameter get_job_from_job_id : nat -> RT Job.

Fixpoint insert_Entry_aux (entry : Entry)
                          (list : EntryList)
                          (comp_func : Entry -> Entry -> bool)
                          : EntryList :=
  match list with
  | nil => cons entry nil
  | cons head tail =>
      match comp_func entry head with
      | true => cons entry (cons head tail)
      | false => cons head (insert_Entry_aux entry tail comp_func)
      end
  end.

Fixpoint insert_Job_aux (job : Job)
                        (list : JobList)
                        (comp_func : Job -> Job -> bool)
                        : JobList :=
  match list with
  | nil => cons job nil
  | cons head tail =>
      match comp_func job head with
      | true => cons job (cons head tail)
      | false => cons head (insert_Job_aux job tail comp_func)
      end
  end.

Fixpoint insert_Entries_aux (entries : EntryList)
                            (list : EntryList)
                            (comp_func : Entry -> Entry -> bool)
                            : EntryList :=
  match entries with
  | nil => list
  | cons entry remaining_entries => 
      insert_Entries_aux remaining_entries (insert_Entry_aux entry list comp_func) comp_func
  end.

Fixpoint insert_Jobs_aux (jobs : JobList)
                         (list : JobList)
                         (comp_func : Job -> Job -> bool)
                         : JobList :=
  match jobs with
  | nil => list
  | cons job remaining_jobs => 
      insert_Jobs_aux remaining_jobs (insert_Job_aux job list comp_func) comp_func
  end.