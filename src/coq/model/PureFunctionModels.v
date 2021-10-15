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
From Scheduler.Model.Interface.Types Require Import TypesModel.
Require Import List.

(* primitive *)

Parameter Jobs : CNat -> Job.

Fixpoint insert_Entry_aux (entry : Entry)
                          (entry_list : list Entry)
                          (comp_func : Entry -> Entry -> CBool)
                          : list Entry :=
  match entry_list with
  | nil => cons entry nil
  | cons head tail =>
      match comp_func entry head with
      | true => cons entry (cons head tail)
      | false => cons head (insert_Entry_aux entry tail comp_func)
      end
  end.

Fixpoint insert_Entries_aux (entries_to_be_added : list Entry)
                            (entry_list : list Entry)
                            (comp_func : Entry -> Entry -> CBool)
                            : list Entry :=
  match entries_to_be_added with
  | nil => entry_list
  | cons entry remaining_entries => 
      insert_Entries_aux remaining_entries (insert_Entry_aux entry entry_list comp_func) comp_func
  end.