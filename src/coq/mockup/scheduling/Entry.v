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

From Scheduler.Model Require Import AbstractFunctions.
From Scheduler.Model Require Import AbstractTypes.
From Scheduler.Model Require Import Monad.

Parameter default_entry : Entry.
Parameter is_default_entry : Entry -> RT CBool.

(* TODO constructor accessors *)

Definition get_entry_counter (entry : Entry) : RT CNat :=
  ret (cnt entry).

Definition get_entry_id (entry : Entry) : RT CNat :=
  ret (id entry).

Definition get_entry_delete (entry : Entry) : RT CNat :=
  ret (del entry).

Definition decrease_del (entry : Entry) : Entry :=
  (fun e =>
  {|
      id := e.(id);
      cnt := e.(cnt);
      del := pred e.(del)
  |}) entry.

Definition decrease_cnt (entry : Entry) : Entry :=
  (fun e =>
  {|
      id := e.(id);
      cnt := pred e.(cnt);
      del := e.(del)
  |}) entry.

Definition cmp_entry_deadline (entry1 entry2 : Entry) : CBool :=
  Nat.leb
    (Jobs(entry1.(id))).(deadline)
    (Jobs(entry2.(id))).(deadline).

Definition make_entry (id : CNat) (cnt : CNat) (del : CNat) : RT Entry :=
  ret (mk_Entry id cnt del).