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

Require Import Jobs.
Require Import AbstractTypes.

(** Doit construire un type Liste d'entry 
    et un type liste de Jobs *)

(** Structure contenue dans la liste C *)
Record element_type := {
  entry : Entry;
  job : Job;
}.

Parameter null_element : element_type.

Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A
.

(** Redéfini en C *)
Inductive pip_list (A : element_type) : Type := 
  | nil : pip_list%A)
  | cons  : A -> pip_list A -> pip_list A.

(** Redéfini en C *)
Definition create_list : LLI pip_list :=
  ret nil.

(** Redéfini en C *)
Definition add_head (head : element_type) (list : pip_list) : LLI pip_list :=
  ret cons head list.

(** Redéfini en C *)
Definition get_head (list : pip_list) : LLI element_type :=
  match list with
  | nil _ => ret null_element
  | cons elem _ _ => ret elem
  end
.

(** Redéfini en C *)
Definition get_tail (list : pip_list) : LLI pip_list :=
  match list with
  | nil _ => ret nil
  | cons _ tail _ => ret tail
  end
.

Definition remove_head (list : pip_list) : LLI pip_list :=
  get_tail list.

(** Fonction compilée en C *)
Definition example : LLI unit := 
  perform new_list := create_list in
  perform head := Build_element_type true in
  perform other_list := add_head head new_list in
  perform last_list := remove_head other_list in
  ret tt;;