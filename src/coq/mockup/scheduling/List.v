Require Import Jobs.
Require Import AbstractTypes.

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