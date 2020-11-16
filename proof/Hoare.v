Require Import FunctionalExtensionality List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import  Coq.Numbers.Natural.Peano.NPeano.
From Scheduler.Proof Require Import Lib Assumptions JobsAxioms.
From Scheduler.Model Require Import Monad AbstractTypes.
From Scheduler.PartitionMockup Require Import Primitives.

(* definition of a Hoare triple *)
Definition hoare
  {A : Type}
  (Pre : Env -> State -> Prop) (m : RT A) (Post : A -> State -> Prop) : Prop :=
forall env s, Pre env s -> let (a, s') := m env s in Post a s'.

(* notation for Hoare triple *)
Notation "{{ Pre }} m {{ Post }}" :=
(hoare Pre m Post)
  (at level 90,
   format "'[' '[' {{  Pre  }}  ']' '/  ' '[' m ']' '['  {{  Post  }} ']' ']'"
  ) : monad_scope.

(* weakening  a Hoare triple *)
Lemma weaken
  (A : Type) (m : RT A)
  (P Q : Env -> State -> Prop) (R : A -> State -> Prop) :
  {{ Q }} m {{ R }} -> (forall env s, P env s -> Q env s) -> {{ P }} m {{ R }}.
Proof.
intros Hm Himpl env s HP.
apply Hm, Himpl, HP.
Qed.

(* strengthening  a Hoare triple *)
Lemma strengthen
  (A : Type) (m : RT A)
  (P : Env -> State -> Prop) (Q R : A -> State -> Prop) :
  {{ P }} m {{ R }} -> (forall a s, R a s -> Q a s) -> {{ P }} m {{ Q }}.
Proof.
  intros Hm Himpl env s HP.
  unfold hoare in Hm.
  specialize (Hm env s HP).
  case_eq (m env s); intros.
  rewrite H in Hm.
  apply Himpl; auto.
Qed.

(* decomposition of a bind : with the tail in the first subgoal *)
Lemma backward
  (A B : Type) (m : RT A) (f : A -> RT B)
  (P : Env -> State -> Prop) (Q : A -> State -> Prop)
  (R : B -> State ->  Prop) :
(forall a, {{ fun env s => Q a s }} f a {{ R }}) ->
{{ P }} m {{ Q }} ->
{{ P }} bind m f {{ R }}.
Proof.
unfold bind.
intros Hf Hm env s HP.
specialize (Hm env s HP).
destruct (m env s) as [a s'].
specialize (Hf a env s').
cbn in Hf.
apply Hf, Hm.
Qed.

(* decomposition of a bind : with the tail in the second subgoal *)
Lemma forward
  (A B : Type) (m : RT A) (f : A -> RT B)
  (P : Env -> State -> Prop) (Q : A -> State -> Prop)
  (R : B -> State ->  Prop) :
{{ P }} m {{ Q }} ->
(forall a, {{ fun env s => Q a s }} f a {{ R }}) ->
{{ P }} bind m f {{ R }}.
Proof.
intros; eapply backward; eassumption.
Qed.

(** weakest precondition in general *)

(* definition of the weakest precondition *)
Definition wp
  {A : Type} (Q : A -> State -> Prop) (m : RT A) : Env -> State -> Prop :=
fun env s => let (a, s') := m env s in Q a s'.

(* [wp] computes a precontition *)
Lemma wp_precondition (A : Type) (Q : A -> State -> Prop) (m : RT A) :
{{ wp Q m }} m {{ Q }}.
Proof.
unfold hoare.
tauto.
Qed.

(* The precondition computed by [wp] is the weakest *)
Lemma wp_weakest
  (A : Type) (P : Env -> State -> Prop) (Q : A -> State -> Prop) (m : RT A) :
  {{ P }} m {{ Q }} -> forall env s, P env s -> wp Q m env s.
Proof.
trivial.
Qed.

(*
Module PrimitiveTriples (J : JobsMod).
Import J.
Module P := Primitives J.
Import P.  
  (** weakest preconditions of primitives *)
  (* the weakest precondition of [ret] *)

  Lemma ret_wp (A : Type) (a : A) (Q : A -> State -> Prop) :
wp Q (ret a) = fun _ s => Q a s.
Proof.
reflexivity.
Qed.

(* the weakest precondition of [bind] *)
Lemma bind_wp (A B : Type) (m : RT A) (f : A -> RT B) (R : B -> State -> Prop) :
wp R (bind m f) =
fun env s => wp (fun a s => wp R (f a) env s) m env s.
Proof.
unfold wp, bind.
extensionality env.
extensionality s.
destruct (m env s); reflexivity.
Qed.

(* the weakest-precondition triple of [ret] *)
Lemma ret_triple (A : Type) (a : A) (Q : A -> State -> Prop) :
{{ fun _ s => Q a s }} ret a {{ Q }}.
Proof.
eapply weaken.
- apply wp_precondition.
- tauto.
Qed.

(* the weakest precondition of [jobs_arriving] *)


Lemma jobs_arriving_wp(N:nat) (Q : list nat -> State -> Prop) :
wp Q (jobs_arriving N) = fun env s => Q ( filter (fun j =>  j <? N) (map jobid (env s.(now)))) s.
Proof.
reflexivity.
Qed.



(* the weakest-precondition triple of [jobs_arriving] *)
Lemma jobs_arriving_triple(N:nat) (Q : list nat -> State -> Prop) :
{{ fun env s => Q ( filter (fun j =>  j <? N) (map jobid (env s.(now)))) s }} jobs_arriving N {{ Q }}.
Proof.
eapply weaken.
- apply wp_precondition.
- tauto.
Qed.

Lemma job_terminating_wp (Q : bool -> State -> Prop) :
  wp Q job_terminating =
  fun _ s =>
    Q
      (match head s.(active) with
         None => false
       | Some e =>
          let j := Jobs (e.(id)) in       
         Nat.leb  e.(cnt)  (j.(budget) - j.(duration)) 
         end)
       s.
Proof.
reflexivity.
Qed.

(* the weakest-precondition triple of [job_terminating] *)
Lemma job_terminating_triple (Q : bool -> State -> Prop) :
{{ fun _ s =>
    Q
      (match head s.(active) with
         None => false
       | Some e =>
          let j := Jobs (e.(id)) in       
         Nat.leb  e.(cnt)  (j.(budget) - j.(duration))
         end)
       s }} job_terminating {{ Q }}.
Proof.
eapply weaken.
- apply wp_precondition.
- tauto.
Qed.

(* the weakest precondition of [job_expired]*)
Lemma job_expired_wp (Q : bool -> State -> Prop) :
  wp Q job_expired =
  fun _ s =>
    Q
      (match head s.(active) with
         None => false
       | Some e =>      
         Nat.eqb  e.(cnt) 0 
         end)
       s.
Proof.
  reflexivity.
Qed.  


Lemma job_expired_triple (Q : bool -> State -> Prop) :
{{ fun _ s =>
    Q
      (match head s.(active) with
         None => false
       | Some e =>    
         Nat.eqb  e.(cnt)  0
         end)
       s }} job_expired {{ Q }}.
Proof.
eapply weaken.
- apply wp_precondition.
- tauto.
Qed.

(* the weakest precondition of [job_expired]*)
Lemma job_late_wp (Q : bool -> State -> Prop) :
  wp Q job_late =
  fun _ s =>
    Q
      (match head s.(active) with
         None => false
       | Some e =>      
         Nat.eqb  e.(del) 0 
         end)
       s.
Proof.
  reflexivity.
Qed.  


Lemma job_late_triple (Q : bool -> State -> Prop) :
{{ fun _ s =>
    Q
      (match head s.(active) with
         None => false
       | Some e =>    
         Nat.eqb  e.(del)  0
         end)
       s }} job_late {{ Q }}.
Proof.
eapply weaken.
- apply wp_precondition.
- tauto.
Qed.

(* the weakest precondition of [insert_entries] *)
Lemma insert_entries_wp (l : list Entry) (Q : unit -> State -> Prop) :
wp Q (insert_entries l) =
fun _ s => Q tt {|
  now := now s;
  active := insert_all _(fun e1 e2 =>
                            (Jobs(e1.(id))).(deadline) <=?
                            (Jobs(e2.(id))).(deadline)) l (active s)
|}.
Proof.
reflexivity.
Qed.

(* the weakest-precondition triple of [insert_entries] *)
Lemma insert_entries_triple (l : list Entry) (Q : unit -> State -> Prop) :
{{ fun _ s => Q tt {|
    now := now s;
    active := insert_all _ (fun e1 e2 =>
                            (Jobs(e1.(id))).(deadline) <=?
                            (Jobs(e2.(id))).(deadline)) l (active s)
  |}
}}
insert_entries l
{{ Q }}.
Proof.
eapply weaken.
- apply wp_precondition.
- tauto.
Qed.



Lemma decrease_all_del_wp (Q : unit -> State -> Prop) :
  wp Q decrease_all_del =
   fun _ s =>
    Q tt {|
    now := s.(now);
    active := decrease_all_del_func s.(active)
      |}.
Proof.
reflexivity.
Qed.

(* the weakest-precondition triple of [decrease_all_del] *)
Lemma decrease_all_del_triple (Q : unit -> State -> Prop) :
{{ fun _ s =>
    Q tt {|
    now := s.(now);
    active := decrease_all_del_func s.(active)
      |}
}}
decrease_all_del
{{ Q }}.
Proof.
eapply weaken.
- apply wp_precondition.
- tauto.
Qed.

(* the weakest precondition of [inc_time_counter] *)
Lemma inc_time_counter_wp (Q : unit -> State -> Prop) :
wp Q inc_time_counter =
fun _ s => Q tt {| now := 1 +  s.(now); active := s.(active) |}.
Proof.
reflexivity.
Qed.

(* the weakest-precondition triple of [inc_time_counter] *)
Lemma inc_time_counter_triple (Q : unit -> State -> Prop) :
{{ fun _ s =>
  Q tt {| now := 1 +  s.(now); active := s.(active) |} }}
inc_time_counter
{{ Q }}.
Proof.
eapply weaken.
- apply wp_precondition.
- tauto.
Qed.

(* the weakest precondition of [decrease_cnt_first] *)
Lemma decrease_cnt_first_wp (Q : unit -> State -> Prop) :
wp Q decrease_cnt_first = fun _ s => let (a, s') := match active s with
  | nil => (tt, s)
  | e :: es => (tt, {|
    now := now s;
    active := {| id := id e; cnt := Nat.pred (cnt e); del := del e |} :: es
  |}) end in Q a s'.
Proof.
reflexivity.
Qed.

(* the weakest-precondition triple of [decrease_cnt_first] : empty case *)
Lemma decrease_cnt_first_triple_empty (Q : unit -> State -> Prop) :
{{ fun _ s => s.(active) = nil /\ Q tt s }} decrease_cnt_first {{ Q }}.
Proof.
eapply weaken.
- apply wp_precondition.
- intros env s.
  unfold wp, decrease_cnt_first.
  destruct s.(active) as [ | e es].
  + tauto.
  + firstorder discriminate.
Qed.

(* the weakest-precondition triple of [decrease_cnt_first] : non-empty case *)
Lemma decrease_cnt_first_triple_nonempty (Q : unit -> State -> Prop) :
{{ fun _ s => exists e es, s.(active) = e :: es /\
  Q tt {|
    now := now s;
    active := {|
      id := id e;
      cnt := Nat.pred (cnt e);
      del := del e |} :: es |} }}
decrease_cnt_first
{{ Q }}.
Proof.
eapply weaken.
- apply wp_precondition.
- intros env s.
  unfold wp, decrease_cnt_first.
  destruct s.(active) as [ | e es].
  + firstorder discriminate.
  + intros (e' & es' & Heq & HQ).
    congruence.
Qed.

(* the weakest-precondition triple of [decrease_cnt_first] *)
Lemma decrease_cnt_first_triple (Q : unit -> State -> Prop) :
{{ fun _ s => let (a, s') := match active s with
  | nil => (tt, s)
  | e :: es => (tt, {|
    now := now s;
    active := {| id := id e; cnt := Nat.pred (cnt e); del := del e |} :: es
  |}) end in Q a s'
}}
decrease_cnt_first
{{ Q }}.
Proof.
eapply weaken.
- apply wp_precondition.
- tauto.
Qed.



Lemma remove_first_wp (Q : unit -> State -> Prop) :
  wp Q remove_first =
  fun _ s =>
   Q tt  {| now := now s; active := tail s.(active) |}.
Proof.
reflexivity.
Qed.


(* the weakest-precondition triple of [remove_first] *)
Lemma remove_first_triple (Q : unit -> State -> Prop) :
{{
fun _ s =>
   Q tt  {| now := now s; active := tail s.(active) |}      
}}
remove_first
{{ Q }}.
Proof.
eapply weaken.
- apply wp_precondition.
- tauto.
Qed.

(* the weakest precondition of [remove_first_if_expired] *)
Lemma remove_first_if_expired_wp (Q : unit -> State -> Prop) :
wp Q remove_first_if_expired = fun _ s => let (a, s') := match active s with
  | nil => (tt, s)
  | e :: es =>
    if Nat.eqb e.(cnt) 0
    then (tt, {| now := now s; active := es |})
    else (tt, s)
  end in Q a s'.
Proof.
reflexivity.
Qed.

(* the weakest-precondition triple of [remove_first_if_expired] : empty case *)
Lemma remove_first_if_expired_triple_empty (Q : unit -> State -> Prop) :
{{ fun _ s => s.(active) = nil /\ Q tt s }} remove_first_if_expired {{ Q }}.
Proof.
eapply weaken.
- apply wp_precondition.
- intros env s.
  unfold wp, remove_first_if_expired.
  destruct s.(active) as [ | e es].
  + tauto.
  + firstorder discriminate.
Qed.

(* the weakest-precondition triple of [remove_first_if_expired] :
   non-empty case *)
Lemma remove_first_if_expired_triple_nonempty (Q : unit -> State -> Prop) :
{{ fun _ s => exists e es, s.(active) = e :: es /\
  if Nat.eqb e.(cnt) 0
  then Q tt {| now := now s; active := es |}
  else Q tt s }}
remove_first_if_expired
{{ Q }}.
Proof.
eapply weaken.
- apply wp_precondition.
- intros env s.
  unfold wp, remove_first_if_expired.
  destruct s.(active) as [ | e es].
  + firstorder discriminate.
  + intros (e' & es' & Heq & HQ).
    injection Heq; intros; subst e' es'.
    destruct (Nat.eqb  _ _); assumption.
Qed.

(* the weakest-precondition triple of [remove_first_if_expired] *)
Lemma remove_first_if_expired_triple (Q : unit -> State -> Prop) :
{{ fun _ s => let (a, s') := match active s with
  | nil => (tt, s)
  | e :: es =>
    if Nat.eqb e.(cnt) 0
    then (tt, {| now := now s; active := es |})
    else (tt, s)
  end in Q a s'
}}
remove_first_if_expired
{{ Q }}.
Proof.
eapply weaken.
- apply wp_precondition.
- tauto.
Qed.



Lemma get_running_wp  (Q : (option nat) -> State -> Prop) :
wp Q (get_running) =
fun _ s =>
  Q
    ( match s.(active) with
           [] => None
          | e :: _  => Some e.(id)
          end
        )
    s.
Proof.
  unfold wp, get_running.
  cbn.
  repeat (apply functional_extensionality; intros).
  case_eq (active x0) ; intros; auto.
Qed.

(* the weakest-precondition triple of [get_running] *)
Lemma get_running_triple (Q : (option nat) -> State -> Prop) :
  {{ fun _ s =>
       Q
        ( match s.(active) with
           [] => None
          | e :: _  => Some e.(id)
          end
        )
       s }}
get_running
{{ Q }}.
Proof.
eapply weaken.
- apply wp_precondition.
- intros env s.
  unfold wp, get_running.
  case_eq (active s) ; intros; auto.
Qed.

End PrimitiveTriples.
*)
