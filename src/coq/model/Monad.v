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

(* This Coq module defines a simple state monad with failure, as an
   example of use of digger to extract some monadic code into C code *)

From Model Require Import AbstractTypes.

Require Import FunctionalExtensionality.

Declare Scope monad_scope.
Open Scope monad_scope.

(** the monad *)

(* type constructor *)
Definition RT (A : Type) : Type := Env -> State -> A * State.

(* return *)
Definition ret {A : Type} (a : A) : RT A :=
fun _ s => (a, s).

(* sequence *)
Definition bind {A B : Type} (m : RT A) (f : A -> RT B) : RT B :=
fun env s => let (a, s') := m env s in f a env s'.

(* notations for the sequence *)
Notation "'do' x <- m ; e" :=
  (bind m (fun x => e))
  (at level 60, x ident, m at level 200, e at level 60) : monad_scope.
Notation " m ;; e" :=
  (bind m (fun _ => e))
  (at level 60, e at level 60) : monad_scope.


(** monad laws *)


Lemma ret_bind (A B : Type) (a : A) (f : A -> RT B) : do x <- ret a ; f x = f a.
Proof.
extensionality env.
extensionality s.
reflexivity.
Qed.

Lemma bind_ret (A : Type) (m : RT A) : do x <- m ; ret x = m.
Proof.
unfold bind.
extensionality env.
extensionality s.
destruct (m env s); reflexivity.
Qed.

Lemma bind_bind (A B C : Type) (m : RT A) (f : A -> RT B) (g : B -> RT C) :
do y <- (do x <- m ; f x); g y = do x <- m; do y <- f x; g y.
Proof.
unfold bind.
extensionality env.
extensionality s.
destruct (m env s); reflexivity.
Qed.