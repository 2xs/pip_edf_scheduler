Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Minus.
Require Import  Coq.Numbers.Natural.Peano.NPeano.
(* Require Import  Coq.Arith.PeanoNat.*)
Require Import Coq.Bool.Bool.
Require Import Lia.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Classical.
Require Import List.
Import ListNotations.


Section GenericSum.
   
 Fixpoint generic_sum
          (f : nat -> nat)(filter : nat -> bool)
          (i j : nat) : nat :=
    match j with 
      0 => 0
    | S j'  => (if  (filter j') && (i <=? j') then f j' else 0) +
               generic_sum f filter i j'
    end.

    
  
  Lemma generic_sum_le_S : forall f filter i j,
      i <= j -> generic_sum f filter i (S j) =
               (if filter j then f j else 0) +  generic_sum f filter i j.  
  Proof.
    intros.
    unfold generic_sum.
    replace  (i <=? j) with true.
    * rewrite andb_true_r; reflexivity.
    * symmetry; rewrite leb_le ; assumption.
  Qed.

  Lemma generic_sum_lt_S : forall f filter i j,
      j < i -> generic_sum f filter i (S j) =  generic_sum f filter i j.  
  Proof.
    intros.
    unfold generic_sum.
    replace  (i <=? j) with false.
    * rewrite andb_false_r; reflexivity.
    * case_eq (i <=? j) ; intros; auto.
      rewrite leb_le in H0 ; lia. 
  Qed.


  Lemma generic_sum_eq  : forall f filter j i, j <= i -> generic_sum f filter i j = 0.
  Proof.
    intros f filter.
    induction j ; intros; auto.
    rewrite generic_sum_lt_S; try lia.
    apply IHj; lia.
  Qed.

  
  Lemma generic_sum_rev_le_S : forall f filter i j,
      i < j -> generic_sum f filter i j =
        (if filter i then f i else 0) +  generic_sum f filter (S i) j.  
  Proof.
    intros f filter i j Hlt.
    induction Hlt.
    * rewrite generic_sum_eq with (i := S i)(j := S i); auto.
      rewrite generic_sum_le_S; auto.
      rewrite generic_sum_eq; auto.
    * rewrite generic_sum_le_S; auto with arith.
      rewrite IHHlt.
      rewrite generic_sum_le_S; auto; lia.
  Qed.
  

 Lemma generic_sum_f_eq : forall f1 f2 filter i j,
  i <= j -> (forall k,  i <= k -> k < j -> filter k = true -> f1 k = f2 k) -> 
     generic_sum f1 filter i j = generic_sum f2 filter i j.
 Proof.
  intros f1 f2 filter i j Hle.
  induction Hle ; intros.
 *  do 2 (rewrite  generic_sum_eq ; auto).
 *
   cbn.
   case_eq (filter m) ; intro Hcase.
    + rewrite H  ; auto ; try lia.
     rewrite Nat.add_cancel_l.
     apply IHHle ; auto.
    + rewrite IHHle ; auto.
 Qed.

  Lemma generic_sum_f_ge : forall f1 f2 filter i j,
  i <= j -> (forall k,  i <= k -> k < j ->  f1 k >= f2 k) -> 
     generic_sum f1 filter i j  >= generic_sum f2 filter i j.
 Proof.
  intros f1 f2 filter i j Hle.
  induction Hle ; intros.
 *  do 2 (rewrite  generic_sum_eq ; auto).
 *
   cbn.
   case_eq (filter m) ; intro Hcase.
   + apply plus_le_compat.
    - replace (i <=? m) with true; [| symmetry ; rewrite leb_le; auto].
      apply H ; auto with arith.
    -
     apply IHHle ; auto.
  + apply IHHle ; auto.
 Qed.

 Lemma generic_sum_split :
   forall f filter filter' i j,
     i <= j ->
     generic_sum f filter i j =
     generic_sum f (fun k => filter k && filter' k) i j +
      generic_sum f (fun k => filter k && negb (filter' k)) i j .
 Proof.
   intros f filter filter' i j Hle.
   induction Hle.   
   *
      do 3 (rewrite  generic_sum_eq ; auto).
   *
     cbn.
     rewrite IHHle.
     replace  (i <=? m) with true.
     + case_eq (filter' m) ; intro Hcas ; cbn;
         repeat rewrite andb_true_r;
         rewrite andb_false_r;
         lia.
     + symmetry; rewrite leb_le ; assumption.
 Qed.
 

 Lemma generic_sum_filter_eq :   forall f filter1 filter2 i j,
  i <= j -> (forall k,  i <= k -> k < j -> filter1 k = filter2 k) -> 
     generic_sum f filter1 i j = generic_sum f filter2 i j.
 Proof.
  intros f filter1 filter2 i j Hle.
  induction Hle ; intros.
 *  do 2 (rewrite  generic_sum_eq ; auto).
 *
   cbn.
   case_eq (filter1 m) ; intro Hcase.
  + rewrite <- H  ; auto ; try lia.
    rewrite Hcase.
     rewrite Nat.add_cancel_l.
     apply IHHle ; auto.
  + cbn.
    rewrite <- H  ; auto ; try lia.
    rewrite Hcase.
    rewrite IHHle ; auto.
 Qed.

  Lemma generic_sum_filter_ge :   forall f filter1 filter2 i j,
  i <= j ->
     generic_sum f filter1 i j >=  generic_sum f (fun i => filter2 i && filter1 i) i j.
 Proof.
  intros f filter1 filter2 i j Hle.
  induction Hle ; intros.
 *  do 2 (rewrite  generic_sum_eq ; auto).
 *
   cbn.
   case_eq (filter1 m) ; intro Hcase.
  +  cbn.
     apply plus_le_compat.
    - case_eq (filter2 m); intro Hcase2 ; cbn; auto with arith.
    - apply IHHle.
  + cbn.
    case_eq (filter2 m); intro Hcase2 ; cbn; auto with arith.
 Qed.

 Lemma generic_sum_0 :
   forall f i j,  i <= j ->    generic_sum f (fun _ => false) i j = 0.
 Proof.  
   intros  f i j Hle.
   induction Hle.
   * apply generic_sum_eq ; auto.
   * apply IHHle.
 Qed.

 Lemma generic_sum_gt_0_ex :
   forall f filter i j,
     i <= j ->
     generic_sum f filter i j > 0 ->
     exists k, k < j /\ filter k = true /\ f k > 0.
 Proof.  
   intros  f filter i j Hle.
   induction Hle; intros.
   * rewrite generic_sum_eq in H ; lia.
   * rewrite generic_sum_le_S in H; auto.
     case_eq (filter m) ; intro Hcas.
   +   rewrite Hcas in H.
       case (gt_dec  (generic_sum f filter i m) 0);
         intros Hcas'; subst.
       -   destruct (IHHle Hcas') as (k & Hkm & Hf & Hfk).
         exists k ; repeat split; auto ; lia.
       - exists m ; repeat split ; auto ; lia.
    +  rewrite Hcas in H; cbn in H.
       destruct (IHHle H) as (k & Hkm & Hf & Hfk).
       exists k; split ; auto.
 Qed. 

 Lemma generic_sum_rev_gt_0_ex :
   forall f filter i j,
     i <= j ->  (exists k,i <= k /\  k < j /\ filter k = true /\ f k > 0) -> 
     generic_sum f filter i j > 0. 
 Proof.  
   intros  f filter i j Hle.
   induction Hle; intros.
   * destruct H as (k & Habs1 & Habs2 & Hrest) ; lia. 
   *  destruct H as (k & Hik & Hksm  & Hfil & Hf).
      case (le_gt_dec m k) ; intro Hcas.
      + assert (k = m) ; try lia; subst.
        rewrite generic_sum_le_S; auto.
        rewrite Hfil; lia.
      +  rewrite generic_sum_le_S; auto.
         assert ( generic_sum f filter i m > 0) ; try lia.
         apply IHHle.
         exists k ; repeat split ; auto.
 Qed. 

 Lemma generic_sum_index_split : forall f filter i j k,
   i <= k -> k < j ->   
   generic_sum f filter i j =
   generic_sum f filter i k +
   (if filter k  then f k else 0) +
   generic_sum f filter (S k) j.
 Proof.                                 
   induction j; intros k Hik Hkj; try lia.
   
   case (le_gt_dec j k) ; intros Hcas.
   * assert (k = j) ; try lia; subst.
     rewrite generic_sum_le_S; try lia.
     rewrite (generic_sum_eq _ _ (S j) (S j)); auto ; lia.
   *  do 2 (rewrite generic_sum_le_S; try lia).
      rewrite IHj with (k := k); try lia.
 Qed.
 
End GenericSum.

Section Booleans.
 
 Lemma negb_inj : forall b1 b2,  negb b1 = negb b2 -> b1 = b2.
  Proof.
    intros b1 b2 Hneg;  destruct b1, b2 ;
      try reflexivity; try discriminate.
 Qed.    

  
  Fixpoint bforall (f : nat -> bool)(N: nat) : bool :=
    match N with
      0 => true
    | S N' => andb (f N') (bforall f N')
    end.                 

  Lemma bforall_forall : forall f N,
      bforall f N  = true -> forall i,  i < N -> f i = true.
  Proof.  
  induction N ; intros.
  * lia.
  * unfold bforall in H.
    rewrite andb_true_iff in H; destruct H.
    specialize (IHN H1).
    case (le_gt_dec N i).
     + intro ; assert (i =N) ; try lia ;subst ; auto.
     +intro ; rewrite IHN ; auto ; lia.
  Qed.

   Lemma forall_bforall : forall f N,
      (forall i,  i < N -> f i = true) -> bforall f N  = true.
  Proof.  
  induction N ; intros.
  * reflexivity.
  * unfold bforall;
    rewrite andb_true_iff; split.
    + apply H ;  lia.
    + apply IHN ; intros.
      apply H ; lia.
  Qed.

 
 Lemma notbforall_exists : forall f N,
      bforall f N  = false -> exists i,  i < N /\ f i = false.
  Proof.  
  induction N ; intros.
  * inversion H.
  *  cbn in H.
    rewrite andb_false_iff in H; destruct H.
    +  exists N ; split ; auto.
    + destruct (IHN H) as (i & HiN & Hfi).
      exists i; split; auto.
  Qed.

 Lemma exists_notbforall : forall f N,
      (exists i,  i < N /\ f i = false) -> bforall f N  = false.
  Proof.  
  induction N ; intros.
  * destruct  H as (i & Habs & Hi); lia.
  *  destruct  H as (i & Hi & Hfi).
     cbn.
     rewrite andb_false_iff.
     case  (le_gt_dec N i); intro Hni.
  +  assert (i = N) ; try lia; subst.
     left ; auto.
  + right ; apply IHN.
    exists i ; repeat split; auto.
  Qed.
  
  Fixpoint bexists (f : nat -> bool)(N: nat) : bool :=
    match N with
      0 => false
    | S N' => orb (f N') (bexists f N')
    end.                 

  
  Lemma notbexists_forall : forall f N,
      bexists f N  = false -> forall i,  i < N -> f i = false.
  Proof.  
   induction N ; intros.
  * lia.
  * unfold bexists in H.
    rewrite orb_false_iff in H; destruct H.
    specialize (IHN H1).
    case (le_gt_dec N i).
     + intro ; assert (i =N) ; try lia; subst ; auto.
     +intro ; rewrite IHN ; auto ; lia.
  Qed.

  
  Lemma forall_notbexists : forall f N,
      (forall i,  i < N -> f i = false) -> bexists f N  = false.
  Proof.  
  induction N ; intros.
  * reflexivity.
  * unfold bexists;
    rewrite orb_false_iff; split.
    + apply H ;  lia.
    + apply IHN ; intros.
      apply H ; lia.
  Qed.
 
  
  Lemma bexists_exists : forall f N,
      bexists f N  = true -> exists i,  i < N /\ f i = true.
  Proof.  
  induction N ; intros.
  * inversion H.
  *  cbn in H.
    rewrite orb_true_iff in H; destruct H.
    +  exists N ; split ; auto.
    + destruct (IHN H) as (i & HiN & Hfi).
      exists i; split; auto.
  Qed.

  
  Lemma exists_bexists : forall f N,
      (exists i,  i < N /\ f i = true) -> bexists f N  = true.
  Proof.  
  induction N ; intros.
  * destruct  H as (i & Habs & Hi); lia.
  *  destruct  H as (i & Hi & Hfi).
     cbn.
     rewrite orb_true_iff.
     case  (le_gt_dec N i); intro Hni.
  +  assert (i = N) ; try lia; subst.
     left ; auto.
  + right ; apply IHN.
    exists i ; repeat split; auto.
  Qed.

End Booleans.  

Section ListsMaps.
  
Lemma In_P_map{A:Type} :
    forall  (l: list A)  P,
      (forall x, In x l -> P x = true) ->
      forall f,
        (forall x,  P x = true -> P (f x) = true) ->
        (forall y,  In y (map f l) -> P y = true).
   Proof. 
  induction l ; intros P Hinall f HPf y Hin.
  * inversion Hin.
  *  inversion Hin ; subst.
    + apply HPf, Hinall; constructor; reflexivity.
    + apply IHl with (f := f); auto.
      intros x Hin'.
      apply Hinall.
      constructor 2; assumption.
   Qed.




  Lemma map_nth_nodef{A B : Type}:
  forall (f : A -> B) (l : list A) (n : nat) (dA:A)(dB:B),
  n < length l ->  nth n (map f l) dB = f (nth n l dA).
  Proof.
    induction l; intros n dA dB Hlt.
    * cbn in*; lia.
    * cbn in Hlt. cbn.
      destruct n  ; try reflexivity.
      apply IHl; lia.
  Qed.


  
  Definition unique_for{A B : Type}
             (f: A -> B)(l: list A) : Prop :=
    NoDup (map f l).


  Lemma NoDup_filter{A : Type}  (f: A -> bool)(l: list A) : NoDup l -> NoDup (filter f l).
  Proof.
    induction l ; intros.
    * apply NoDup_nil.
    * cbn in *.
      inversion H ; subst.
      destruct (f a) ; auto.
      constructor ; auto.
      intro Hin ; apply H2.
      rewrite filter_In in Hin.
      intuition.
   Qed.
(*
Lemma unique_neutral_map{A B:Type} :
    forall (l: list A) (f: A -> B) g, 
     (forall (x:A), g (f x) = f x) 
    -> unique_for f l
    -> unique_for g (map f l).
  Proof.
    induction l ; intros f g Hfg Hun; auto.
    inversion Hun ; subst; clear Hun.
    unfold unique_for in *.
    rewrite map_map.
    cbn.
    rewrite Hfg.
    constructor.
    *  intro Hin; apply H1.
       rewrite in_map_iff in Hin.
       rewrite in_map_iff.
       destruct Hin as (x & Heq & Hin).
       exists x;split ; auto.
       rewrite Hfg in Heq; auto.
    * rewrite <- map_map.
      apply IHl ; auto.      
Qed.
  *)    
  (*Lemma unique_for_app {A B : Type}(f: A -> B)(l1 l2: list A) :
    unique_for f l1 -> unique_for f l2 ->
    (forall x y, In x l1 -> In y l2 -> f x <> f y) ->
    unique_for f (l1 ++ l2).
  Proof.
    induction l1 ; intros Hun1 Hun2 Hinboth; auto.
    cbn.
    inversion Hun1 ; subst.
    rewrite in_map_iff in H1.
    unfold unique_for in *.
    cbn.
    constructor.
    *  rewrite in_map_iff.
       intro Hex.
       apply H1.
       destruct Hex as (x  & Hfeq & Hinapp).
       exists x ; split; auto.
       rewrite in_app_iff in Hinapp.
       destruct Hinapp; auto.
       exfalso.
       apply (Hinboth a x); auto.
       constructor ; auto.
    *  apply IHl1; auto; intros.
       apply Hinboth; auto.
       constructor 2; auto.
  Qed. *)

  Lemma unique_for_In{A B: Type}(f : A -> B)(l : list A)(d:A) :
    forall x y, unique_for f l ->
                In x l -> In y l -> f x = f y -> x = y.
  Proof.
  intros x y Hun Hin1 Hin2 Hfeq.
  unfold unique_for in Hun.
  apply  In_nth  with (d :=d) in Hin1.
  apply  In_nth  with (d :=d) in Hin2.
  destruct Hin1 as (i & Hli & Hni).
  destruct Hin2 as (j & Hlj & Hnj).
  generalize (NoDup_nth (map f l) (f d)); intro HNoDup; intuition.
  clear H.
  specialize (H1 i j).
  rewrite map_length in H1.
  specialize (H1 Hli Hlj).
  do 2 rewrite map_nth in H1.
  rewrite Hni, Hnj in H1.
  rewrite <- Hni, <- Hnj.
  rewrite H1; auto.
  Qed.
(*
  Lemma In_unique_for{A B: Type}(f : A -> B)(l : list A)(d:A) :
    (forall x y, 
                In x l -> In y l -> f x = f y -> x = y) -> unique_for f l.
  Proof.
    induction l ; intros.
    * apply NoDup_nil.
    * apply NoDup_cons ; auto.
    + unfold not.
     intro.
      apply in_map_iff in H0.
      destruct H0 as (z & Heq & Hin).
      
 intros Hun.
 unfold unique_for.
 rewrite (NoDup_nth (map f l) (f d)).
 intros.
 rewrite map_length in *.
 do 2 rewrite map_nth in H1.
 generalize (nth_In) ; intro Hnth_In. 
 generalize (Hnth_In  _ i l d H); intro Hini.
 generalize (Hnth_In  _ j l d H0); intro Hinj.
 clear Hnth_In.
 specialize (Hun _ _ Hini Hinj H1).
  apply NoDup_nth.
 apply  In_nth  with (d :=d)
  apply  In_nth  with (d :=d) in Hin2.
  destruct Hin1 as (i & Hli & Hni).
  destruct Hin2 as (j & Hlj & Hnj).
  generalize (NoDup_nth (map f l) (f d)); intro HNoDup; intuition.
  clear H.
  specialize (H1 i j).
  rewrite map_length in H1.
  specialize (H1 Hli Hlj).
  do 2 rewrite map_nth in H1.
  rewrite Hni, Hnj in H1.
  rewrite <- Hni, <- Hnj.
  rewrite
 *) 
End ListsMaps.

Section SortedLists.

  Variable A : Type.
  Variable R : A -> A -> bool.
(*Hypothesis R_refl : forall a,  R a a  = true.
Hypothesis R_asym:  forall a b, R a b = true -> R b a = true -> a = b.*)
  Hypothesis R_trans : forall a b c,
      R a b = true-> R b c = true -> R a c = true.
  Hypothesis R_total : forall a b,  R a b = true \/ R b a = true.

Lemma not_false_true : forall a b,  R a b = false -> R b a = true.
  Proof.
  intros.
  destruct (R_total a b); auto.
  rewrite H in H0; discriminate.
  Qed.

  
Inductive is_sorted : list A -> Prop :=
  is_sorted_nil : is_sorted []
| is_sorted_singleton : forall a, is_sorted [a]
| is_sorted_more : forall a b l', R a b = true ->
                                 is_sorted   (b::l') ->
                                 is_sorted  (a::b::l').

Lemma is_sorted_tail : forall l a,  is_sorted (a:: l) -> is_sorted l.
Proof.
  intros l a Hs.
  inversion Hs; subst; auto; constructor.
Qed.

Lemma is_sorted_R_forall :
  forall  l a x,  is_sorted (a::l) -> In x l -> R a x = true.

Proof.                                        
  induction l;  intros a' x Hs Hin.
  * inversion Hin.
  *  inversion Hin ; subst.
     + inversion Hs ; subst; auto.
     + 
       inversion Hs ; subst; auto.
       apply IHl ; auto.
       inversion H4 ; subst.
       - constructor.
       - constructor ; auto.
         eapply R_trans ; eauto.
Qed.


Lemma R_forall_is_sorted:
  forall l a, (forall x, In x l -> R a x = true) ->
              is_sorted l -> is_sorted (a::l).
Proof.
induction l ; intros a' Hin Hsor.
* constructor.
* constructor; auto.
  apply Hin; constructor ; reflexivity.
Qed.
  

Fixpoint insert(a:A)(l:list A) :=
  match l with 
    [] => [a]
  |  b :: l' => if R a b  then  a::b:: l' else b::(insert  a l')
  end.


(* for rewriting *)
 Lemma insert_false : forall a b l,
    R a b = false -> insert a (b :: l) =  b :: (insert a l).
 Proof.
 intros a b l Hrab.   
 cbn.
 rewrite Hrab; reflexivity.
 Qed.

 Lemma insert_contents :
  forall l a x,  In x (insert a l) -> x = a \/ In x l.
 Proof.
   induction l; intros a' x Hin.
   * left.
     inversion Hin; subst ; auto.
     inversion H.
   * case_eq (R a' a); intros Hcas.
     + unfold insert in Hin; rewrite Hcas in Hin.
       inversion Hin ; subst; auto.     
     + rewrite insert_false in Hin ; auto.
       inversion Hin; subst.
        - right ; constructor; reflexivity.
        - destruct (IHl _ _ H).
          ** left; assumption.
          **  right ;constructor 2 ; assumption.
 Qed.

Lemma insert_contents_rev : 
  forall l a x, ( x = a \/ In x l ) -> In x (insert a l).
Proof.
induction l; intros a' x [Heq | Hin]; subst.
* constructor; subst ; reflexivity.
* inversion Hin.
*  case_eq (R a' a); intros Hcas.
   + unfold insert; rewrite Hcas ; constructor; reflexivity.
   + rewrite insert_false  ; auto.
     constructor 2.
     apply IHl.
     left; reflexivity.
* inversion Hin ; subst.
   +  case_eq (R a' x); intros Hcas.
      - unfold insert; rewrite Hcas.
        constructor 2; constructor; reflexivity.
      - rewrite insert_false; auto.
        constructor ; reflexivity.
   +  case_eq (R a' a); intros Hcas.
      - unfold insert; rewrite Hcas.
        do 2 (constructor 2); assumption.
    - rewrite insert_false  ; auto.
      constructor 2.
      apply IHl.
      right; assumption.
Qed.

Lemma insert_contents_iff : 
  forall l a x, ( x = a \/ In x l ) <-> In x (insert a l).
Proof.
split.  
* intros; apply insert_contents_rev; auto.
* intros; apply insert_contents; auto.
Qed.

  Lemma insert_is_sorted:
  forall l a,  is_sorted l -> is_sorted (insert a l).
  Proof.
  induction l ; intros a' Hsor.
  * constructor.
  * case_eq (R a' a); intro Hcas; cbn.  
    + rewrite Hcas.
      do 2 (constructor ; auto).
    + rewrite Hcas.
      apply not_false_true in Hcas.
      inversion Hsor ; subst.
      - do 2 ( constructor ; auto).
      - case_eq (R a' b); intros Hcas' ; cbn.
        ** rewrite Hcas'.
           do 2 (constructor; auto).
        ** rewrite Hcas'.
           constructor ; auto.
           specialize (IHl a' H2).
           cbn in IHl.
           rewrite Hcas' in IHl; auto.
Qed.

Lemma insert_unique{B:Type} : forall l x f,
    ~ In (f x) (map f l) -> unique_for f l ->
    unique_for(B:=B) f (insert x l).
Proof.
 induction l; intros x f HnIn Hun.
 * cbn.
   apply NoDup_cons.
    + intro Habs; inversion Habs.
    + apply NoDup_nil.
 * cbn.
   unfold unique_for in *.
   case_eq (R x a) ; intros Hcas.
  + cbn. 
    constructor; auto.
  + cbn.
    constructor.
    - unfold unique_for in *.
      intro Hin.
      rewrite in_map_iff in Hin.
      destruct Hin as (x0 & Heq0 & Hin0).
      inversion Hun; subst.
      rewrite in_map_iff in H1.
      apply H1.
      exists x0; split ; auto.
      rewrite <- insert_contents_iff in Hin0.
      destruct Hin0; auto.
      subst.
      exfalso.
      apply HnIn.
      cbn; left; symmetry; auto.
   -  apply IHl.
      **
        intro Hin; apply HnIn.
        right ; auto.
      **  cbn in Hun.
          inversion Hun; subst; auto.
Qed.


Fixpoint insert_all(l l': list A) :=
  match l with
    [] => l'
  |b :: l'' => insert_all l'' (insert b l')
  end.                        
 

Lemma insert_all_contents : 
  forall l l' x,  In x (insert_all l l') -> In x l  \/ In x l'.
Proof.  
 induction l ; intros l' x Hin ; auto.
 cbn in *.
 destruct (IHl _ _ Hin).
 * left; right ; assumption.
 * rewrite <- insert_contents_iff in H.
   destruct H.
   + left ; left ; subst; reflexivity.
   + right ; assumption.
Qed.

Lemma insert_all_contents_rev : 
  forall l l' x,  (In x l  \/ In x l') -> In x (insert_all l l').
Proof.  
induction l ; intros l' x [Hin | Hin']; auto.
* inversion Hin.
* inversion Hin.   
  + rewrite H in *.
    apply IHl.
    right.
    rewrite <- insert_contents_iff.
    left; reflexivity.
  +  apply IHl.
     left; assumption.   
 * apply IHl.
   right.       
   rewrite <- insert_contents_iff.
   right; assumption.
Qed.



Lemma insert_all_contents_iff : 
  forall l l' x,  (In x l  \/ In x l') <-> In x (insert_all l l').
Proof.
split.  
* intros; apply insert_all_contents_rev; auto.
* intros; apply insert_all_contents; auto.
Qed.
 

Lemma insert_all_sorted :
  forall l l',  is_sorted l' -> is_sorted (insert_all l l').
Proof.
  induction l ; intros l' Hsor ;auto.
  apply IHl.
  apply insert_is_sorted ; assumption.
Qed.


Lemma insert_all_unique{B:Type} : forall l1 l2 f,
    (forall x,  In (f x) (map f l1) -> ~ In (f x) (map f l2)) ->
    unique_for f l1 ->
    unique_for f l2 ->
    unique_for(B:=B) f (insert_all l1 l2).
Proof.
  induction l1 ; intros l2 f Hprop Hun1 Hun2; auto.
  unfold unique_for in *.
  cbn in *.
  apply IHl1.
  *  intros x Hin.
     intro HIn.
     rewrite in_map_iff in HIn.
      destruct HIn as (x0 & Hf0 & Hin0).
     apply (Hprop x).
      + right; auto.
      + 
        rewrite in_map_iff.       
        exists x0 ; split; auto.
        destruct (classic (x0 = a)); subst.
          - rewrite in_map_iff in Hin.
            destruct Hin as (y & Hfy & Hiny).
            rewrite <- Hf0 in Hfy.            
            inversion Hun1; subst.
            exfalso.
            apply H1.
            rewrite in_map_iff.
            now exists y.
          -  rewrite <- insert_contents_iff in Hin0; intuition.
   * inversion Hun1; auto.
   * apply insert_unique.
      + apply Hprop; left; auto.
      + inversion Hun1; auto.
Qed.

End SortedLists.


Section Wf_minimal.

 
  Variable A : Type.
  Variable R : A -> A -> Prop.
  Hypothesis R_wf : well_founded R.
  
  Variable P : A -> Prop.
  Hypothesis P_inh : exists x,  P x.
  
  Lemma nonempty_set_minimal_elt :
    exists y, P y /\ (forall z, P z -> ~ R z y).
  Proof.
    destruct P_inh as (x & HPx) ; clear P_inh.
    induction R_wf with (a := x).
    case (classic (exists y, R y x /\ P y)) ; intro Hcas.
    * destruct Hcas as (y & HRyx & Hpy).
      apply H0 with (y := y) ; auto.
    
    *  exists x ; split; auto.
       intros z Hpz Hzrx.
       apply Hcas.
       now exists z.
  Qed.                
End Wf_minimal.


Section PigeonHole.

  Lemma length_remove
  (A : Type) (eq_dec : forall (a1 a2 : A), {a1 = a2}+{a1 <> a2})
  (a : A) (l : list A) :
length l = length (remove eq_dec a l) + count_occ eq_dec l a.
Proof.
induction l as [ | a' l IH]; cbn; trivial.
destruct (eq_dec a a') as [Heq1 | Hneq1];
 destruct (eq_dec a' a) as [Heq2 | Hneq2]; subst; try tauto; cbn; lia.
Qed.

Lemma in_list_max (l : list nat) : l <> nil -> In (list_max l) l.
Proof.
assert (H : l = nil \/ In (list_max l) l).
{
  induction l as [ | i l' IH]; [tauto | ].
  right.
  destruct IH as [Heq | Hin].
  - subst l'.
    cbn.
    lia.
  - cbn.
    fold (list_max l').
    destruct (Compare_dec.le_ge_dec i (list_max l')) as [Hle | Hge].
    + right.
      apply Max.max_r in Hle.
      rewrite Hle.
      apply Hin.
    + apply Max.max_l in Hge.
      rewrite Hge.
      tauto.
}
tauto.
Qed.

Lemma le_list_max (n : nat) (l : list nat) : In n l -> le n (list_max l).
Proof.
induction l as [ | i l IH]; cbn; [tauto | ].
intros [Heq | Hin].
subst i.
- apply Max.le_max_l.
- etransitivity; [ | apply Max.le_max_r].
  apply IH, Hin.
Qed.

Lemma pigeon_hole (l : list nat) (n: nat) :
NoDup l -> (forall i,  In i l -> i < n) -> length l <= n.
Proof.
remember (length l) as len eqn: Hlen.
revert l n Hlen.
induction len as [ | len IH]; intros l n Hlen Hnodup Hlt; [apply le_0_n | ].
destruct n as [ | n].
- exfalso.
  destruct l as [ | i l]; [discriminate | ].
  specialize (Hlt _ (or_introl (eq_refl i))).
  lia.
- apply le_n_S, (IH (remove PeanoNat.Nat.eq_dec (list_max l) l)); clear IH.
  + clear Hlt.
    assert (Hnil : l <> nil).
    {
      contradict Hlen.
      subst l.
      discriminate.
    }
    rewrite (NoDup_count_occ' PeanoNat.Nat.eq_dec) in Hnodup.
    specialize (Hnodup _ (in_list_max _ Hnil)).
    assert (Heq := length_remove _ PeanoNat.Nat.eq_dec (list_max l) l).
    lia.
  + rewrite <- remove_alt.
    unfold remove'.
    apply NoDup_filter, Hnodup.
  + intros i Hin.
    assert (Hin' : In (list_max l) l).
    {
      apply in_list_max.
      contradict Hlen.
      subst l.
      discriminate.
    }
    assert (Hlemax : i <= list_max l).
    {
      apply le_list_max.
      apply in_remove in Hin.
      tauto.
    }
    apply in_remove in Hin.
    destruct Hin as [Hin Hneq].
    assert (Hlt1 := Hlt _ Hin).
    assert (Hlt2 := Hlt _ Hin').
    lia.
Qed.


End PigeonHole.


Section Misc.


Lemma subs1 : forall a b c,  a - b - c >= 0  -> b <= a -> c <= a -b -> S (a - b -c) = S a - b - c.
Proof.
  (* minus_Sn_m: forall n m : nat, m <= n -> S (n - m) = S n - m *)
  intros.
  rewrite minus_Sn_m; auto.
  assert (Hrew:  S (a - b) = S a - b);
  [rewrite minus_Sn_m | rewrite Hrew]; auto.
Qed.

Lemma nat_decomp2 : forall n, n= 0 \/ n = 1 \/ exists m,  n = S (S m).
Proof.
  intro n.
  destruct n.
   *left ; reflexivity.
   * destruct n.
    + right ; left ; reflexivity.
    +  right ; right ; now exists n.
Qed.                    
  
  Lemma in_tl{A:Type} : forall (l : list A) e,  In e (tl l) -> In e l.
  Proof.  
    intros l  e Hin.
    destruct l; [inversion Hin | ].
    constructor 2 ; auto.
  Qed.

  Lemma in_hd_or_tl{A:Type} : forall x (l: list A),
      In x l -> hd_error l = Some x \/ In x (tl l).
  Proof.
    destruct l; intros Hin ; inversion Hin; subst.
    * left; auto.
    * right ; auto.
  Qed.

  Lemma in_hd_error_some{A: Type} : forall (a:A) l1 l2,
      exists x , hd_error (l1 ++ a :: l2) = Some x.
  Proof.
    intros a l1 l2.
    destruct l1.
    exists a; auto.
    exists a0 ; auto.
  Qed.

  Lemma is_sorted_map{A B : Type} :
  forall (R: A -> A -> bool) (f:B -> A) l,
    is_sorted B  (fun x y => R (f x) (f y))  l ->
    is_sorted A R (map f l).
Proof.
  intros E f l Hsor.
  induction Hsor.
  * constructor.
  * constructor.
  * constructor ; auto.
Qed.



Definition drop_snd{A B C : Type}(t : A * B * C) : A * C :=
  match t with (a, b, c) => (a,c) end.

Lemma snd_drop_snd{A B C : Type}(t : A * B * C):  snd t = snd (drop_snd t).
destruct t as ((a & b) & c) ; auto.
Qed.

  
Lemma NoDup_tl{A: Type} : forall (l : list A), NoDup l -> NoDup (tl l).
Proof.
  intros l Hno.
  destruct l.
  * apply NoDup_nil.
  *  cbn.
     rewrite NoDup_cons_iff in Hno.
     destruct Hno ; auto.
Qed.


Lemma map_tl{A B : Type} : forall (f : A -> B) l,
    map f (tl l) = tl (map f l).
Proof.
induction l ; auto.  
Qed.

Lemma map_hd{A B : Type} : forall (f : A -> B) l b,
     hd_error (map f l) = Some b -> exists a,  f a = b /\ hd_error  l = Some a.
Proof.
intros f l b Hh.  
destruct l ; inversion Hh ; subst.
now exists a.
Qed.

Lemma hd_in{A : Type} : forall l (e : A), hd_error l = Some e -> In e l.
Proof.
intros l e Hh.  
destruct l ; inversion Hh ; subst.
constructor ; auto.
Qed.


End Misc.

