Require Import Lia List.

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
