(** * Gödel's β-function

    Any finite sequence of naturals is coded by two numbers:
    [beta_exists] gives [a] and [b] with
    [a mod (1 + (j+1)·b) = l_j] for every position [j]. This is what
    lets a first-order formula quantify over finite sequences of states
    ([Equivalence.Godel]).

    The proof takes [b = m!] with [m] at least the length and every
    element. The moduli [1 + (j+1)·b] are then pairwise coprime and
    exceed every element, and the Chinese remainder theorem of the
    standard library ([Z.combinecong_sound_coprime], [Stdlib.ZArith.Zcong])
    solves the congruences, one modulus at a time. Constructive. *)

From Stdlib Require Import ZArith Arith Lia Znumtheory Zcong Factorial List.
Import ListNotations.

Local Open Scope Z_scope.

Section Moduli.

Variable B : Z.
Hypothesis Bpos : 0 < B.

Definition dm (j : nat) : Z := 1 + (Z.of_nat j + 1) * B.

Lemma dm_pos : forall j, 0 < dm j.
Proof. intros j. unfold dm. nia. Qed.

Lemma dm_coprime_B : forall j, Z.coprime (dm j) B.
Proof.
  intros j. unfold Z.coprime, dm.
  rewrite Z.gcd_comm, Z.gcd_add_mult_diag_r, Z.gcd_1_r.
  reflexivity.
Qed.

Lemma divide_coprime : forall g x, (g | x) -> Z.coprime x B -> Z.coprime g B.
Proof.
  intros g x [k ->] H. apply Z.Bezout_coprime in H.
  destruct H as [u [v E]]. apply Z.coprime_Bezout.
  exists (u * k), v. rewrite <- E. ring.
Qed.

(** Two moduli at distance at most [m] are coprime, when [b] is a
    multiple of every number up to [m]. *)
Lemma dm_coprime : forall i j,
    (i < j)%nat -> (Z.of_nat (j - i) | B) -> Z.coprime (dm i) (dm j).
Proof.
  intros i j Hij Hdiv. unfold Z.coprime.
  set (g := Z.gcd (dm i) (dm j)).
  assert (Gi : (g | dm i)) by apply Z.gcd_divide_l.
  assert (Gj : (g | dm j)) by apply Z.gcd_divide_r.
  assert (Gd : (g | B * Z.of_nat (j - i))).
  { replace (B * Z.of_nat (j - i)) with (dm j - dm i)
      by (unfold dm; rewrite Nat2Z.inj_sub by lia; ring).
    apply Z.divide_sub_r; assumption. }
  assert (GB : Z.coprime g B)
    by exact (divide_coprime g (dm i) Gi (dm_coprime_B i)).
  apply Z.gauss in Gd; [| exact GB].
  assert (G1 : (g | B)) by (eapply Z.divide_trans; eassumption).
  assert (G2 : (g | 1)).
  { replace 1 with (dm i - (Z.of_nat i + 1) * B) by (unfold dm; ring).
    apply Z.divide_sub_r; [exact Gi | apply Z.divide_mul_r, G1]. }
  apply Z.divide_1_r_nonneg in G2; [exact G2 | apply Z.gcd_nonneg].
Qed.

Fixpoint prodd (n : nat) : Z :=
  match n with O => 1 | S n => prodd n * dm n end.

Lemma prodd_pos : forall n, 0 < prodd n.
Proof. induction n; simpl; [lia | pose proof (dm_pos n); nia]. Qed.

Lemma dm_divides_prodd : forall i n, (i < n)%nat -> (dm i | prodd n).
Proof.
  intros i n. induction n as [| n IH]; intros H; [lia |]. simpl.
  destruct (Nat.eq_dec i n) as [-> | Hne].
  - apply Z.divide_mul_r, Z.divide_refl.
  - apply Z.divide_mul_l, IH. lia.
Qed.

Lemma prodd_coprime : forall k n,
    (forall i, (i < k)%nat -> Z.coprime (dm i) (dm n)) ->
    Z.coprime (prodd k) (dm n).
Proof.
  induction k as [| k IH]; intros n H; simpl.
  - apply Z.coprime_1_l.
  - apply Z.coprime_mul_l; [apply IH; intros i Hi; apply H; lia
                           | apply H; lia].
Qed.

(** The Chinese remainder theorem, for the first [n] moduli. *)
Lemma crt : forall n (r : nat -> Z),
    (forall i j, (i < j < n)%nat -> Z.coprime (dm i) (dm j)) ->
    exists x, forall i, (i < n)%nat -> x mod dm i = r i mod dm i.
Proof.
  induction n as [| n IH]; intros r Hc.
  - exists 0. intros i Hi. lia.
  - destruct (IH r (fun i j H => Hc i j ltac:(lia))) as [x Hx].
    assert (Cop : Z.coprime (prodd n) (dm n)).
    { apply prodd_coprime. intros i Hi. apply Hc. lia. }
    destruct (Z.combinecong_sound_coprime _ _ x (r n) Cop) as [E1 E2].
    exists (Z.combinecong (prodd n) (dm n) x (r n)). intros i Hi.
    destruct (Nat.eq_dec i n) as [-> | Hne]; [exact E2 |].
    assert (D : (dm i | prodd n)) by (apply dm_divides_prodd; lia).
    rewrite <- (Z.mod_mod_divide _ _ _ D), E1, (Z.mod_mod_divide _ _ _ D).
    apply Hx. lia.
Qed.

End Moduli.

Local Close Scope Z_scope.

Lemma le_fact : forall n, n <= fact n.
Proof. induction n; simpl; [lia | pose proof (lt_O_fact n); nia]. Qed.

Lemma divide_fact : forall k m, 0 < k <= m -> Nat.divide k (fact m).
Proof.
  intros k m. induction m as [| m IH]; intros H; [lia |].
  simpl fact. destruct (Nat.eq_dec k (S m)) as [-> | Hne].
  - exists (fact m). lia.
  - destruct (IH ltac:(lia)) as [q Hq]. exists (q + m * q). nia.
Qed.

Theorem beta_exists : forall (l : list nat), exists a b : nat,
    forall j, j < length l -> a mod (1 + (j + 1) * b) = nth j l 0.
Proof.
  intros l. set (m := length l + list_max l).
  set (b := fact m). set (B := Z.of_nat b).
  assert (Bpos : (0 < B)%Z) by (unfold B, b; pose proof (lt_O_fact m); lia).
  assert (Hc : forall i j, i < j < length l -> Z.coprime (dm B i) (dm B j)).
  { intros i j H. apply dm_coprime; [lia |].
    destruct (divide_fact (j - i) m ltac:(unfold m; lia)) as [q Hq].
    exists (Z.of_nat q). unfold B, b. rewrite Hq, Nat2Z.inj_mul. reflexivity. }
  destruct (crt B (length l) (fun i => Z.of_nat (nth i l 0)) Hc) as [x Hx].
  set (P := prodd B (length l)).
  assert (Ppos : (0 < P)%Z) by apply prodd_pos, Bpos.
  exists (Z.to_nat (x mod P)), b. intros j Hj.
  assert (Hlt : nth j l 0 < 1 + (j + 1) * b).
  { assert (nth j l 0 <= list_max l).
    { pose proof (proj1 (list_max_le l (list_max l)) (Nat.le_refl _)) as F.
      rewrite Forall_forall in F. apply F, nth_In, Hj. }
    pose proof (le_fact m). unfold b, m in *. nia. }
  apply Nat2Z.inj. rewrite Nat2Z.inj_mod.
  rewrite Z2Nat.id by (apply Z.mod_pos_bound, Ppos).
  replace (Z.of_nat (1 + (j + 1) * b)) with (dm B j) by (unfold dm, B; lia).
  assert (D : (dm B j | P)%Z) by (apply dm_divides_prodd, Hj).
  rewrite (Z.mod_mod_divide _ _ _ D), (Hx j Hj).
  apply Z.mod_small. unfold dm, B. lia.
Qed.
