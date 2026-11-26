(** * Expressiveness: weakest preconditions of loops are first-order

    [Equivalence.Cook] proves Hoare logic over syntactic formulas
    complete relative to expressiveness of loops. This file discharges
    that assumption for a first-order arithmetic assertion language
    ([gf]): every weakest liberal precondition of every Imp program, for
    every postcondition, is a formula ([wlp_expressible]). So Hoare logic
    over these formulas is complete for Imp outright ([fa_complete]):
    Cook's theorem with no expressiveness hypothesis.

    The assertion language has, besides Imp's own expressions and tests,
    *logical* variables, numbered, with [+] and [×] and their own
    quantifiers, as in Winskel's assertion language. Fresh logical
    variables are just larger numbers, so no renaming is ever needed.

    - [Rel c yb fr]: a formula saying that [c] takes the current state
      to the state whose written variables ([wvars]) hold the logical
      variables [yb, yb+1, …] ([rel_correct]); the variables [fr, …]
      are free for its own quantifiers.
    - Loops: a run of a loop is a finite sequence of states; the history
      of each written variable is coded by two numbers through Gödel's
      β-function ([Equivalence.Beta]).
    - [Wlp c φ]: for all values of the written variables, if [c] can
      reach them, [φ] holds there.

    Final states are compared as functions, so the proofs use
    [functional_extensionality]. *)

From Stdlib Require Import String List Arith Lia Bool FunctionalExtensionality.
From LogicTransformers.Imp Require Import Syntax BigStep Hoare.
From LogicTransformers.Equivalence Require Import Beta Cook.
Import ListNotations.

(** ** The assertion language *)

Inductive term : Type :=
  | TN (n : nat)
  | TL (k : nat)              (* a logical variable *)
  | TA (a : aexp)             (* an Imp expression, over the state *)
  | TP (t1 t2 : term)
  | TM (t1 t2 : term).

Fixpoint teval (s : state) (r : nat -> nat) (t : term) : nat :=
  match t with
  | TN n => n
  | TL k => r k
  | TA a => aeval s a
  | TP t1 t2 => teval s r t1 + teval s r t2
  | TM t1 t2 => teval s r t1 * teval s r t2
  end.

Inductive gf : Type :=
  | GEq (t1 t2 : term)
  | GLe (t1 t2 : term)
  | GB (b : bexp)
  | GNot (f : gf)
  | GAnd (f g : gf)
  | GOr (f g : gf)
  | GImp (f g : gf)
  | GAllL (k : nat) (f : gf)
  | GExL (k : nat) (f : gf)
  | GAll (x : var) (f : gf)
  | GSub (x : var) (a : aexp) (f : gf)
  | GSubL (x : var) (k : nat) (f : gf).

Definition upd (r : nat -> nat) (k v : nat) : nat -> nat :=
  fun j => if Nat.eqb j k then v else r j.

Fixpoint fd (f : gf) (s : state) (r : nat -> nat) : Prop :=
  match f with
  | GEq t1 t2 => teval s r t1 = teval s r t2
  | GLe t1 t2 => teval s r t1 <= teval s r t2
  | GB b => bassn b s
  | GNot f => ~ fd f s r
  | GAnd f g => fd f s r /\ fd g s r
  | GOr f g => fd f s r \/ fd g s r
  | GImp f g => fd f s r -> fd g s r
  | GAllL k f => forall v, fd f s (upd r k v)
  | GExL k f => exists v, fd f s (upd r k v)
  | GAll x f => forall n, fd f (update s x n) r
  | GSub x a f => fd f (update s x (aeval s a)) r
  | GSubL x k f => fd f (update s x (r k)) r
  end.

Definition GTrue : gf := GEq (TN 0) (TN 0).

(** ** Extensionality *)

Lemma aeval_ext : forall a s s', (forall x, s x = s' x) ->
    aeval s a = aeval s' a.
Proof. induction a; intros s s' E; simpl; auto. Qed.

Lemma beval_ext : forall b s s', (forall x, s x = s' x) ->
    beval s b = beval s' b.
Proof.
  induction b; intros s s' E; simpl;
    try rewrite (aeval_ext a1 s s' E), (aeval_ext a2 s s' E); auto;
    try rewrite (IHb s s' E); try rewrite (IHb1 s s' E), (IHb2 s s' E); auto.
Qed.

Lemma update_ext : forall s s' x v, (forall y, s y = s' y) ->
    forall y, update s x v y = update s' x v y.
Proof. intros. unfold update. destruct (String.eqb x y); auto. Qed.

Lemma upd_ext : forall r r' k v, (forall j, r j = r' j) ->
    forall j, upd r k v j = upd r' k v j.
Proof. intros. unfold upd. destruct (Nat.eqb j k); auto. Qed.

Lemma teval_ext : forall t s s' r r', (forall x, s x = s' x) ->
    (forall k, r k = r' k) -> teval s r t = teval s' r' t.
Proof.
  induction t; intros s s' r r' E F; simpl; auto using aeval_ext;
    rewrite (IHt1 s s' r r' E F), (IHt2 s s' r r' E F); reflexivity.
Qed.

Lemma fd_ext : forall f s s' r r', (forall x, s x = s' x) ->
    (forall k, r k = r' k) -> (fd f s r <-> fd f s' r').
Proof.
  induction f; intros s s' r r' E F; simpl.
  - rewrite (teval_ext t1 s s' r r' E F), (teval_ext t2 s s' r r' E F).
    reflexivity.
  - rewrite (teval_ext t1 s s' r r' E F), (teval_ext t2 s s' r r' E F).
    reflexivity.
  - unfold bassn. rewrite (beval_ext b s s' E). reflexivity.
  - rewrite (IHf s s' r r' E F). reflexivity.
  - rewrite (IHf1 s s' r r' E F), (IHf2 s s' r r' E F). reflexivity.
  - rewrite (IHf1 s s' r r' E F), (IHf2 s s' r r' E F). reflexivity.
  - rewrite (IHf1 s s' r r' E F), (IHf2 s s' r r' E F). reflexivity.
  - split; intros H v; [rewrite <- (IHf s s' _ _ E (upd_ext r r' k v F))
                        | rewrite (IHf s s' _ _ E (upd_ext r r' k v F))];
      apply H.
  - split; intros [v H]; exists v;
      [rewrite <- (IHf s s' _ _ E (upd_ext r r' k v F))
      | rewrite (IHf s s' _ _ E (upd_ext r r' k v F))]; exact H.
  - split; intros H n; [rewrite <- (IHf _ _ r r' (update_ext s s' x n E) F)
                        | rewrite (IHf _ _ r r' (update_ext s s' x n E) F)];
      apply H.
  - rewrite (aeval_ext a s s' E). apply IHf; [apply update_ext, E | exact F].
  - rewrite (F k). apply IHf; [apply update_ext, E | exact F].
Qed.

(** Which logical variables a formula can see. *)
Fixpoint tlv (t : term) : nat :=
  match t with
  | TN _ | TA _ => 0
  | TL k => S k
  | TP t1 t2 | TM t1 t2 => Nat.max (tlv t1) (tlv t2)
  end.

Fixpoint flv (f : gf) : nat :=
  match f with
  | GEq t1 t2 | GLe t1 t2 => Nat.max (tlv t1) (tlv t2)
  | GB _ => 0
  | GNot f | GAll _ f | GSub _ _ f => flv f
  | GAnd f g | GOr f g | GImp f g => Nat.max (flv f) (flv g)
  | GAllL k f | GExL k f => Nat.max (S k) (flv f)
  | GSubL _ k f => Nat.max (S k) (flv f)
  end.

Lemma teval_irr : forall t s r r', (forall k, k < tlv t -> r k = r' k) ->
    teval s r t = teval s r' t.
Proof.
  induction t; intros s r r' H; cbn [teval tlv] in *; auto.
  - rewrite (IHt1 s r r'), (IHt2 s r r'); auto; intros; apply H; lia.
  - rewrite (IHt1 s r r'), (IHt2 s r r'); auto; intros; apply H; lia.
Qed.

Lemma fd_irr : forall f s r r', (forall k, k < flv f -> r k = r' k) ->
    (fd f s r <-> fd f s r').
Proof.
  induction f; intros s r r' H; cbn [fd flv] in *.
  - rewrite (teval_irr t1 s r r'), (teval_irr t2 s r r');
      [reflexivity | |]; intros; apply H; lia.
  - rewrite (teval_irr t1 s r r'), (teval_irr t2 s r r');
      [reflexivity | |]; intros; apply H; lia.
  - reflexivity.
  - rewrite (IHf s r r' H). reflexivity.
  - rewrite (IHf1 s r r'), (IHf2 s r r'); [reflexivity | |];
      intros; apply H; lia.
  - rewrite (IHf1 s r r'), (IHf2 s r r'); [reflexivity | |];
      intros; apply H; lia.
  - rewrite (IHf1 s r r'), (IHf2 s r r'); [reflexivity | |];
      intros; apply H; lia.
  - assert (G : forall v j, j < flv f -> upd r k v j = upd r' k v j).
    { intros v j Hj. unfold upd. destruct (Nat.eqb j k); auto. apply H. lia. }
    split; intros K v;
      [rewrite <- (IHf s _ _ (G v)) | rewrite (IHf s _ _ (G v))];
      apply K.
  - assert (G : forall v j, j < flv f -> upd r k v j = upd r' k v j).
    { intros v j Hj. unfold upd. destruct (Nat.eqb j k); auto. apply H. lia. }
    split; intros [v K]; exists v;
      [rewrite <- (IHf s _ _ (G v)) | rewrite (IHf s _ _ (G v))]; exact K.
  - split; intros K n; [rewrite <- (IHf _ r r' H) | rewrite (IHf _ r r' H)];
      apply K.
  - apply IHf, H.
  - rewrite (H k) by lia. apply IHf. intros; apply H; lia.
Qed.

(** ** Blocks of logical variables *)

Definition setb (r : nat -> nat) (fr n : nat) (g : nat -> nat) : nat -> nat :=
  fun k => if (fr <=? k) && (k <? fr + n) then g (k - fr) else r k.

Lemma setb_in : forall r fr n g k, fr <= k < fr + n ->
    setb r fr n g k = g (k - fr).
Proof.
  intros. unfold setb. destruct (Nat.leb_spec fr k), (Nat.ltb_spec k (fr + n));
    simpl; auto; lia.
Qed.

Lemma setb_out : forall r fr n g k, ~ (fr <= k < fr + n) ->
    setb r fr n g k = r k.
Proof.
  intros. unfold setb. destruct (Nat.leb_spec fr k), (Nat.ltb_spec k (fr + n));
    simpl; auto; lia.
Qed.

Lemma upd_eq : forall r k v, upd r k v k = v.
Proof. intros. unfold upd. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_ne : forall r k v j, j <> k -> upd r k v j = r j.
Proof.
  intros. unfold upd. destruct (Nat.eqb_spec j k); [lia | reflexivity].
Qed.

Fixpoint exB (fr n : nat) (f : gf) : gf :=
  match n with O => f | S n => GExL fr (exB (S fr) n f) end.

Fixpoint allB (fr n : nat) (f : gf) : gf :=
  match n with O => f | S n => GAllL fr (allB (S fr) n f) end.

Lemma setb_cons : forall r fr n v g k,
    setb (upd r fr v) (S fr) n g k =
    setb r fr (S n) (fun i => match i with 0 => v | S i => g i end) k.
Proof.
  intros. unfold setb, upd.
  destruct (Nat.leb_spec (S fr) k), (Nat.ltb_spec k (S fr + n)),
           (Nat.leb_spec fr k), (Nat.ltb_spec k (fr + S n)),
           (Nat.eqb_spec k fr); simpl; try lia; auto.
  - replace (k - fr) with (S (k - S fr)) by lia. reflexivity.
  - subst. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma exB_iff : forall n fr f s r,
    fd (exB fr n f) s r <-> exists g, fd f s (setb r fr n g).
Proof.
  induction n as [| n IH]; intros fr f s r; simpl.
  - split; [intros H; exists (fun _ => 0) | intros [g H]];
      (eapply fd_ext; [| | exact H]; [reflexivity |]);
      intros k; unfold setb; destruct (_ && _) eqn:E; auto;
      apply andb_true_iff in E; destruct E as [E1 E2];
      apply Nat.leb_le in E1; apply Nat.ltb_lt in E2; lia.
  - split.
    + intros [v H]. apply IH in H. destruct H as [g H].
      exists (fun i => match i with 0 => v | S i => g i end).
      eapply fd_ext; [| | exact H]; [reflexivity |]. intros k.
      symmetry. apply setb_cons.
    + intros [g H]. exists (g 0). apply IH. exists (fun i => g (S i)).
      eapply fd_ext; [| | exact H]; [reflexivity |]. intros k.
      rewrite setb_cons. unfold setb.
      destruct (_ && _); [destruct (k - fr) |]; reflexivity.
Qed.

Lemma allB_iff : forall n fr f s r,
    fd (allB fr n f) s r <-> forall g, fd f s (setb r fr n g).
Proof.
  induction n as [| n IH]; intros fr f s r; simpl.
  - split; [intros H g | intros H; specialize (H (fun _ => 0))];
      (eapply fd_ext; [| | exact H]; [reflexivity |]);
      intros k; unfold setb; destruct (_ && _) eqn:E; auto;
      apply andb_true_iff in E; destruct E as [E1 E2];
      apply Nat.leb_le in E1; apply Nat.ltb_lt in E2; lia.
  - split.
    + intros H g. specialize (H (g 0)).
      apply IH with (g := fun i => g (S i)) in H.
      eapply fd_ext; [| | exact H]; [reflexivity |]. intros k.
      rewrite setb_cons. unfold setb.
      destruct (_ && _); [destruct (k - fr) |]; reflexivity.
    + intros H v. apply IH. intros g.
      specialize (H (fun i => match i with 0 => v | S i => g i end)).
      eapply fd_ext; [| | exact H]; [reflexivity |]. intros k.
      apply setb_cons.
Qed.

(** ** Written variables, and the frame *)

Fixpoint wvars (c : com) : list var :=
  match c with
  | CSkip => []
  | CAsgn x _ | CHavoc x => [x]
  | CSeq c1 c2 | CIf _ c1 c2 | CChoice c1 c2 => wvars c1 ++ wvars c2
  | CWhile _ c => wvars c
  end.

Lemma frame : forall c s s', ceval c s s' ->
    forall x, ~ In x (wvars c) -> s' x = s x.
Proof.
  intros c s s' H. induction H; intros y Hy; simpl in *;
    try (rewrite in_app_iff in Hy); auto.
  - apply update_neq. intros ->. apply Hy. left. reflexivity.
  - rewrite IHceval2, IHceval1; auto.
  - rewrite IHceval2, IHceval1; auto.
  - apply update_neq. intros ->. apply Hy. left. reflexivity.
Qed.

Lemma ceval_ext : forall c s1 s2 t1 t2, (forall x, s1 x = s2 x) ->
    (forall x, t1 x = t2 x) -> ceval c s1 t1 -> ceval c s2 t2.
Proof.
  intros c s1 s2 t1 t2 E F H.
  replace s2 with s1 by (apply functional_extensionality, E).
  replace t2 with t1 by (apply functional_extensionality, F). exact H.
Qed.

(** ** Loops as finite traces *)

Lemma trace_while : forall b c k (σ : nat -> state),
    (forall j, j < k -> bassn b (σ j) /\ ceval c (σ j) (σ (S j))) ->
    ~ bassn b (σ k) -> ceval (CWhile b c) (σ 0) (σ k).
Proof.
  intros b c k. induction k as [| k IH]; intros σ Hs Hn.
  - apply E_WhileFalse, bassn_false, Hn.
  - destruct (Hs 0 ltac:(lia)) as [Hb Hc].
    eapply E_WhileTrue; [exact Hb | exact Hc |].
    apply (IH (fun j => σ (S j))); [| exact Hn].
    intros j Hj. apply Hs. lia.
Qed.

Lemma while_trace : forall b c s s',
    ceval (CWhile b c) s s' <->
    exists k (σ : nat -> state), σ 0 = s /\
      (forall j, j < k -> bassn b (σ j) /\ ceval c (σ j) (σ (S j))) /\
      σ k = s' /\ ~ bassn b s'.
Proof.
  intros b c s s'. split.
  - intros H. remember (CWhile b c) as w eqn:Ew.
    induction H; inversion Ew; subst.
    + exists 0, (fun _ => st). split; [reflexivity |].
      split; [intros; lia |]. split; [reflexivity | apply bassn_false'; auto].
    + destruct (IHceval2 eq_refl) as [k [σ [E0 [Hs [Ek Hn]]]]].
      exists (S k), (fun j => match j with 0 => st | S j => σ j end).
      split; [reflexivity |]. split; [| split; [exact Ek | exact Hn]].
      intros [| j] Hj.
      * rewrite E0. split; assumption.
      * apply Hs. lia.
  - intros [k [σ [E0 [Hs [Ek Hn]]]]]. subst.
    apply trace_while; [exact Hs | exact Hn].
Qed.

(** ** Positions in a list of variables *)

Fixpoint idx (V : list var) (x : var) : option nat :=
  match V with
  | [] => None
  | y :: V => if String.eqb y x then Some 0 else option_map S (idx V x)
  end.

Lemma idx_some : forall V x i, idx V x = Some i ->
    i < length V /\ nth i V ""%string = x.
Proof.
  induction V as [| y V IH]; intros x i H; simpl in H; [discriminate |].
  destruct (String.eqb_spec y x).
  - injection H; intros; subst. simpl. split; [lia | reflexivity].
  - destruct (idx V x) as [i' |] eqn:E; simpl in H; [| discriminate].
    injection H; intros; subst. destruct (IH x i' E). simpl.
    split; [lia | auto].
Qed.

Lemma idx_none : forall V x, ~ In x V -> idx V x = None.
Proof.
  induction V as [| y V IH]; intros x H; simpl; [reflexivity |].
  destruct (String.eqb_spec y x); [subst; exfalso; apply H; left; auto |].
  rewrite IH; [reflexivity | intros K; apply H; right; exact K].
Qed.

Lemma idx_nth : forall V i, NoDup V -> i < length V ->
    idx V (nth i V ""%string) = Some i.
Proof.
  induction V as [| y V IH]; intros i ND H; simpl in *; [lia |].
  inversion ND; subst. destruct i as [| i].
  - rewrite String.eqb_refl. reflexivity.
  - destruct (String.eqb_spec y (nth i V ""%string)).
    + exfalso. apply H2. rewrite e. apply nth_In. lia.
    + rewrite IH by (auto; lia). reflexivity.
Qed.

Definition post (V : list var) (s : state) (r : nat -> nat) (yb : nat)
  : state :=
  fun x => match idx V x with Some i => r (yb + i) | None => s x end.

Section Vars.

Variable V : list var.
Hypothesis NDV : NoDup V.

Local Notation n := (length V).
Local Notation xv i := (nth i V ""%string).

Lemma post_nth : forall s r yb i, i < n -> post V s r yb (xv i) = r (yb + i).
Proof. intros. unfold post. rewrite idx_nth; auto. Qed.

Lemma post_out : forall s r yb x, ~ In x V -> post V s r yb x = s x.
Proof. intros. unfold post. rewrite idx_none; auto. Qed.

Lemma post_from : forall s r yb (t : state),
    (forall i, i < n -> r (yb + i) = t (xv i)) ->
    (forall x, ~ In x V -> s x = t x) ->
    forall x, post V s r yb x = t x.
Proof.
  intros s r yb t Hin Hout x. unfold post.
  destruct (idx V x) as [i |] eqn:E.
  - destruct (idx_some V x i E) as [Hi Hx]. rewrite <- Hx. apply Hin, Hi.
  - apply Hout. intros K. destruct (In_nth V x ""%string K) as [i [Hi Hx]].
    rewrite <- Hx, idx_nth in E by auto. discriminate.
Qed.

Lemma post_post : forall s r1 b1 r2 b2 x,
    post V (post V s r1 b1) r2 b2 x = post V s r2 b2 x.
Proof.
  intros. unfold post. destruct (idx V x); reflexivity.
Qed.

Lemma post_agree : forall s r r' yb,
    (forall i, i < n -> r (yb + i) = r' (yb + i)) ->
    forall x, post V s r yb x = post V s r' yb x.
Proof.
  intros s r r' yb H x. unfold post. destruct (idx V x) as [i |] eqn:E;
    [apply H, (idx_some V x i E) | reflexivity].
Qed.

(** ** Substituting a block of logical variables for the variables *)

Fixpoint substB (W : list var) (yb : nat) (f : gf) : gf :=
  match W with
  | [] => f
  | x :: W => GSubL x yb (substB W (S yb) f)
  end.

Lemma substB_iff_gen : forall W yb f s r, NoDup W ->
    fd (substB W yb f) s r <-> fd f (post W s r yb) r.
Proof.
  induction W as [| x W IH]; intros yb f s r ND; simpl.
  - apply fd_ext; [| reflexivity]. intros y. reflexivity.
  - inversion ND; subst. rewrite IH by assumption.
    apply fd_ext; [| reflexivity]. intros y. unfold post. simpl.
    destruct (String.eqb_spec x y).
    + subst. rewrite idx_none by assumption. rewrite update_eq.
      simpl. f_equal. lia.
    + destruct (idx W y) as [i |]; simpl.
      * f_equal. lia.
      * apply update_neq. assumption.
Qed.

Lemma substB_iff : forall yb f s r,
    fd (substB V yb f) s r <-> fd f (post V s r yb) r.
Proof. intros. apply substB_iff_gen, NDV. Qed.

(** ** A block of equations, one per variable *)

Fixpoint eqsB (W : list var) (yb : nat) (g : var -> option aexp) : gf :=
  match W with
  | [] => GTrue
  | x :: W =>
      GAnd (match g x with Some a => GEq (TL yb) (TA a) | None => GTrue end)
           (eqsB W (S yb) g)
  end.

Lemma eqsB_iff_gen : forall W yb g s r, NoDup W ->
    fd (eqsB W yb g) s r <->
    forall x a, In x W -> g x = Some a -> post W s r yb x = aeval s a.
Proof.
  induction W as [| x W IH]; intros yb g s r ND; simpl.
  - split; [intros _ y a [] | intros _; reflexivity].
  - inversion ND; subst. rewrite IH by assumption. split.
    + intros [Hh Ht] y a [-> | Hy] Hg.
      * unfold post. simpl. rewrite String.eqb_refl. rewrite Hg in Hh.
        simpl in Hh. rewrite Nat.add_0_r. exact Hh.
      * rewrite <- (Ht y a Hy Hg). unfold post. simpl.
        destruct (String.eqb_spec x y); [subst; contradiction |].
        destruct (idx W y); simpl; [f_equal; lia | reflexivity].
    + intros H. split.
      * destruct (g x) as [a |] eqn:Hg; [| reflexivity]. simpl.
        rewrite <- (H x a (or_introl eq_refl) Hg). unfold post. simpl.
        rewrite String.eqb_refl. f_equal. lia.
      * intros y a Hy Hg. rewrite <- (H y a (or_intror Hy) Hg). unfold post.
        simpl. destruct (String.eqb_spec x y); [subst; contradiction |].
        destruct (idx W y); simpl; [f_equal; lia | reflexivity].
Qed.

Lemma eqsB_iff : forall yb g s r,
    fd (eqsB V yb g) s r <->
    forall x a, In x V -> g x = Some a -> post V s r yb x = aeval s a.
Proof. intros. apply eqsB_iff_gen, NDV. Qed.

End Vars.

(** ** Finite conjunctions, the β-formula, finite choice *)

Fixpoint bigAnd (f : nat -> gf) (n : nat) : gf :=
  match n with O => GTrue | S n => GAnd (bigAnd f n) (f n) end.

Lemma bigAnd_iff : forall f n s r,
    fd (bigAnd f n) s r <-> forall i, i < n -> fd (f i) s r.
Proof.
  intros f n s r. induction n as [| n IH]; simpl.
  - split; [intros _ i Hi; lia | intros _; reflexivity].
  - rewrite IH. split.
    + intros [H1 H2] i Hi. destruct (Nat.eq_dec i n) as [-> | Hne];
        [exact H2 | apply H1; lia].
    + intros H. split; [intros i Hi; apply H; lia | apply H; lia].
Qed.

Definition dterm (tj tb : term) : term := TP (TN 1) (TM (TP tj (TN 1)) tb).

(** [tv] is the [tj]-th element of the sequence coded by [ta], [tb]. *)
Definition betaF (ta tb tj tv : term) (q : nat) : gf :=
  GExL q (GAnd (GEq ta (TP (TM (TL q) (dterm tj tb)) tv))
               (GLe (TP tv (TN 1)) (dterm tj tb))).

Lemma betaF_iff : forall ta tb tj tv q s r,
    tlv ta <= q -> tlv tb <= q -> tlv tj <= q -> tlv tv <= q ->
    fd (betaF ta tb tj tv q) s r <->
    teval s r tv = teval s r ta mod (1 + (teval s r tj + 1) * teval s r tb).
Proof.
  intros ta tb tj tv q s r Ha Hb Hj Hv. unfold betaF. cbn [fd].
  assert (I : forall t v, tlv t <= q -> teval s (upd r q v) t = teval s r t).
  { intros t v Ht. apply teval_irr. intros k Hk. apply upd_ne. lia. }
  split.
  - intros [v [E L]]. unfold dterm in *. cbn [fd teval] in E, L.
    rewrite upd_eq in E. rewrite !I in E, L by assumption.
    rewrite (I tv v Hv) in E.
    apply (Nat.mod_unique _ (1 + (teval s r tj + 1) * teval s r tb) v); lia.
  - intros E. exists (teval s r ta / (1 + (teval s r tj + 1) * teval s r tb)).
    unfold dterm. cbn [fd teval]. rewrite upd_eq, !I by assumption. rewrite E.
    set (d := 1 + (teval s r tj + 1) * teval s r tb).
    assert (Hd : d <> 0) by (unfold d; lia).
    pose proof (Nat.div_mod_eq (teval s r ta) d).
    pose proof (Nat.mod_upper_bound (teval s r ta) d Hd). unfold d in *. lia.
Qed.

Lemma choice2 : forall n (P : nat -> nat -> nat -> Prop),
    (forall i, i < n -> exists a b, P i a b) ->
    exists ga gb : nat -> nat, forall i, i < n -> P i (ga i) (gb i).
Proof.
  induction n as [| n IH]; intros P H.
  - exists (fun _ => 0), (fun _ => 0). intros i Hi. lia.
  - destruct (IH P (fun i Hi => H i ltac:(lia))) as [ga [gb Hg]].
    destruct (H n ltac:(lia)) as [a [b Hab]].
    exists (fun i => if Nat.eqb i n then a else ga i),
           (fun i => if Nat.eqb i n then b else gb i).
    intros i Hi.
    destruct (Nat.eqb_spec i n); [subst; exact Hab | apply Hg; lia].
Qed.

Lemma beta_fun : forall (vals : nat -> nat) k, exists a b,
    forall j, j <= k -> a mod (1 + (j + 1) * b) = vals j.
Proof.
  intros vals k. destruct (beta_exists (map vals (seq 0 (S k)))) as [a [b H]].
  exists a, b. intros j Hj. rewrite H by (rewrite length_map, length_seq; lia).
  rewrite (nth_indep _ 0 (vals 0)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

(** ** Basic commands, as functions of the state *)

Lemma skip_iff : forall s t, ceval CSkip s t <-> forall y, t y = s y.
Proof.
  intros s t. split.
  - intros H. inversion H; subst. reflexivity.
  - intros E. replace t with s by (apply functional_extensionality;
      intros y; symmetry; apply E). apply E_Skip.
Qed.

Lemma asgn_iff : forall x a s t,
    ceval (CAsgn x a) s t <-> forall y, t y = update s x (aeval s a) y.
Proof.
  intros x a s t. split.
  - intros H. inversion H; subst. reflexivity.
  - intros E. replace t with (update s x (aeval s a))
      by (apply functional_extensionality; intros y; symmetry; apply E).
    apply E_Asgn.
Qed.

Lemma havoc_iff : forall x s t,
    ceval (CHavoc x) s t <-> exists v, forall y, t y = update s x v y.
Proof.
  intros x s t. split.
  - intros H. inversion H; subst. exists n. reflexivity.
  - intros [v E]. replace t with (update s x v)
      by (apply functional_extensionality; intros y; symmetry; apply E).
    apply E_Havoc.
Qed.

(** ** The relation of a program, as a formula *)

Section Rel.

Variable V : list var.
Hypothesis NDV : NoDup V.

Local Notation n := (length V).
Local Notation xv i := (nth i V ""%string).

Definition seqF (R1 R2 : gf) (fr : nat) : gf :=
  exB fr n (GAnd R1 (substB V fr R2)).

Fixpoint Rel (c : com) (yb fr : nat) : gf :=
  match c with
  | CSkip => eqsB V yb (fun y => Some (AVar y))
  | CAsgn x a =>
      eqsB V yb (fun y => Some (if String.eqb x y then a else AVar y))
  | CHavoc x =>
      eqsB V yb (fun y => if String.eqb x y then None else Some (AVar y))
  | CSeq c1 c2 => seqF (Rel c1 fr (fr + n)) (Rel c2 yb (fr + n)) fr
  | CIf b c1 c2 =>
      GOr (GAnd (GB b) (Rel c1 yb fr)) (GAnd (GNot (GB b)) (Rel c2 yb fr))
  | CChoice c1 c2 => GOr (Rel c1 yb fr) (Rel c2 yb fr)
  | CWhile b c =>
      let A := fr in let Bk := fr + n in let K := fr + 2 * n in
      let J := S K in let U := S J in let W := U + n in let Q := W + n in
      let code i (tj tv : term) := betaF (TL (A + i)) (TL (Bk + i)) tj tv Q in
      exB A n (exB Bk n (GExL K
        (GAnd (bigAnd (fun i => code i (TN 0) (TA (AVar (xv i)))) n)
        (GAnd (GAllL J (GImp (GLe (TP (TL J) (TN 1)) (TL K))
                 (exB U n (exB W n
                   (GAnd (bigAnd (fun i => code i (TL J) (TL (U + i))) n)
                   (GAnd (bigAnd (fun i => code i (TP (TL J) (TN 1))
                                                   (TL (W + i))) n)
                         (substB V U (GAnd (GB b) (Rel c W (S Q))))))))))
        (GAnd (bigAnd (fun i => code i (TL K) (TL (yb + i))) n)
              (substB V yb (GNot (GB b))))))))
  end.

Lemma incl_app_l : forall {A} (l1 l2 l : list A),
    incl (l1 ++ l2) l -> incl l1 l.
Proof. intros A l1 l2 l H x Hx. apply H, in_or_app. left. exact Hx. Qed.

Lemma incl_app_r : forall {A} (l1 l2 l : list A),
    incl (l1 ++ l2) l -> incl l2 l.
Proof. intros A l1 l2 l H x Hx. apply H, in_or_app. right. exact Hx. Qed.

Lemma post_ext_ceval : forall c s t1 t2, (forall x, t1 x = t2 x) ->
    ceval c s t1 -> ceval c s t2.
Proof. intros. eapply ceval_ext; [| | eassumption]; auto. Qed.

Definition beta (a b j : nat) : nat := a mod (1 + (j + 1) * b).

Lemma post_same : forall s r r' yb yb',
    (forall i, i < n -> r (yb + i) = r' (yb' + i)) ->
    forall x, post V s r yb x = post V s r' yb' x.
Proof.
  intros s r r' yb yb' H x. unfold post.
  destruct (idx V x) as [i |] eqn:E;
    [apply H, (idx_some V x i E) | reflexivity].
Qed.

Ltac subk := repeat match goal with
  |- context [?a + ?i - ?a] => replace (a + i - a) with i by lia end.

Ltac lk := repeat (first [ rewrite upd_eq | rewrite upd_ne by lia
                        | rewrite setb_out by lia | rewrite setb_in by lia ]).

Lemma while_correct : forall b c,
    incl (wvars c) V ->
    (forall yb fr s r, yb + n <= fr ->
       (fd (Rel c yb fr) s r <-> ceval c s (post V s r yb))) ->
    forall yb fr s r, yb + n <= fr ->
    (fd (Rel (CWhile b c) yb fr) s r <-> ceval (CWhile b c) s (post V s r yb)).
Proof.
  intros b c Hinc IH yb fr s r Hle. cbn [Rel].
  set (Q := S (S (fr + 2 * n)) + n + n).
  rewrite exB_iff. setoid_rewrite exB_iff. split.
  - (* a coded run is a run *)
    intros [ga [gb [kv [Hst [Hin [Hfi Hex]]]]]].
    set (r3 := upd (setb (setb r fr n ga) (fr + n) n gb) (fr + 2 * n) kv) in *.
    assert (LA : forall i, i < n -> r3 (fr + i) = ga i)
      by (intros i Hi; unfold r3; lk; f_equal; lia).
    assert (LB : forall i, i < n -> r3 (fr + n + i) = gb i)
      by (intros i Hi; unfold r3; lk; f_equal; lia).
    assert (LY : forall i, i < n -> r3 (yb + i) = r (yb + i))
      by (intros i Hi; unfold r3; lk; reflexivity).
    assert (LK : r3 (fr + 2 * n) = kv) by (unfold r3; lk; reflexivity).
    set (sg := fun j => post V s (fun i => beta (ga i) (gb i) j) 0).
    rewrite bigAnd_iff in Hst, Hfi.
    assert (S0 : forall x, sg 0 x = s x).
    { intros x. unfold sg. apply (post_from V NDV).
      - intros i Hi. specialize (Hst i Hi).
        rewrite betaF_iff in Hst by (cbn [tlv]; lia). cbn [teval] in Hst.
        rewrite LA, LB in Hst by exact Hi.
        cbv beta. rewrite Nat.add_0_l. unfold beta. rewrite <- Hst.
        reflexivity.
      - intros y _. reflexivity. }
    assert (SK : forall x, sg kv x = post V s r yb x).
    { intros x. unfold sg. apply post_same. intros i Hi.
      specialize (Hfi i Hi). rewrite betaF_iff in Hfi by (cbn [tlv]; lia).
      cbn [teval] in Hfi. rewrite LA, LB, LY in Hfi by exact Hi.
      rewrite LK in Hfi. cbv beta. rewrite Nat.add_0_l. unfold beta.
      rewrite <- Hfi.
      reflexivity. }
    assert (Steps : forall j, j < kv ->
              bassn b (sg j) /\ ceval c (sg j) (sg (S j))).
    { intros j Hj. specialize (Hin j). cbn [fd] in Hin.
      assert (Hle1 : teval s (upd r3 (S (fr + 2 * n)) j)
                       (TP (TL (S (fr + 2 * n))) (TN 1))
                     <= teval s (upd r3 (S (fr + 2 * n)) j) (TL (fr + 2 * n))).
      { cbn [teval]. rewrite upd_eq, upd_ne by lia. unfold r3. lk. lia. }
      specialize (Hin Hle1). rewrite exB_iff in Hin. destruct Hin as [gu Hin].
      rewrite exB_iff in Hin. destruct Hin as [gw [HU [HW Hbody]]].
      set (r6 := setb (setb (upd r3 (S (fr + 2 * n)) j)
                       (S (S (fr + 2 * n))) n gu)
                      (S (S (fr + 2 * n)) + n) n gw) in *.
      rewrite bigAnd_iff in HU, HW.
      assert (L6A : forall i, i < n -> r6 (fr + i) = ga i)
        by (intros i Hi; unfold r6; lk; apply LA, Hi).
      assert (L6B : forall i, i < n -> r6 (fr + n + i) = gb i)
        by (intros i Hi; unfold r6; lk; apply LB, Hi).
      assert (L6J : r6 (S (fr + 2 * n)) = j) by (unfold r6; lk; reflexivity).
      assert (EU : forall x, post V s r6 (S (S (fr + 2 * n))) x = sg j x).
      { intros x. unfold sg. apply post_same. intros i Hi.
        specialize (HU i Hi). rewrite betaF_iff in HU by (cbn [tlv]; lia).
        cbn [teval] in HU. rewrite L6A, L6B, L6J in HU by exact Hi.
        cbv beta. rewrite Nat.add_0_l. unfold beta. rewrite <- HU.
        reflexivity. }
      assert (EW : forall x, post V s r6 (S (S (fr + 2 * n)) + n) x
                             = sg (S j) x).
      { intros x. unfold sg. apply post_same. intros i Hi.
        specialize (HW i Hi). rewrite betaF_iff in HW by (cbn [tlv]; lia).
        cbn [teval] in HW. rewrite L6A, L6B, L6J in HW by exact Hi.
        cbv beta. rewrite Nat.add_0_l. unfold beta.
        replace (S j + 1) with (j + 1 + 1) by lia. rewrite <- HW.
        reflexivity. }
      rewrite substB_iff in Hbody by exact NDV. cbn [fd] in Hbody.
      destruct Hbody as [Hb Hc].
      rewrite IH in Hc by lia. split.
      - unfold bassn in *. rewrite <- Hb. symmetry. apply beval_ext, EU.
      - eapply ceval_ext; [| | exact Hc]; [exact EU |].
        intros x. rewrite post_post. apply EW. }
    eapply ceval_ext; [exact S0 | exact SK |].
    apply trace_while; [exact Steps |].
    rewrite substB_iff in Hex by exact NDV. cbn [fd] in Hex.
    unfold bassn in *. intros Hb. apply Hex. rewrite <- Hb. apply beval_ext.
    intros x. rewrite SK. apply post_agree. intros i Hi. apply LY, Hi.
  - (* a run is a coded run *)
    intros H. apply while_trace in H.
    destruct H as [k [sg [E0 [Hs [Ek Hn]]]]].
    assert (Fr : forall j, j <= k -> forall x, ~ In x V -> sg j x = s x).
    { induction j as [| j IHj]; intros Hj x Hx; [subst; reflexivity |].
      rewrite (frame c (sg j) (sg (S j)) (proj2 (Hs j ltac:(lia))) x
                 (fun K => Hx (Hinc x K))).
      apply IHj; [lia | exact Hx]. }
    destruct (choice2 n (fun i a b' => forall j, j <= k ->
                beta a b' j = sg j (xv i)))
      as [ga [gb Hg]].
    { intros i Hi. destruct (beta_fun (fun j => sg j (xv i)) k) as [a [b' H]].
      exists a, b'. exact H. }
    exists ga, gb, k.
    set (r3 := upd (setb (setb r fr n ga) (fr + n) n gb) (fr + 2 * n) k).
    assert (LA : forall i, i < n -> r3 (fr + i) = ga i)
      by (intros i Hi; unfold r3; lk; f_equal; lia).
    assert (LB : forall i, i < n -> r3 (fr + n + i) = gb i)
      by (intros i Hi; unfold r3; lk; f_equal; lia).
    assert (LY : forall i, i < n -> r3 (yb + i) = r (yb + i))
      by (intros i Hi; unfold r3; lk; reflexivity).
    cbn [fd]. split; [| split; [| split]].
    + rewrite bigAnd_iff. intros i Hi.
      rewrite betaF_iff by (cbn [tlv]; lia). cbn [teval].
      rewrite LA, LB by exact Hi.
      pose proof (Hg i Hi 0 ltac:(lia)) as G. unfold beta in G.
      rewrite G, E0. reflexivity.
    + intros j Hj. cbn [teval] in Hj. rewrite upd_eq, upd_ne in Hj by lia.
      assert (LK : r3 (fr + 2 * n) = k) by (unfold r3; lk; reflexivity).
      rewrite LK in Hj.
      rewrite exB_iff. exists (fun i => sg j (xv i)).
      rewrite exB_iff. exists (fun i => sg (S j) (xv i)).
      set (r6 := setb (setb (upd r3 (S (fr + 2 * n)) j)
                       (S (S (fr + 2 * n))) n (fun i => sg j (xv i)))
                      (S (S (fr + 2 * n)) + n) n (fun i => sg (S j) (xv i))).
      assert (L6A : forall i, i < n -> r6 (fr + i) = ga i)
        by (intros i Hi; unfold r6; lk; apply LA, Hi).
      assert (L6B : forall i, i < n -> r6 (fr + n + i) = gb i)
        by (intros i Hi; unfold r6; lk; apply LB, Hi).
      assert (L6J : r6 (S (fr + 2 * n)) = j) by (unfold r6; lk; reflexivity).
      assert (EU : forall x, post V s r6 (S (S (fr + 2 * n))) x = sg j x).
      { apply (post_from V NDV).
        - intros i Hi. unfold r6. lk. subk. reflexivity.
        - intros x Hx. symmetry. apply Fr; [lia | exact Hx]. }
      assert (EW : forall x, post V s r6 (S (S (fr + 2 * n)) + n) x
                             = sg (S j) x).
      { apply (post_from V NDV).
        - intros i Hi. unfold r6. lk. subk. reflexivity.
        - intros x Hx. symmetry. apply Fr; [lia | exact Hx]. }
      cbn [fd]. split; [| split].
      * rewrite bigAnd_iff. intros i Hi.
        rewrite betaF_iff by (cbn [tlv]; lia). cbn [teval].
        rewrite L6A, L6B, L6J by exact Hi. unfold r6. lk.
        pose proof (Hg i Hi j ltac:(lia)) as G. unfold beta in G.
        replace (S (S (fr + 2 * n)) + i - S (S (fr + 2 * n))) with i by lia.
        rewrite G. reflexivity.
      * rewrite bigAnd_iff. intros i Hi.
        rewrite betaF_iff by (cbn [tlv]; lia). cbn [teval].
        rewrite L6A, L6B, L6J by exact Hi. unfold r6. lk.
        pose proof (Hg i Hi (S j) ltac:(lia)) as G. unfold beta in G.
        replace (S (S (fr + 2 * n)) + n + i - (S (S (fr + 2 * n)) + n))
          with i by lia.
        rewrite <- G. f_equal. f_equal. lia.
      * rewrite substB_iff by exact NDV. cbn [fd].
        destruct (Hs j ltac:(lia)) as [Hb Hc]. split.
        -- unfold bassn in *. rewrite <- Hb. apply beval_ext, EU.
        -- rewrite IH by lia. eapply ceval_ext; [| | exact Hc].
           ++ intros x. symmetry. apply EU.
           ++ intros x. rewrite post_post. symmetry. apply EW.
    + rewrite bigAnd_iff. intros i Hi.
      rewrite betaF_iff by (cbn [tlv]; lia). cbn [teval].
      rewrite LA, LB, LY by exact Hi.
      replace (r3 (fr + 2 * n)) with k by (unfold r3; lk; reflexivity).
      pose proof (Hg i Hi k ltac:(lia)) as G. unfold beta in G.
      rewrite G, Ek, (post_nth V NDV) by exact Hi. reflexivity.
    + rewrite substB_iff by exact NDV. cbn [fd]. intros Hb. apply Hn.
      unfold bassn in *. rewrite <- Hb. apply beval_ext. intros x.
      apply post_agree. intros i Hi. symmetry. apply LY, Hi.
Qed.

Theorem rel_correct : forall c, incl (wvars c) V ->
    forall yb fr s r, yb + n <= fr ->
    (fd (Rel c yb fr) s r <-> ceval c s (post V s r yb)).
Proof.
  induction c as [| x a | c1 IH1 c2 IH2 | b c1 IH1 c2 IH2 | b c IH
                  | c1 IH1 c2 IH2 | x]; intros Hinc yb fr s r Hle;
    simpl in Hinc; cbn [Rel].
  - (* skip *)
    rewrite eqsB_iff by exact NDV. rewrite skip_iff. split.
    + intros H y. destruct (in_dec String.string_dec y V) as [Hy | Hy].
      * exact (H y (AVar y) Hy eq_refl).
      * apply post_out, Hy.
    + intros H y a' _ E. injection E as <-. apply H.
  - (* assignment *)
    rewrite eqsB_iff by exact NDV. rewrite asgn_iff.
    assert (Hx : In x V) by (apply Hinc; left; reflexivity).
    split.
    + intros H y. destruct (in_dec String.string_dec y V) as [Hy | Hy].
      * rewrite (H y _ Hy eq_refl). unfold update.
        destruct (String.eqb x y); reflexivity.
      * rewrite post_out by exact Hy. symmetry. apply update_neq.
        intros ->. contradiction.
    + intros H y a' _ E. injection E as <-. rewrite H. unfold update.
      destruct (String.eqb x y); reflexivity.
  - (* sequencing *)
    unfold seqF. rewrite exB_iff.
    pose proof (incl_app_l _ _ _ Hinc) as I1.
    pose proof (incl_app_r _ _ _ Hinc) as I2.
    split.
    + intros [g [H1 H2]].
      rewrite (IH1 I1 fr (fr + n) s _ ltac:(lia)) in H1.
      rewrite substB_iff, (IH2 I2 yb (fr + n) _ _ ltac:(lia)) in H2
        by exact NDV.
      eapply E_Seq; [exact H1 |]. eapply post_ext_ceval; [| exact H2].
      intros y. rewrite post_post. apply post_agree. intros i Hi.
      rewrite setb_out by lia. reflexivity.
    + intros H. inversion H as [| | ? ? ? s1 ? Hc1 Hc2 | | | | | | |]; subst.
      exists (fun i => s1 (xv i)).
      assert (E1 : forall y, post V s (setb r fr n (fun i => s1 (xv i))) fr y
                             = s1 y).
      { apply (post_from V NDV).
        - intros i Hi. rewrite setb_in by lia.
          replace (fr + i - fr) with i by lia. reflexivity.
        - intros y Hy. symmetry. apply (frame c1 s s1 Hc1).
          intros K. apply Hy, I1, K. }
      split.
      * rewrite (IH1 I1 fr (fr + n) s _ ltac:(lia)).
        eapply post_ext_ceval; [| exact Hc1]. intros y. symmetry. apply E1.
      * rewrite substB_iff by exact NDV.
        rewrite (IH2 I2 yb (fr + n) _ _ ltac:(lia)).
        eapply ceval_ext; [| | exact Hc2].
        -- intros y. symmetry. apply E1.
        -- intros y. rewrite post_post. apply post_agree. intros i Hi.
           rewrite setb_out by lia. reflexivity.
  - (* conditional *)
    pose proof (incl_app_l _ _ _ Hinc) as I1.
    pose proof (incl_app_r _ _ _ Hinc) as I2.
    cbn [fd]. rewrite (IH1 I1 yb fr s r Hle), (IH2 I2 yb fr s r Hle). split.
    + intros [[Hb H] | [Hb H]];
        [apply E_IfTrue | apply E_IfFalse; [apply bassn_false |]]; assumption.
    + intros H. inversion H; subst; [left | right]; split; auto.
      apply bassn_false'. assumption.
  - (* loops *)
    apply while_correct; [exact Hinc | | exact Hle].
    intros yb' fr' s' r' H'. apply IH; assumption.
  - (* choice *)
    pose proof (incl_app_l _ _ _ Hinc) as I1.
    pose proof (incl_app_r _ _ _ Hinc) as I2.
    cbn [fd]. rewrite (IH1 I1 yb fr s r Hle), (IH2 I2 yb fr s r Hle). split.
    + intros [H | H]; [apply E_ChoiceL | apply E_ChoiceR]; assumption.
    + intros H. inversion H; subst; [left | right]; assumption.
  - (* havoc *)
    rewrite eqsB_iff by exact NDV. rewrite havoc_iff.
    assert (Hx : In x V) by (apply Hinc; left; reflexivity).
    split.
    + intros H. exists (post V s r yb x). intros y.
      destruct (String.eqb_spec x y) as [-> | Hne].
      * rewrite update_eq. reflexivity.
      * rewrite update_neq by exact Hne.
        destruct (in_dec String.string_dec y V) as [Hy | Hy].
        -- apply (H y (AVar y) Hy). rewrite (proj2 (String.eqb_neq x y) Hne).
           reflexivity.
        -- apply post_out, Hy.
    + intros [v H] y a' _ E. destruct (String.eqb_spec x y); [discriminate |].
      injection E as <-. rewrite H. apply update_neq. assumption.
Qed.

End Rel.

(** ** Weakest preconditions are formulas *)

Definition wv (c : com) : list var := nodup String.string_dec (wvars c).

Definition Wlp (c : com) (phi : gf) : gf :=
  let V := wv c in let yb := flv phi in
  allB yb (length V)
    (GImp (Rel V c yb (yb + length V)) (substB V yb phi)).

Theorem wlp_correct : forall c phi s r,
    fd (Wlp c phi) s r <-> forall s', ceval c s s' -> fd phi s' r.
Proof.
  intros c phi s r. unfold Wlp.
  set (V := wv c). set (yb := flv phi). set (n := length V).
  assert (ND : NoDup V) by apply NoDup_nodup.
  assert (Inc : incl (wvars c) V)
    by (intros x Hx; apply nodup_In; exact Hx).
  rewrite allB_iff.
  assert (Irr : forall g t, fd phi t (setb r yb n g) <-> fd phi t r).
  { intros g t. apply fd_irr. intros k Hk. apply setb_out. unfold yb. lia. }
  split.
  - intros H s' Hc. specialize (H (fun i => s' (nth i V ""%string))).
    set (rg := setb r yb n (fun i => s' (nth i V ""%string))) in *.
    assert (E : forall x, post V s rg yb x = s' x).
    { apply (post_from V ND).
      - intros i Hi. unfold rg. rewrite setb_in by lia.
        replace (yb + i - yb) with i by lia. reflexivity.
      - intros x Hx. symmetry. apply (frame c s s' Hc).
        intros K. apply Hx, Inc, K. }
    cbn [fd] in H. rewrite (rel_correct V ND c Inc yb (yb + n) s rg) in H
      by lia.
    rewrite substB_iff in H by exact ND.
    assert (Hp : fd phi (post V s rg yb) rg).
    { apply H. eapply ceval_ext; [| | exact Hc]; [reflexivity |].
      intros x. symmetry. apply E. }
    apply Irr in Hp. eapply fd_ext; [| | exact Hp];
      [intros x; symmetry; apply E | reflexivity].
  - intros H g. cbn [fd]. intros HR.
    rewrite (rel_correct V ND c Inc yb (yb + n) s _) in HR by lia.
    rewrite substB_iff by exact ND. apply Irr. apply H, HR.
Qed.

(** ** Cook's theorem, outright *)

Definition r0 : nat -> nat := fun _ => 0.

Definition FA : FoLang.
Proof.
  refine (mkFoLang gf (fun f s => fd f s r0) GSub GAll GAnd
            (fun b f => GAnd f (GB b)) (fun b f => GAnd f (GNot (GB b)))
            (fun b f => GImp (GB b) f) (fun b f => GImp (GNot (GB b)) f)
            _ _ _ _ _ _ _); intros; reflexivity.
Defined.

(** Every weakest liberal precondition is a formula. *)
Theorem wlp_expressible : forall c g, exists f,
    forall s, den FA f s <-> wlpc c (den FA g) s.
Proof.
  intros c g. exists (Wlp c g). intros s. cbn [den FA].
  rewrite wlp_correct. reflexivity.
Qed.

Lemma fa_loops_expressive : forall c, loops_expressive FA c.
Proof.
  induction c; simpl; try tauto.
  split; [| assumption]. intros g. apply wlp_expressible.
Qed.

(** Hoare logic over first-order arithmetic formulas is complete for
    Imp, with no expressiveness assumption. *)
Theorem fa_complete : forall f c g,
    hoare_valid (den FA f) c (den FA g) -> hs FA f c g.
Proof.
  intros f c g V. apply hs_complete; [apply fa_loops_expressive | exact V].
Qed.
