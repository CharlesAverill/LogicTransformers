(** * Separation logic: the published rules and the generated logic

    [seplog] is separation logic for the heap language of
    [Separation.Heap], with Reynolds's backward ("global") axioms for
    the heap commands (LICS 2002), the usual structural rules, and the
    frame rule:

<<
      {∃v. (e ↦ v * true) ∧ Q[v/x]}          x := [e]   {Q}
      {(e ↦ −) * (e ↦ e' −* Q)}              [e] := e'  {Q}
      {∀l. (l ↦ 0 −* Q[l/x])}                x := alloc {Q}
      {(e ↦ −) * Q}                          free e     {Q}
      {P} c {Q}  ⊢  {P * F} c {Q * F}        (c writes no variable of F)
>>

    - [seplog_sound]: every rule is sound for fault-avoiding partial
      correctness; the frame rule through locality
      ([Heap.frame_valid]).
    - [seplog_complete]: complete, by Cook's argument with weakest
      preconditions: each backward axiom states its command's exact
      weakest precondition.
    - [seplog_iff_generated]: so it proves exactly what the generated
      Hoare logic proves of the heap language.

    Heaps are compared as functions ([functional_extensionality]). *)

From Stdlib Require Import String List Arith Lia FunctionalExtensionality.
From LogicTransformers.Imp Require Import Syntax Hoare.
From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel Rules.
From LogicTransformers.Separation Require Import Heap.
From LogicTransformers.Examples Require Import Common.

Definition htrue : hprop := fun _ _ => True.
Definition anyv (a : aexp) : hprop := fun s h => exists v, pts a v s h.
Definition ptsE (a1 a2 : aexp) : hprop :=
  fun s h => h = single (aeval s a1) (aeval s a2).

Inductive seplog : hprop -> hcmd -> hprop -> Prop :=
  | SL_Skip : forall P, seplog P CSkip' P
  | SL_Asgn : forall Q x a,
      seplog (fun s h => Q (update s x (aeval s a)) h) (CAct (HAsgn x a)) Q
  | SL_Load : forall Q x a,
      seplog (fun s h => exists v, star (pts a v) htrue s h /\
                                   Q (update s x v) h)
             (CAct (HLoad x a)) Q
  | SL_Store : forall Q a1 a2,
      seplog (star (anyv a1) (wand (ptsE a1 a2) Q)) (CAct (HStore a1 a2)) Q
  | SL_Alloc : forall Q x,
      seplog (fun s h => forall l,
                 wand (fun _ h' => h' = single l 0)
                      (fun s' h'' => Q (update s' x l) h'') s h)
             (CAct (HAlloc x)) Q
  | SL_Free : forall Q a, seplog (star (anyv a) Q) (CAct (HFree a)) Q
  | SL_Seq : forall P R Q c1 c2,
      seplog P c1 R -> seplog R c2 Q -> seplog P (CSeq' c1 c2) Q
  | SL_If : forall P Q b c1 c2,
      seplog (fun s h => P s h /\ bassn b s) c1 Q ->
      seplog (fun s h => P s h /\ ~ bassn b s) c2 Q ->
      seplog P (CIf' b c1 c2) Q
  | SL_While : forall I b c,
      seplog (fun s h => I s h /\ bassn b s) c I ->
      seplog I (CWhile' b c) (fun s h => I s h /\ ~ bassn b s)
  | SL_Cons : forall P P' Q Q' c,
      (forall s h, P s h -> P' s h) -> (forall s h, Q' s h -> Q s h) ->
      seplog P' c Q' -> seplog P c Q
  | SL_Frame : forall P Q F c,
      indep (wr c) F -> seplog P c Q -> seplog (star P F) c (star Q F).

(** ** Heap facts *)

Lemma single_eq : forall l v, single l v l = Some v.
Proof. intros. unfold single. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma single_ne : forall l v l', l' <> l -> single l v l' = None.
Proof.
  intros. unfold single. destruct (Nat.eqb_spec l' l); [lia | reflexivity].
Qed.

(** Splitting a heap at an allocated cell. *)
Lemma split_cell : forall h l v, h l = Some v ->
    disj (single l v) (hupd h l None) /\
    h = hunion (single l v) (hupd h l None).
Proof.
  intros h l v E. split.
  - intros l'. destruct (Nat.eq_dec l' l) as [-> | Hne].
    + right. apply hupd_eq.
    + left. apply single_ne, Hne.
  - apply functional_extensionality. intros l'. unfold hunion, hupd, single.
    destruct (Nat.eqb_spec l' l) as [-> | Hne]; [exact E | reflexivity].
Qed.

Lemma star_cell : forall a v Q s h, star (pts a v) Q s h ->
    h (aeval s a) = Some v /\ Q s (hupd h (aeval s a) None).
Proof.
  intros a v Q s h [h1 [h2 [D [-> [Hp Hq]]]]]. unfold pts in Hp. subst h1.
  set (l := aeval s a). split.
  - apply hunion_l, single_eq.
  - replace (hupd (hunion (single l v) h2) l None) with h2; [exact Hq |].
    apply functional_extensionality. intros l'. unfold hupd, hunion.
    destruct (Nat.eqb_spec l' l) as [-> | Hne].
    + destruct (D l) as [K | K]; [rewrite single_eq in K; discriminate | auto].
    + rewrite single_ne by exact Hne. reflexivity.
Qed.

Lemma hunion_single : forall h l v, h l = None ->
    hunion h (single l v) = hupd h l (Some v).
Proof.
  intros h l v E. apply functional_extensionality. intros l'.
  unfold hunion, hupd, single.
  destruct (Nat.eqb_spec l' l) as [-> | Hne]; rewrite ?E; [reflexivity |].
  destruct (h l'); reflexivity.
Qed.

(** ** Runs of the derived commands *)

Lemma if_run : forall b c1 c2 s h r,
    hkev (enc (CIf' b c1 c2)) (Some (s, h)) r ->
    (bassn b s /\ hkev (enc c1) (Some (s, h)) r) \/
    (~ bassn b s /\ hkev (enc c2) (Some (s, h)) r).
Proof.
  intros b c1 c2 s h r H. simpl in H.
  inversion H as [| | | | ? ? ? ? Hk | ? ? ? ? Hk | |]; subst;
    inversion Hk as [| | | ? ? ? m ? Ha Hc | | | |]; subst;
    inversion Ha; subst; [left | right]; auto.
Qed.

Lemma star_inv : forall (I : hprop) b c,
    (forall s h, I s h -> bassn b s -> forall r,
        hkev (enc c) (Some (s, h)) r -> lift I r) ->
    forall r m, hkev (KStar (KSeq (KAssume (test b)) (enc c))) r m ->
    lift I r -> lift I m.
Proof.
  intros I b c H r m Hk. remember (KStar (KSeq (KAssume (test b)) (enc c)))
    as k eqn:Ek.
  induction Hk; inversion Ek; subst; intros HI; [exact HI |].
  apply IHHk2; [reflexivity |].
  destruct s as [[s0 h0] |]; [| contradiction].
  inversion Hk1 as [| | | ? ? ? m' ? Ha Hc | | | |]; subst.
  inversion Ha; subst.
  exact (H s0 h0 HI ltac:(assumption) _ Hc).
Qed.

(** ** Soundness *)

Theorem seplog_sound : forall P c Q, seplog P c Q -> slv P c Q.
Proof.
  intros P c Q H. induction H; intros s h HP r Hk; simpl in Hk.
  - inversion Hk; subst. exact HP.
  - inversion Hk; subst. simpl in *. subst. exact HP.
  - inversion Hk; subst. simpl in *.
    destruct HP as [v [Hs HQ]]. destruct (star_cell a v htrue s h Hs) as [E _].
    rewrite E in *. subst. exact HQ.
  - inversion Hk; subst. simpl in *.
    destruct HP as [h1 [h2 [D [-> [[v Hp] Hw]]]]]. unfold pts in Hp. subst h1.
    rewrite (hunion_l _ _ _ v (single_eq _ _)) in *. subst. simpl.
    assert (D2 : disj h2 (single (aeval s a1) (aeval s a2))).
    { intros l. destruct (Nat.eq_dec l (aeval s a1)) as [-> | Hne].
      - left. destruct (D (aeval s a1)) as [K | K];
          [rewrite single_eq in K; discriminate | exact K].
      - right. apply single_ne, Hne. }
    specialize (Hw _ D2 eq_refl).
    replace (hupd (hunion (single (aeval s a1) v) h2) (aeval s a1)
               (Some (aeval s a2)))
      with (hunion h2 (single (aeval s a1) (aeval s a2))); [exact Hw |].
    apply functional_extensionality. intros l. unfold hupd, hunion, single.
    destruct (Nat.eqb_spec l (aeval s a1)) as [-> | Hne].
    + destruct (D (aeval s a1)) as [K | K];
        [unfold single in K; rewrite Nat.eqb_refl in K; discriminate |].
      rewrite K. reflexivity.
    + destruct (h2 l); reflexivity.
  - inversion Hk; subst. simpl in *.
    match goal with K : exists l, _ |- _ => destruct K as [l [El ->]] end.
    simpl.
    rewrite <- hunion_single by exact El.
    apply (HP l). intros l'. destruct (Nat.eq_dec l' l) as [-> | Hne];
      [left; exact El | right; apply single_ne, Hne].
    reflexivity.
  - inversion Hk; subst. simpl in *.
    destruct HP as [h1 [h2 [D [E [[v Hp] HQ]]]]].
    destruct (star_cell a v Q s h) as [E1 HQ1].
    { exists h1, h2. auto. }
    rewrite E1 in *. subst. exact HQ1.
  - inversion Hk as [| | | ? ? ? r1 ? H1 H2 | | | |]; subst.
    pose proof (IHseplog1 s h HP r1 H1) as K.
    destruct r1 as [[s1 h1] |]; [| contradiction].
    exact (IHseplog2 s1 h1 K r H2).
  - destruct (if_run b c1 c2 s h r Hk) as [[Hb K] | [Hb K]];
      [exact (IHseplog1 s h (conj HP Hb) r K)
      | exact (IHseplog2 s h (conj HP Hb) r K)].
  - inversion Hk as [| | | ? ? ? m ? Hs Ha | | | |]; subst.
    inversion Ha; subst.
    assert (K : lift I r).
    { apply (star_inv I b c) with (r := Some (s, h)); [| exact Hs | exact HP].
      intros s' h' Hi Hb r' Hr. exact (IHseplog s' h' (conj Hi Hb) r' Hr). }
    destruct r as [[s' h'] |]; [| contradiction]. simpl. split; assumption.
  - pose proof (IHseplog s h (H s h HP) r Hk) as K.
    destruct r as [[s' h'] |]; [apply H0, K | exact K].
  - exact (frame_valid P c Q F H (IHseplog) s h HP r Hk).
Qed.

(** ** Completeness *)

Definition wlp (c : hcmd) (Q : hprop) : hprop :=
  fun s h => forall r, hkev (enc c) (Some (s, h)) r -> lift Q r.

Lemma wlp_valid : forall c Q, slv (wlp c Q) c Q.
Proof. intros c Q s h H. exact H. Qed.

Lemma act_run : forall a s h r, hsem a (Some (s, h)) r ->
    hkev (enc (CAct a)) (Some (s, h)) r.
Proof. intros. apply KE_Act. assumption. Qed.

Lemma seplog_wlp : forall c Q, seplog (wlp c Q) c Q.
Proof.
  induction c as [| a | c1 IH1 c2 IH2 | b c1 IH1 c2 IH2 | b c IH];
    intros Q.
  - eapply SL_Cons; [| | apply (SL_Skip Q)]; [| exact (fun _ _ k => k)].
    intros s h H. exact (H _ (KE_Skip _ _)).
  - destruct a as [x e | x e | e1 e2 | x | e].
    + eapply SL_Cons; [| | apply SL_Asgn]; [| exact (fun _ _ k => k)].
      intros s h H. exact (H _ (act_run (HAsgn x e) s h _ eq_refl)).
    + eapply SL_Cons; [| | apply SL_Load]; [| exact (fun _ _ k => k)].
      intros s h H. destruct (h (aeval s e)) as [v |] eqn:E.
      * exists v. split.
        -- destruct (split_cell h (aeval s e) v E) as [D Eh].
           exists (single (aeval s e) v), (hupd h (aeval s e) None).
           split; [exact D | split; [exact Eh |]].
           split; [reflexivity | exact I].
        -- apply (H (Some (update s x v, h))). apply act_run. simpl.
           rewrite E. reflexivity.
      * exfalso. apply (H None). apply act_run. simpl. rewrite E.
        reflexivity.
    + eapply SL_Cons; [| | apply SL_Store]; [| exact (fun _ _ k => k)].
      intros s h H. destruct (h (aeval s e1)) as [v |] eqn:E.
      * destruct (split_cell h (aeval s e1) v E) as [D Eh].
        exists (single (aeval s e1) v), (hupd h (aeval s e1) None).
        split; [exact D | split; [exact Eh |]].
        split; [exists v; reflexivity |].
        intros h' D' Hp. unfold ptsE in Hp. subst h'.
        assert (K := H _ (act_run (HStore e1 e2) s h _
                            ltac:(simpl; rewrite E; reflexivity))).
        simpl in K. replace (hunion (hupd h (aeval s e1) None)
                     (single (aeval s e1) (aeval s e2)))
          with (hupd h (aeval s e1) (Some (aeval s e2))); [exact K |].
        rewrite hunion_single by apply hupd_eq.
        apply functional_extensionality. intros l. unfold hupd.
        destruct (Nat.eqb l (aeval s e1)); reflexivity.
      * exfalso. apply (H None). apply act_run. simpl. rewrite E.
        reflexivity.
    + eapply SL_Cons; [| | apply SL_Alloc]; [| exact (fun _ _ k => k)].
      intros s h H l h' D Hp. subst h'.
      assert (El : h l = None).
      { destruct (D l) as [K | K]; [exact K | rewrite single_eq in K;
                                             discriminate]. }
      rewrite hunion_single by exact El.
      apply (H (Some (update s x l, hupd h l (Some 0)))). apply act_run.
      simpl. exists l. auto.
    + eapply SL_Cons; [| | apply SL_Free]; [| exact (fun _ _ k => k)].
      intros s h H. destruct (h (aeval s e)) as [v |] eqn:E.
      * destruct (split_cell h (aeval s e) v E) as [D Eh].
        exists (single (aeval s e) v), (hupd h (aeval s e) None).
        split; [exact D | split; [exact Eh |]].
        split; [exists v; reflexivity |].
        apply (H (Some (s, hupd h (aeval s e) None))). apply act_run.
        simpl. rewrite E. reflexivity.
      * exfalso. apply (H None). apply act_run. simpl. rewrite E.
        reflexivity.
  - eapply SL_Cons; [| | eapply SL_Seq; [apply (IH1 (wlp c2 Q)) | apply IH2]];
      [| exact (fun _ _ k => k)].
    intros s h H r1 H1. destruct r1 as [[s1 h1] |].
    + intros r H2. apply H. simpl. eapply KE_Seq; eassumption.
    + simpl. apply (H None). simpl. eapply KE_Seq; [exact H1 |].
      apply none_none.
  - apply SL_If.
    + eapply SL_Cons; [| | apply IH1]; [| exact (fun _ _ k => k)].
      intros s h [H Hb] r Hr. apply H. simpl. apply KE_ChoiceL.
      eapply KE_Seq; [apply KE_Assume; exact Hb | exact Hr].
    + eapply SL_Cons; [| | apply IH2]; [| exact (fun _ _ k => k)].
      intros s h [H Hb] r Hr. apply H. simpl. apply KE_ChoiceR.
      eapply KE_Seq; [apply KE_Assume; exact Hb | exact Hr].
  - set (I := wlp (CWhile' b c) Q).
    eapply SL_Cons; [| | apply (SL_While I b c)]; [exact (fun _ _ k => k) | |].
    + intros s h [H Hb]. apply (H (Some (s, h))). simpl.
      eapply KE_Seq; [apply KE_StarRefl | apply KE_Assume; exact Hb].
    + eapply SL_Cons; [| | apply IH]; [| exact (fun _ _ k => k)].
      intros s h [H Hb] r Hr. destruct r as [[s' h'] |].
      * intros r' Hr'. apply H. simpl in Hr' |- *.
        inversion Hr' as [| | | ? ? ? m ? Hs Ha | | | |]; subst.
        eapply KE_Seq; [| exact Ha].
        eapply KE_StarStep; [| exact Hs].
        eapply KE_Seq; [apply KE_Assume; exact Hb | exact Hr].
      * simpl. apply (H None). simpl.
        eapply KE_Seq; [| apply KE_Assume; exact Logic.I].
        eapply KE_StarStep; [| apply KE_StarRefl].
        eapply KE_Seq; [apply KE_Assume; exact Hb | exact Hr].
Qed.

Theorem seplog_complete : forall P c Q, slv P c Q -> seplog P c Q.
Proof.
  intros P c Q V.
  eapply SL_Cons; [| | apply seplog_wlp]; [| exact (fun _ _ k => k)].
  intros s h HP r Hr. exact (V s h HP r Hr).
Qed.

(** ** Against the generated logic *)

Theorem seplog_iff_generated : forall P c Q,
    seplog P c Q <-> sl (HLv hsem) P c Q.
Proof.
  intros P c Q. rewrite slv_iff.
  split; [apply seplog_sound | apply seplog_complete].
Qed.
