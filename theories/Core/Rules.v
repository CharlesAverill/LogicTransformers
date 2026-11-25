(** * Proof rules for writing proofs in any record

    For a core language, this file gives textbook-style rules at each of
    the four [Plain] nodes of the top face: HL, IL, NC and SIL. Each rule
    is stated for *any* record [V] at that node, so it can be used in any
    logic a transformer produces. [prov V P c Q] means that [V]'s logic
    derives the triple [(P, c, Q)].

    For each node there are rules for [skip], atomic actions, [assume],
    [;], [⊕] and star, a consequence rule in the node's direction, and a
    [while] rule for [kwhile B c = (assume B; c)*; assume ¬B]:

    - HL: the invariant rule;
    - NC: a backward-invariant rule;
    - IL: O'Hearn's iteration-indexed variant rule;
    - SIL: a descending-variant rule (one premise per remaining iteration
      count).

    The rules are admissible: each is proved sound once, and the record's
    completeness turns that into derivability. For the [Dual] nodes, prove
    the triple at the partner node and transport it
    ([vl_transport_compl], [vl_transport_same] in [Framework.Verified]).
    Everything here is constructive. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel.

(** [only s]: the assertion that holds of [s] alone. *)
Definition only {S : Type} (s : S) : S -> Prop := fun x => x = s.

Section Rules.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Notation T := (KLang act_sem).
Notation kev := (kev act_sem).
Notation com := (kcom Σ Act).

Definition prov {d p a} (V : VLogic T d p a) (P : Σ -> Prop) (c : com)
    (Q : Σ -> Prop) : Prop :=
  derivable (rules (vl_logic V)) (@mkTriple T P c Q).

Lemma star_forward : forall (I : Σ -> Prop) c,
    (forall s s', I s -> kev c s s' -> I s') ->
    forall s s', kev (KStar c) s s' -> I s -> I s'.
Proof.
  intros I c Hst s s' H. remember (KStar c) as k eqn:Ek.
  induction H; inversion Ek; subst; intros HI; [exact HI |].
  apply IHkev2; [reflexivity | eapply Hst; eassumption].
Qed.

Lemma star_backward : forall (I : Σ -> Prop) c,
    (forall s s', kev c s s' -> I s' -> I s) ->
    forall s s', kev (KStar c) s s' -> I s' -> I s.
Proof.
  intros I c Hst s s' H. remember (KStar c) as k eqn:Ek.
  induction H; inversion Ek; subst; intros HI; [exact HI |].
  eapply Hst; [eassumption | apply IHkev2; auto].
Qed.

Ltac body_inv H :=
  inversion H; subst;
  match goal with H' : kev (KAssume _) _ _ |- _ => inversion H'; subst end.

(** ** HL: [post P ⊆ Q] *)

Section HL.

Variable V : VLogic T Forward Plain Over.

Lemma hl_iff : forall P c Q,
    prov V P c Q <-> (forall s s', P s -> kev c s s' -> Q s').
Proof.
  intros P c Q. unfold prov. rewrite (vl_theory V). cbn [cvalid].
  exact (hl_valid_iff (@mkTriple T P c Q)).
Qed.

Lemma hl_skip : forall P, prov V P KSkip P.
Proof. intros P. apply hl_iff. intros s s' HP H. inversion H; subst. auto. Qed.

Lemma hl_act : forall Q a,
    prov V (fun s => forall s', act_sem a s s' -> Q s') (KAct a) Q.
Proof.
  intros Q a. apply hl_iff. intros s s' HP H. inversion H; subst. auto.
Qed.

Lemma hl_assume : forall Q (B : Σ -> Prop),
    prov V (fun s => B s -> Q s) (KAssume B) Q.
Proof.
  intros Q B. apply hl_iff. intros s s' HP H. inversion H; subst. auto.
Qed.

Lemma hl_seq : forall P R Q c1 c2,
    prov V P c1 R -> prov V R c2 Q -> prov V P (KSeq c1 c2) Q.
Proof.
  intros P R Q c1 c2 H1 H2. rewrite hl_iff in *.
  intros s s' HP H. inversion H; subst. eauto.
Qed.

Lemma hl_choice : forall P Q c1 c2,
    prov V P c1 Q -> prov V P c2 Q -> prov V P (KChoice c1 c2) Q.
Proof.
  intros P Q c1 c2 H1 H2. rewrite hl_iff in *.
  intros s s' HP H. inversion H; subst; eauto.
Qed.

Lemma hl_star : forall I c, prov V I c I -> prov V I (KStar c) I.
Proof.
  intros I c H. rewrite hl_iff in *. intros s s' HI Hc.
  exact (star_forward I c H s s' Hc HI).
Qed.

Lemma hl_cons : forall P P' Q Q' c,
    (forall s, P s -> P' s) -> prov V P' c Q' -> (forall s, Q' s -> Q s) ->
    prov V P c Q.
Proof.
  intros P P' Q Q' c HP H HQ. rewrite hl_iff in *. eauto.
Qed.

Lemma hl_while : forall I (B : Σ -> Prop) c,
    prov V (fun s => I s /\ B s) c I ->
    prov V I (kwhile B c) (fun s => I s /\ ~ B s).
Proof.
  intros I B c H. rewrite hl_iff in *. intros s s' HI Hc.
  apply kwhile_run_iff in Hc as [Hs Hn]. split; [| exact Hn].
  apply (star_forward I (KSeq (KAssume B) c)) with s;
    [| exact Hs | exact HI].
  intros x x' Hx Hb. body_inv Hb. eauto.
Qed.

End HL.

(** ** IL: [Q ⊆ post P] *)

Section IL.

Variable V : VLogic T Forward Plain Under.

Lemma il_iff : forall P c Q,
    prov V P c Q <-> (forall s', Q s' -> exists s, P s /\ kev c s s').
Proof.
  intros P c Q. unfold prov. rewrite (vl_theory V). cbn [cvalid].
  exact (il_valid_iff (@mkTriple T P c Q)).
Qed.

Lemma il_skip : forall P, prov V P KSkip P.
Proof.
  intros P. apply il_iff. intros s' H. exists s'. split; auto. constructor.
Qed.

Lemma il_act : forall P a,
    prov V P (KAct a) (fun s' => exists s, P s /\ act_sem a s s').
Proof.
  intros P a. apply il_iff. intros s' [s [HP Ha]]. exists s.
  split; [exact HP | apply KE_Act, Ha].
Qed.

Lemma il_assume : forall P (B : Σ -> Prop),
    prov V P (KAssume B) (fun s => P s /\ B s).
Proof.
  intros P B. apply il_iff. intros s' [HP HB]. exists s'.
  split; [exact HP | apply KE_Assume, HB].
Qed.

Lemma il_seq : forall P R Q c1 c2,
    prov V P c1 R -> prov V R c2 Q -> prov V P (KSeq c1 c2) Q.
Proof.
  intros P R Q c1 c2 H1 H2. rewrite il_iff in *. intros s'' HQ.
  destruct (H2 s'' HQ) as [s' [HR H2']]. destruct (H1 s' HR) as [s [HP H1']].
  exists s. split; [exact HP | eapply KE_Seq; eassumption].
Qed.

Lemma il_choice_l : forall P Q c1 c2,
    prov V P c1 Q -> prov V P (KChoice c1 c2) Q.
Proof.
  intros P Q c1 c2 H. rewrite il_iff in *. intros s' HQ.
  destruct (H s' HQ) as [s [HP Hc]]. exists s. split; [exact HP |].
  apply KE_ChoiceL, Hc.
Qed.

Lemma il_choice_r : forall P Q c1 c2,
    prov V P c2 Q -> prov V P (KChoice c1 c2) Q.
Proof.
  intros P Q c1 c2 H. rewrite il_iff in *. intros s' HQ.
  destruct (H s' HQ) as [s [HP Hc]]. exists s. split; [exact HP |].
  apply KE_ChoiceR, Hc.
Qed.

Lemma il_disj : forall P Q1 Q2 c,
    prov V P c Q1 -> prov V P c Q2 -> prov V P c (fun s => Q1 s \/ Q2 s).
Proof.
  intros P Q1 Q2 c H1 H2. rewrite il_iff in *.
  intros s' [Hq | Hq]; [apply H1 | apply H2]; exact Hq.
Qed.

Lemma il_false : forall P c, prov V P c (fun _ => False).
Proof. intros P c. apply il_iff. intros s' []. Qed.

Lemma il_cons : forall P P' Q Q' c,
    (forall s, P' s -> P s) -> prov V P' c Q' -> (forall s, Q s -> Q' s) ->
    prov V P c Q.
Proof.
  intros P P' Q Q' c HP H HQ. rewrite il_iff in *. intros s' Hs'.
  destruct (H s' (HQ s' Hs')) as [s [HP' Hc]]. exists s. auto.
Qed.

Lemma il_star : forall (X : nat -> Σ -> Prop) c,
    (forall n, prov V (X n) c (X (S n))) ->
    prov V (X 0) (KStar c) (fun s => exists n, X n s).
Proof.
  intros X c H. setoid_rewrite il_iff in H. apply il_iff.
  intros s' [n Hn]. revert s' Hn. induction n as [| n IH]; intros s' Hn.
  - exists s'. split; [exact Hn | apply KE_StarRefl].
  - destruct (H n s' Hn) as [s1 [H1 Hc]]. destruct (IH s1 H1) as [s0 [H0 Hs]].
    exists s0. split; [exact H0 | eapply kev_star_snoc; eassumption].
Qed.

Lemma il_while : forall (X : nat -> Σ -> Prop) (B : Σ -> Prop) c,
    (forall n, prov V (fun s => X n s /\ B s) c (X (S n))) ->
    prov V (X 0) (kwhile B c) (fun s => exists n, X n s /\ ~ B s).
Proof.
  intros X B c H. setoid_rewrite il_iff in H. apply il_iff.
  intros s' [n [Hn Hb]].
  assert (Hreach : forall n s', X n s' ->
            exists s, X 0 s /\ kev (KStar (KSeq (KAssume B) c)) s s').
  { induction n0 as [| k IH]; intros x Hx.
    - exists x. split; [exact Hx | apply KE_StarRefl].
    - destruct (H k x Hx) as [x1 [[H1 HB] Hc]].
      destruct (IH x1 H1) as [x0 [H0 Hs]].
      exists x0. split; [exact H0 |].
      eapply kev_star_snoc; [exact Hs |].
      eapply KE_Seq; [apply KE_Assume, HB | exact Hc]. }
  destruct (Hreach n s' Hn) as [s [H0 Hs]].
  exists s. split; [exact H0 | apply kwhile_run_iff; auto].
Qed.

(** From a single state: an atom's rule needs only one step of its
    relation, and [assume]'s only that the state passes. Proofs that
    follow one state through a program use these, for any language. *)

Lemma il_act_pt : forall a s s', act_sem a s s' ->
    prov V (only s) (KAct a) (only s').
Proof.
  intros a s s' H. apply il_iff. intros x E. unfold only in E. subst x.
  exists s. split; [reflexivity | apply KE_Act, H].
Qed.

Lemma il_assume_pt : forall (B : Σ -> Prop) s, B s ->
    prov V (only s) (KAssume B) (only s).
Proof.
  intros B s H. apply il_iff. intros x E. unfold only in E. subst x.
  exists s. split; [reflexivity | apply KE_Assume, H].
Qed.

End IL.

(** ** NC: [pre Q ⊆ P] *)

Section NC.

Variable V : VLogic T Backward Plain Over.

Lemma nc_iff : forall P c Q,
    prov V P c Q <-> (forall s s', kev c s s' -> Q s' -> P s).
Proof.
  intros P c Q. unfold prov. rewrite (vl_theory V). cbn [cvalid].
  exact (nc_valid_iff (@mkTriple T P c Q)).
Qed.

Lemma nc_skip : forall Q, prov V Q KSkip Q.
Proof. intros Q. apply nc_iff. intros s s' H HQ. inversion H; subst. auto. Qed.

Lemma nc_act : forall Q a,
    prov V (fun s => exists s', act_sem a s s' /\ Q s') (KAct a) Q.
Proof.
  intros Q a. apply nc_iff. intros s s' H HQ. inversion H; subst. eauto.
Qed.

Lemma nc_assume : forall Q (B : Σ -> Prop),
    prov V (fun s => B s /\ Q s) (KAssume B) Q.
Proof.
  intros Q B. apply nc_iff. intros s s' H HQ. inversion H; subst. auto.
Qed.

Lemma nc_seq : forall P R Q c1 c2,
    prov V P c1 R -> prov V R c2 Q -> prov V P (KSeq c1 c2) Q.
Proof.
  intros P R Q c1 c2 H1 H2. rewrite nc_iff in *.
  intros s s' H HQ. inversion H; subst. eauto.
Qed.

Lemma nc_choice : forall P Q c1 c2,
    prov V P c1 Q -> prov V P c2 Q -> prov V P (KChoice c1 c2) Q.
Proof.
  intros P Q c1 c2 H1 H2. rewrite nc_iff in *.
  intros s s' H HQ. inversion H; subst; eauto.
Qed.

Lemma nc_cons : forall P P' Q Q' c,
    (forall s, P' s -> P s) -> prov V P' c Q' -> (forall s, Q s -> Q' s) ->
    prov V P c Q.
Proof.
  intros P P' Q Q' c HP H HQ. rewrite nc_iff in *. eauto.
Qed.

Lemma nc_star : forall I c, prov V I c I -> prov V I (KStar c) I.
Proof.
  intros I c H. rewrite nc_iff in *. intros s s' Hc HI.
  exact (star_backward I c H s s' Hc HI).
Qed.

Lemma nc_while : forall I (B : Σ -> Prop) c,
    prov V (fun s => B s -> I s) c I ->
    prov V I (kwhile B c) (fun s => I s /\ ~ B s).
Proof.
  intros I B c H. rewrite nc_iff in *. intros s s' Hc [HI Hn].
  apply kwhile_run_iff in Hc as [Hs _].
  apply (star_backward I (KSeq (KAssume B) c)) with s';
    [| exact Hs | exact HI].
  intros x x' Hb Hx'. body_inv Hb. eapply H; eauto.
Qed.

End NC.

(** ** SIL: [P ⊆ pre Q] *)

Section SIL.

Variable V : VLogic T Backward Plain Under.

Lemma sil_iff : forall P c Q,
    prov V P c Q <-> (forall s, P s -> exists s', kev c s s' /\ Q s').
Proof.
  intros P c Q. unfold prov. rewrite (vl_theory V). cbn [cvalid].
  exact (sil_valid_iff (@mkTriple T P c Q)).
Qed.

Lemma sil_skip : forall Q, prov V Q KSkip Q.
Proof.
  intros Q. apply sil_iff. intros s HQ. exists s. split; [constructor | auto].
Qed.

Lemma sil_act : forall Q a,
    prov V (fun s => exists s', act_sem a s s' /\ Q s') (KAct a) Q.
Proof.
  intros Q a. apply sil_iff. intros s [s' [Ha HQ]]. exists s'.
  split; [apply KE_Act, Ha | exact HQ].
Qed.

Lemma sil_assume : forall Q (B : Σ -> Prop),
    prov V (fun s => B s /\ Q s) (KAssume B) Q.
Proof.
  intros Q B. apply sil_iff. intros s [HB HQ]. exists s.
  split; [apply KE_Assume, HB | exact HQ].
Qed.

Lemma sil_seq : forall P R Q c1 c2,
    prov V P c1 R -> prov V R c2 Q -> prov V P (KSeq c1 c2) Q.
Proof.
  intros P R Q c1 c2 H1 H2. rewrite sil_iff in *. intros s HP.
  destruct (H1 s HP) as [s1 [Hc1 HR]]. destruct (H2 s1 HR) as [s2 [Hc2 HQ]].
  exists s2. split; [eapply KE_Seq; eassumption | exact HQ].
Qed.

Lemma sil_choice_l : forall P Q c1 c2,
    prov V P c1 Q -> prov V P (KChoice c1 c2) Q.
Proof.
  intros P Q c1 c2 H. rewrite sil_iff in *. intros s HP.
  destruct (H s HP) as [s' [Hc HQ]]. exists s'.
  split; [apply KE_ChoiceL, Hc | exact HQ].
Qed.

Lemma sil_choice_r : forall P Q c1 c2,
    prov V P c2 Q -> prov V P (KChoice c1 c2) Q.
Proof.
  intros P Q c1 c2 H. rewrite sil_iff in *. intros s HP.
  destruct (H s HP) as [s' [Hc HQ]]. exists s'.
  split; [apply KE_ChoiceR, Hc | exact HQ].
Qed.

Lemma sil_disj : forall P1 P2 Q c,
    prov V P1 c Q -> prov V P2 c Q -> prov V (fun s => P1 s \/ P2 s) c Q.
Proof.
  intros P1 P2 Q c H1 H2. rewrite sil_iff in *.
  intros s [Hp | Hp]; [apply H1 | apply H2]; exact Hp.
Qed.

Lemma sil_false : forall c Q, prov V (fun _ => False) c Q.
Proof. intros c Q. apply sil_iff. intros s []. Qed.

Lemma sil_cons : forall P P' Q Q' c,
    (forall s, P s -> P' s) -> prov V P' c Q' -> (forall s, Q' s -> Q s) ->
    prov V P c Q.
Proof.
  intros P P' Q Q' c HP H HQ. rewrite sil_iff in *. intros s Hs.
  destruct (H s (HP s Hs)) as [s' [Hc HQ']]. exists s'. auto.
Qed.

Lemma sil_star : forall (X : nat -> Σ -> Prop) c,
    (forall n, prov V (X (S n)) c (X n)) ->
    prov V (fun s => exists n, X n s) (KStar c) (X 0).
Proof.
  intros X c H. setoid_rewrite sil_iff in H. apply sil_iff.
  intros s [n Hn]. revert s Hn. induction n as [| n IH]; intros s Hn.
  - exists s. split; [apply KE_StarRefl | exact Hn].
  - destruct (H n s Hn) as [s1 [Hc H1]]. destruct (IH s1 H1) as [s2 [Hs H2]].
    exists s2. split; [eapply KE_StarStep; eassumption | exact H2].
Qed.

Lemma sil_while : forall (X : nat -> Σ -> Prop) (B : Σ -> Prop) c,
    (forall n, prov V (X (S n)) c (X n)) ->
    (forall n s, X (S n) s -> B s) ->
    (forall s, X 0 s -> ~ B s) ->
    prov V (fun s => exists n, X n s) (kwhile B c) (X 0).
Proof.
  intros X B c H HB H0. setoid_rewrite sil_iff in H. apply sil_iff.
  intros s [n Hn]. revert s Hn. induction n as [| n IH]; intros s Hn.
  - exists s. split; [apply kwhile_run_iff; split; [apply KE_StarRefl |] |];
      auto.
  - destruct (H n s Hn) as [s1 [Hc H1]].
    destruct (IH s1 H1) as [s2 [Hw H2]].
    apply kwhile_run_iff in Hw as [Hs Hnb]. exists s2.
    split; [| exact H2]. apply kwhile_run_iff. split; [| exact Hnb].
    eapply KE_StarStep; [| exact Hs].
    eapply KE_Seq; [apply KE_Assume, (HB n s Hn) | exact Hc].
Qed.

End SIL.

End Rules.
