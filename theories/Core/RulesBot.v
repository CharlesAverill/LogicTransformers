(** * Proof rules for the bottom face

    Rules for any record at the four [Plain] nodes of the bottom face
    (assertions over [option Σ], [None = ⊥]). [provb V P c Q] means [V]
    derives [(P, c, Q)]. [som X] lifts a state predicate and excludes ⊥.

    Besides per-construct rules and consequence, the loop rules are:

    - HL⊥: [hlb_while_inv] (partial: a run either diverges or ends in
      [I ∧ ¬B]) and [hlb_while_total] (a well-founded variant: no
      divergence, end in [I ∧ ¬B]);
    - IL⊥: [ilb_while] (O'Hearn's variant) and [ilb_diverge] (divergence
      is reachable, from a coinvariant whose steps are IL⊥ singleton
      triples);
    - NC⊥: [ncb_while] (backward invariant, terminating outcomes) and
      [ncb_div_guard] (only states satisfying the guard can diverge);
    - SIL⊥: [silb_while] (descending variant) and [silb_diverge] (a
      coinvariant: every state can step back into it, so divergence is
      possible).

    Termination-related NC⊥ facts can also be proved as HL⊥ total
    correctness of the complemented triple and transported
    ([vl_transport_compl] then [vl_transport_same]). Everything here is
    constructive. *)

From LogicTransformers.Framework Require Import
  Language ProgramLogic Cube Verified.
From LogicTransformers.Core Require Import Kernel KernelBot.

Section RulesBot.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Notation B := (KLangB act_sem).
Notation kev := (kev act_sem).
Notation kdiv := (kdiv act_sem).
Notation semKB := (semKB act_sem).
Notation com := (kcom Σ Act).

Definition provb {d p a} (V : VLogic B d p a) (P : option Σ -> Prop) (c : com)
    (Q : option Σ -> Prop) : Prop :=
  derivable (rules (vl_logic V)) (@mkTriple B P c Q).

(** [X] on proper states, false on ⊥. *)
Definition som (X : Σ -> Prop) : option Σ -> Prop :=
  fun o => match o with Some s => X s | None => False end.

Ltac kinv H := inversion H; subst.

(** ** HL⊥ *)

Section HLB.

Variable V : VLogic B Forward Plain Over.

Lemma hlb_iff : forall P c Q,
    provb V P c Q <-> (forall o o', P o -> semKB c o o' -> Q o').
Proof.
  intros P c Q. unfold provb. rewrite (vl_theory V). cbn [cvalid].
  exact (hl_valid_iff (@mkTriple B P c Q)).
Qed.

Lemma hlb_skip : forall P, provb V P KSkip P.
Proof.
  intros P. apply hlb_iff. intros o o' HP H. apply semKB_skip in H.
  subst. exact HP.
Qed.

Lemma hlb_act : forall Q a,
    provb V (fun o => match o with
                      | Some s => forall s', act_sem a s s' -> Q (Some s')
                      | None => Q None
                      end) (KAct a) Q.
Proof.
  intros Q a. apply hlb_iff. intros [s|] [s'|] HP H; apply semKB_act in H;
    try contradiction; auto.
Qed.

Lemma hlb_assume : forall Q (Bt : Σ -> Prop),
    provb V (fun o => match o with
                      | Some s => Bt s -> Q (Some s)
                      | None => Q None
                      end) (KAssume Bt) Q.
Proof.
  intros Q Bt. apply hlb_iff. intros [s|] [s'|] HP H;
    apply semKB_assume in H; try contradiction; auto.
  destruct H as [-> HB]. auto.
Qed.

Lemma hlb_seq : forall P R Q c1 c2,
    provb V P c1 R -> provb V R c2 Q -> provb V P (KSeq c1 c2) Q.
Proof.
  intros P R Q c1 c2 H1 H2. rewrite hlb_iff in *. intros o o'' HP H.
  apply semKB_seq in H as [o' [Ha Hb]]. eauto.
Qed.

Lemma hlb_choice : forall P Q c1 c2,
    provb V P c1 Q -> provb V P c2 Q -> provb V P (KChoice c1 c2) Q.
Proof.
  intros P Q c1 c2 H1 H2. rewrite hlb_iff in *. intros o o' HP H.
  apply semKB_choice in H as [H | H]; eauto.
Qed.

Lemma hlb_false : forall c Q, provb V (fun _ => False) c Q.
Proof. intros c Q. apply hlb_iff. intros o o' []. Qed.

Lemma hlb_cons : forall P P' Q Q' c,
    (forall o, P o -> P' o) -> provb V P' c Q' -> (forall o, Q' o -> Q o) ->
    provb V P c Q.
Proof. intros P P' Q Q' c HP H HQ. rewrite hlb_iff in *. eauto. Qed.

(** Partial correctness with ⊥ allowed: the loop diverges or exits in
    [I ∧ ¬B]. The invariant is about proper states only. *)
Lemma hlb_while_inv : forall (I : Σ -> Prop) (Bt : Σ -> Prop) c,
    provb V (som (fun s => I s /\ Bt s)) c
      (fun o => match o with Some s => I s | None => True end) ->
    provb V (som I) (kwhile Bt c)
      (fun o => match o with Some s => I s /\ ~ Bt s | None => True end).
Proof.
  intros I Bt c H. rewrite hlb_iff in *.
  intros [s|] [s'|] HP Hc; simpl in *; try contradiction; auto.
  apply kwhile_run_iff in Hc as [Hs Hn]. split; [| exact Hn].
  remember (KStar (KSeq (KAssume Bt) c)) as k eqn:Ek.
  revert HP. induction Hs; inversion Ek; subst; intros HP; [exact HP |].
  match goal with Hb : kev (KSeq _ _) _ _ |- _ => kinv Hb end.
  match goal with Ha : kev (KAssume _) _ _ |- _ => kinv Ha end.
  match goal with
  | Hk : kev c ?x ?y, Hb : Bt ?x |- _ =>
      apply IHHs2; try reflexivity; try assumption;
      exact (H (Some x) (Some y) (conj HP Hb) Hk)
  end.
Qed.

(** Total correctness: a well-founded variant [mu] decreases on every
    iteration and the body never diverges, so the loop terminates in
    [I ∧ ¬B]. *)
Lemma hlb_while_total : forall (W : Type) (R : W -> W -> Prop)
    (Hwf : well_founded R) (mu : Σ -> W) (I : Σ -> Prop) (Bt : Σ -> Prop) c,
    (forall w, provb V (som (fun s => I s /\ Bt s /\ mu s = w)) c
                 (som (fun s => I s /\ R (mu s) w))) ->
    provb V (som I) (kwhile Bt c) (som (fun s => I s /\ ~ Bt s)).
Proof.
  intros W R Hwf mu I Bt c H. setoid_rewrite hlb_iff in H. apply hlb_iff.
  intros [s|] [s'|] HP Hc; simpl in *; try contradiction.
  - apply kwhile_run_iff in Hc as [Hs Hn]. split; [| exact Hn].
    remember (KStar (KSeq (KAssume Bt) c)) as k eqn:Ek.
    revert HP. induction Hs; inversion Ek; subst; intros HP; [exact HP |].
    match goal with Hb : kev (KSeq _ _) _ _ |- _ => kinv Hb end.
    match goal with Ha : kev (KAssume _) _ _ |- _ => kinv Ha end.
    match goal with
    | Hk : kev c ?x ?y, Hb : Bt ?x |- _ =>
        apply IHHs2; try reflexivity; try assumption;
        exact (proj1 (H (mu x) (Some x) (Some y) (conj HP (conj Hb eq_refl))
                        Hk))
    end.
  - apply (kwhile_no_div_wf act_sem W R I mu Bt c Hwf) with s; auto.
    + intros x Hx Hb Hd. exact (H (mu x) (Some x) None
                                   (conj Hx (conj Hb eq_refl)) Hd).
    + intros x x' Hx Hb Hk. exact (H (mu x) (Some x) (Some x')
                                     (conj Hx (conj Hb eq_refl)) Hk).
Qed.

End HLB.

(** ** IL⊥ *)

Section ILB.

Variable V : VLogic B Forward Plain Under.

Lemma ilb_iff : forall P c Q,
    provb V P c Q <-> (forall o', Q o' -> exists o, P o /\ semKB c o o').
Proof.
  intros P c Q. unfold provb. rewrite (vl_theory V). cbn [cvalid].
  exact (il_valid_iff (@mkTriple B P c Q)).
Qed.

Lemma ilb_skip : forall P, provb V P KSkip P.
Proof.
  intros P. apply ilb_iff. intros o' H. exists o'.
  split; [exact H | apply semKB_skip; reflexivity].
Qed.

Lemma ilb_act : forall P a,
    provb V P (KAct a)
      (fun o' => match o' with
                 | Some s' => exists s, P (Some s) /\ act_sem a s s'
                 | None => P None
                 end).
Proof.
  intros P a. apply ilb_iff. intros [s'|] H.
  - destruct H as [s [HP Ha]]. exists (Some s). split; [exact HP |].
    apply semKB_act. exact Ha.
  - exists None. split; [exact H | exact I].
Qed.

Lemma ilb_assume : forall P (Bt : Σ -> Prop),
    provb V P (KAssume Bt)
      (fun o => match o with Some s => P (Some s) /\ Bt s | None => P None end).
Proof.
  intros P Bt. apply ilb_iff. intros [s|] H.
  - destruct H as [HP HB]. exists (Some s). split; [exact HP |].
    apply semKB_assume. auto.
  - exists None. split; [exact H | exact I].
Qed.

Lemma ilb_seq : forall P R Q c1 c2,
    provb V P c1 R -> provb V R c2 Q -> provb V P (KSeq c1 c2) Q.
Proof.
  intros P R Q c1 c2 H1 H2. rewrite ilb_iff in *. intros o'' HQ.
  destruct (H2 o'' HQ) as [o' [HR Hb]]. destruct (H1 o' HR) as [o [HP Ha]].
  exists o. split; [exact HP | apply semKB_seq; eauto].
Qed.

Lemma ilb_choice_l : forall P Q c1 c2,
    provb V P c1 Q -> provb V P (KChoice c1 c2) Q.
Proof.
  intros P Q c1 c2 H. rewrite ilb_iff in *. intros o' HQ.
  destruct (H o' HQ) as [o [HP Hc]]. exists o.
  split; [exact HP | apply semKB_choice; auto].
Qed.

Lemma ilb_choice_r : forall P Q c1 c2,
    provb V P c2 Q -> provb V P (KChoice c1 c2) Q.
Proof.
  intros P Q c1 c2 H. rewrite ilb_iff in *. intros o' HQ.
  destruct (H o' HQ) as [o [HP Hc]]. exists o.
  split; [exact HP | apply semKB_choice; auto].
Qed.

Lemma ilb_disj : forall P Q1 Q2 c,
    provb V P c Q1 -> provb V P c Q2 -> provb V P c (fun o => Q1 o \/ Q2 o).
Proof.
  intros P Q1 Q2 c H1 H2. rewrite ilb_iff in *.
  intros o' [Hq | Hq]; [apply H1 | apply H2]; exact Hq.
Qed.

Lemma ilb_false : forall P c, provb V P c (fun _ => False).
Proof. intros P c. apply ilb_iff. intros o' []. Qed.

Lemma ilb_cons : forall P P' Q Q' c,
    (forall o, P' o -> P o) -> provb V P' c Q' -> (forall o, Q o -> Q' o) ->
    provb V P c Q.
Proof.
  intros P P' Q Q' c HP H HQ. rewrite ilb_iff in *. intros o' Ho'.
  destruct (H o' (HQ o' Ho')) as [o [HP' Hc]]. exists o. auto.
Qed.

Lemma ilb_while : forall (X : nat -> Σ -> Prop) (Bt : Σ -> Prop) c,
    (forall n, provb V (som (fun s => X n s /\ Bt s)) c (som (X (S n)))) ->
    provb V (som (X 0)) (kwhile Bt c)
      (som (fun s => exists n, X n s /\ ~ Bt s)).
Proof.
  intros X Bt c H. setoid_rewrite ilb_iff in H. apply ilb_iff.
  intros [s'|] Hs'; [| contradiction]. destruct Hs' as [n [Hn Hb]].
  assert (Hreach : forall n s', X n s' ->
            exists s, X 0 s /\ kev (KStar (KSeq (KAssume Bt) c)) s s').
  { induction n0 as [| k IH]; intros x Hx.
    - exists x. split; [exact Hx | apply KE_StarRefl].
    - destruct (H k (Some x) Hx) as [[x1|] [Hpre Hc]]; [| contradiction].
      destruct Hpre as [H1 HB].
      destruct (IH x1 H1) as [x0 [H0 Hs]]. exists x0. split; [exact H0 |].
      eapply kev_star_snoc; [exact Hs |].
      eapply KE_Seq; [apply KE_Assume, HB | exact Hc]. }
  destruct (Hreach n s' Hn) as [s [H0 Hs]].
  exists (Some s). split; [exact H0 | simpl; apply kwhile_run_iff; auto].
Qed.

(** Divergence is reachable from [s0] if [s0] lies in a coinvariant [J]:
    every state of [J] satisfies the guard and has an IL⊥-provable body
    step to a state of [J]. *)
Lemma ilb_diverge : forall (J : Σ -> Prop) (Bt : Σ -> Prop) c (s0 : Σ),
    J s0 ->
    (forall s, J s -> Bt s /\
       exists s', J s' /\
         provb V (fun o => o = Some s) c (fun o => o = Some s')) ->
    provb V (fun o => o = Some s0) (kwhile Bt c) (fun o => o = None).
Proof.
  intros J Bt c s0 H0 H. apply ilb_iff. intros o' ->.
  exists (Some s0). split; [reflexivity |]. simpl.
  apply (kwhile_div_intro act_sem J); [| exact H0].
  intros s Hs. destruct (H s Hs) as [Hb [s' [Hs' D]]].
  split; [exact Hb |]. exists s'. split; [| exact Hs'].
  destruct (proj1 (ilb_iff _ _ _) D (Some s') eq_refl) as [o [Ho Hc]].
  subst o.
  exact Hc.
Qed.

End ILB.

(** ** NC⊥ *)

Section NCB.

Variable V : VLogic B Backward Plain Over.

Lemma ncb_iff : forall P c Q,
    provb V P c Q <-> (forall o o', semKB c o o' -> Q o' -> P o).
Proof.
  intros P c Q. unfold provb. rewrite (vl_theory V). cbn [cvalid].
  exact (nc_valid_iff (@mkTriple B P c Q)).
Qed.

Lemma ncb_skip : forall Q, provb V Q KSkip Q.
Proof.
  intros Q. apply ncb_iff. intros o o' H HQ. apply semKB_skip in H.
  subst. exact HQ.
Qed.

Lemma ncb_act : forall Q a,
    provb V (fun o => match o with
                      | Some s => exists s', act_sem a s s' /\ Q (Some s')
                      | None => Q None
                      end) (KAct a) Q.
Proof.
  intros Q a. apply ncb_iff. intros [s|] [s'|] H HQ; apply semKB_act in H;
    try contradiction; eauto.
Qed.

Lemma ncb_assume : forall Q (Bt : Σ -> Prop),
    provb V (fun o => match o with
                      | Some s => Bt s /\ Q (Some s)
                      | None => Q None
                      end) (KAssume Bt) Q.
Proof.
  intros Q Bt. apply ncb_iff. intros [s|] [s'|] H HQ;
    apply semKB_assume in H; try contradiction; auto.
  destruct H as [-> HB]. auto.
Qed.

Lemma ncb_seq : forall P R Q c1 c2,
    provb V P c1 R -> provb V R c2 Q -> provb V P (KSeq c1 c2) Q.
Proof.
  intros P R Q c1 c2 H1 H2. rewrite ncb_iff in *. intros o o'' H HQ.
  apply semKB_seq in H as [o' [Ha Hb]]. eauto.
Qed.

Lemma ncb_choice : forall P Q c1 c2,
    provb V P c1 Q -> provb V P c2 Q -> provb V P (KChoice c1 c2) Q.
Proof.
  intros P Q c1 c2 H1 H2. rewrite ncb_iff in *. intros o o' H HQ.
  apply semKB_choice in H as [H | H]; eauto.
Qed.

Lemma ncb_cons : forall P P' Q Q' c,
    (forall o, P' o -> P o) -> provb V P' c Q' -> (forall o, Q o -> Q' o) ->
    provb V P c Q.
Proof. intros P P' Q Q' c HP H HQ. rewrite ncb_iff in *. eauto. Qed.

(** Backward invariant for terminating outcomes. *)
Lemma ncb_while : forall (I : Σ -> Prop) (Bt : Σ -> Prop) c,
    provb V (som (fun s => Bt s -> I s)) c (som I) ->
    provb V (som I) (kwhile Bt c) (som (fun s => I s /\ ~ Bt s)).
Proof.
  intros I Bt c H. rewrite ncb_iff in *.
  intros [s|] [s'|] Hc HQ; simpl in *; try contradiction.
  destruct HQ as [HI Hn]. apply kwhile_run_iff in Hc as [Hs _].
  remember (KStar (KSeq (KAssume Bt) c)) as k eqn:Ek.
  induction Hs; inversion Ek; subst; [exact HI |].
  match goal with Hb : kev (KSeq _ _) _ _ |- _ => kinv Hb end.
  match goal with Ha : kev (KAssume _) _ _ |- _ => kinv Ha end.
  match goal with
  | Hk : kev c ?x ?y, Hb : Bt ?x |- _ =>
      exact (H (Some x) (Some y) Hk (IHHs2 eq_refl HI Hn) Hb)
  end.
Qed.

(** Only states satisfying the guard (or ⊥ itself) can lead to ⊥. *)
Lemma ncb_div_guard : forall (Bt : Σ -> Prop) c,
    provb V (fun o => match o with Some s => Bt s | None => True end)
      (kwhile Bt c) (fun o => o = None).
Proof.
  intros Bt c. apply ncb_iff. intros [s|] o' H Ho'; simpl; [| exact I].
  subst. exact (kwhile_div_guard act_sem Bt c s H).
Qed.

End NCB.

(** ** SIL⊥ *)

Section SILB.

Variable V : VLogic B Backward Plain Under.

Lemma silb_iff : forall P c Q,
    provb V P c Q <-> (forall o, P o -> exists o', semKB c o o' /\ Q o').
Proof.
  intros P c Q. unfold provb. rewrite (vl_theory V). cbn [cvalid].
  exact (sil_valid_iff (@mkTriple B P c Q)).
Qed.

Lemma silb_skip : forall Q, provb V Q KSkip Q.
Proof.
  intros Q. apply silb_iff. intros o HQ. exists o.
  split; [apply semKB_skip; reflexivity | exact HQ].
Qed.

Lemma silb_act : forall Q a,
    provb V (fun o => match o with
                      | Some s => exists s', act_sem a s s' /\ Q (Some s')
                      | None => Q None
                      end) (KAct a) Q.
Proof.
  intros Q a. apply silb_iff. intros [s|] H.
  - destruct H as [s' [Ha HQ]]. exists (Some s').
    split; [apply semKB_act; exact Ha | exact HQ].
  - exists None. split; [exact I | exact H].
Qed.

Lemma silb_assume : forall Q (Bt : Σ -> Prop),
    provb V (fun o => match o with
                      | Some s => Bt s /\ Q (Some s)
                      | None => Q None
                      end) (KAssume Bt) Q.
Proof.
  intros Q Bt. apply silb_iff. intros [s|] H.
  - destruct H as [HB HQ]. exists (Some s).
    split; [apply semKB_assume; auto | exact HQ].
  - exists None. split; [exact I | exact H].
Qed.

Lemma silb_seq : forall P R Q c1 c2,
    provb V P c1 R -> provb V R c2 Q -> provb V P (KSeq c1 c2) Q.
Proof.
  intros P R Q c1 c2 H1 H2. rewrite silb_iff in *. intros o HP.
  destruct (H1 o HP) as [o1 [Ha HR]]. destruct (H2 o1 HR) as [o2 [Hb HQ]].
  exists o2. split; [apply semKB_seq; eauto | exact HQ].
Qed.

Lemma silb_choice_l : forall P Q c1 c2,
    provb V P c1 Q -> provb V P (KChoice c1 c2) Q.
Proof.
  intros P Q c1 c2 H. rewrite silb_iff in *. intros o HP.
  destruct (H o HP) as [o' [Hc HQ]]. exists o'.
  split; [apply semKB_choice; auto | exact HQ].
Qed.

Lemma silb_choice_r : forall P Q c1 c2,
    provb V P c2 Q -> provb V P (KChoice c1 c2) Q.
Proof.
  intros P Q c1 c2 H. rewrite silb_iff in *. intros o HP.
  destruct (H o HP) as [o' [Hc HQ]]. exists o'.
  split; [apply semKB_choice; auto | exact HQ].
Qed.

Lemma silb_disj : forall P1 P2 Q c,
    provb V P1 c Q -> provb V P2 c Q -> provb V (fun o => P1 o \/ P2 o) c Q.
Proof.
  intros P1 P2 Q c H1 H2. rewrite silb_iff in *.
  intros o [Hp | Hp]; [apply H1 | apply H2]; exact Hp.
Qed.

(** ⊥ leads to ⊥. *)
Lemma silb_bot : forall c, provb V (fun o => o = None) c (fun o => o = None).
Proof.
  intros c. apply silb_iff. intros o ->. exists None.
  split; [exact I | reflexivity].
Qed.

Lemma silb_false : forall c Q, provb V (fun _ => False) c Q.
Proof. intros c Q. apply silb_iff. intros o []. Qed.

Lemma silb_cons : forall P P' Q Q' c,
    (forall o, P o -> P' o) -> provb V P' c Q' -> (forall o, Q' o -> Q o) ->
    provb V P c Q.
Proof.
  intros P P' Q Q' c HP H HQ. rewrite silb_iff in *. intros o Ho.
  destruct (H o (HP o Ho)) as [o' [Hc HQ']]. exists o'. auto.
Qed.

Lemma silb_while : forall (X : nat -> Σ -> Prop) (Bt : Σ -> Prop) c,
    (forall n, provb V (som (X (S n))) c (som (X n))) ->
    (forall n s, X (S n) s -> Bt s) ->
    (forall s, X 0 s -> ~ Bt s) ->
    provb V (som (fun s => exists n, X n s)) (kwhile Bt c) (som (X 0)).
Proof.
  intros X Bt c H HB H0. setoid_rewrite silb_iff in H. apply silb_iff.
  intros [s|] Hs; [| contradiction]. destruct Hs as [n Hn].
  revert s Hn. induction n as [| n IH]; intros s Hn.
  - exists (Some s). split; [| exact Hn]. simpl.
    apply kwhile_run_iff. split; [apply KE_StarRefl | apply H0, Hn].
  - destruct (H n (Some s) Hn) as [[s1|] [Hc H1]]; [| contradiction].
    destruct (IH s1 H1) as [[s2|] [Hw H2]]; [| contradiction].
    exists (Some s2). split; [| exact H2]. simpl in *.
    apply kwhile_run_iff in Hw as [Hs Hnb].
    apply kwhile_run_iff. split; [| exact Hnb].
    eapply KE_StarStep; [| exact Hs].
    eapply KE_Seq; [apply KE_Assume, (HB n s Hn) | exact Hc].
Qed.

(** Divergence from a coinvariant [J]: every state of [J] satisfies the
    guard and has an SIL⊥-provable body run back into [J]. *)
Lemma silb_diverge : forall (J : Σ -> Prop) (Bt : Σ -> Prop) c,
    provb V (som J) c (som J) ->
    (forall s, J s -> Bt s) ->
    provb V (som J) (kwhile Bt c) (fun o => o = None).
Proof.
  intros J Bt c H HB. rewrite silb_iff in *.
  intros [s|] Hs; [| contradiction]. exists None. split; [| reflexivity].
  simpl. apply (kwhile_div_intro act_sem J); [| exact Hs].
  intros x Hx. split; [apply HB, Hx |].
  destruct (H (Some x) Hx) as [[x'|] [Hc Hx']]; [| contradiction].
  exists x'. auto.
Qed.

End SILB.

End RulesBot.
