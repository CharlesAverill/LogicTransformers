(** * Rely/guarantee with a repaired while rule: complete for sequential code

    [ParImp.RGWhile] shows Jones's while rule, which needs a stable exit
    condition [I ∧ ¬b], is incomplete under interference. [rgc] replaces
    it with the standard fix: the loop's post is any stable [Q] that
    contains [I ∧ ¬b] ([RGC_While]). Everything else is as in
    [ParImp.RGGhost] (Jones's rules plus atomic multiple assignment).

    - [rgc_sound]: every rule is sound.
    - [rgc_complete_seq]: for programs without parallel composition, the
      rules are complete for rely/guarantee validity, under any rely,
      for any reflexive guarantee. The proof is Cook-style: each
      precondition is closed under the rely, and the intermediate
      assertions are the strongest stable postconditions [sp].

    Parallel composition additionally needs auxiliary variables
    ([RGIncomplete.inc2_not_rg], [RGGhost.inc2_by_ghosts]); completeness
    with them is the remaining classical theorem, not mechanized here.
    Axiom-free. *)

From LogicTransformers.Imp Require Import Syntax.
From LogicTransformers.ParImp Require Import ParImp RelyGuarantee RGGhost.

Ltac pinv H := inversion H; subst; clear H.

(** ** The repaired while rule *)

Lemma rg_while2_sound : forall R G (I Q : state -> Prop) b c,
    (forall s, G s s) -> stable R I -> stable R Q ->
    (forall s, I s -> beval s b = false -> Q s) ->
    rg_valid R G (fun s => I s /\ beval s b = true) c I ->
    rg_valid R G I (PWhile b c) Q.
Proof.
  intros R G I Q b c HG HI HQ HE Hb s0 k H0 Hr.
  set (W := PWhile b c).
  set (U := PIf b (PSeq c W) PSkip).
  assert (Hk : (fst k = W /\ I (snd k)) \/ (fst k = U /\ I (snd k)) \/
               (exists c' s1, fst k = PSeq c' W /\
                  (I s1 /\ beval s1 b = true) /\ reach R (c, s1) (c', snd k)) \/
               (fst k = PSkip /\ Q (snd k))).
  { induction Hr as [| k k' _ IH Hst | cc s s' _ IH HR].
    - left. auto.
    - destruct k as [cc s].
      destruct IH as [[E Hi] | [[E Hi] | [[c' [s1 [E [Hp1 Hr1]]]] |
                                         [E Hq]]]];
        cbn [fst snd] in *; subst cc.
      + pinv Hst. right. left. auto.
      + pinv Hst.
        * right. right. left. exists c, s.
          split; [reflexivity |]. split; [auto | apply RRefl].
        * right. right. right. auto.
      + simpl in Hr1. pinv Hst.
        * left. split; [reflexivity |].
          exact (proj2 (Hb s1 _ Hp1 Hr1) eq_refl).
        * right. right. left. eexists _, s1. split; [reflexivity |].
          split; [exact Hp1 | simpl; eapply RProg; eassumption].
      + inversion Hst.
    - destruct IH as [[E Hi] | [[E Hi] | [[c' [s1 [E [Hp1 Hr1]]]] |
                                         [E Hq]]]]; simpl in *.
      + left. split; [exact E | eapply HI; eassumption].
      + right. left. split; [exact E | eapply HI; eassumption].
      + right. right. left. exists c', s1. split; [exact E |].
        split; [exact Hp1 | eapply REnv; eassumption].
      + right. right. right. split; [exact E | eapply HQ; eassumption]. }
  destruct k as [cc s].
  destruct Hk as [[E Hi] | [[E Hi] | [[c' [s1 [E [Hp1 Hr1]]]] |
                                     [E Hq]]]];
    cbn [fst snd] in *; subst cc.
  - split; [| discriminate]. intros k' Hst. pinv Hst. apply HG.
  - split; [| discriminate]. intros k' Hst. pinv Hst; apply HG.
  - split; [| discriminate]. intros k' Hst. pinv Hst.
    + apply HG.
    + exact (proj1 (Hb s1 _ Hp1 Hr1) _ ltac:(eassumption)).
  - split; [intros k' Hst; inversion Hst | intros _; auto].
Qed.

(** ** The rules *)

Inductive rgc : srel -> srel -> (state -> Prop) -> pcom ->
                (state -> Prop) -> Prop :=
  | RGC_Skip : forall R G P, stable R P -> rgc R G P PSkip P
  | RGC_Asgn : forall R G (P Q : state -> Prop) x a,
      stable R P -> stable R Q ->
      (forall s, P s ->
         Q (update s x (aeval s a)) /\ G s (update s x (aeval s a))) ->
      rgc R G P (PAsgn x a) Q
  | RGC_Multi : forall R G (P Q : state -> Prop) l,
      stable R P -> stable R Q ->
      (forall s, P s -> Q (massign l s) /\ G s (massign l s)) ->
      rgc R G P (PMulti l) Q
  | RGC_Seq : forall R G P M Q c1 c2,
      (forall s, G s s) -> rgc R G P c1 M -> rgc R G M c2 Q ->
      rgc R G P (PSeq c1 c2) Q
  | RGC_If : forall R G P Q b c1 c2,
      (forall s, G s s) -> stable R P ->
      rgc R G (fun s => P s /\ beval s b = true) c1 Q ->
      rgc R G (fun s => P s /\ beval s b = false) c2 Q ->
      rgc R G P (PIf b c1 c2) Q
  | RGC_While : forall R G (I Q : state -> Prop) b c,
      (forall s, G s s) -> stable R I -> stable R Q ->
      (forall s, I s -> beval s b = false -> Q s) ->
      rgc R G (fun s => I s /\ beval s b = true) c I ->
      rgc R G I (PWhile b c) Q
  | RGC_Par : forall R G R1 G1 R2 G2 P1 P2 Q1 Q2 c1 c2,
      (forall s, G s s) ->
      (forall s s', R s s' \/ G2 s s' -> R1 s s') ->
      (forall s s', R s s' \/ G1 s s' -> R2 s s') ->
      (forall s s', G1 s s' \/ G2 s s' -> G s s') ->
      rgc R1 G1 P1 c1 Q1 -> rgc R2 G2 P2 c2 Q2 ->
      rgc R G (fun s => P1 s /\ P2 s) (PPar c1 c2) (fun s => Q1 s /\ Q2 s)
  | RGC_Cons : forall R R' G G' P P' Q Q' c,
      (forall s, P s -> P' s) -> (forall s s', R s s' -> R' s s') ->
      (forall s s', G' s s' -> G s s') -> (forall s, Q' s -> Q s) ->
      rgc R' G' P' c Q' -> rgc R G P c Q.

Theorem rgc_sound : forall R G P c Q, rgc R G P c Q -> rg_valid R G P c Q.
Proof.
  intros R G P c Q H. induction H.
  - apply rg_skip_sound; assumption.
  - apply rg_asgn_sound; assumption.
  - apply rg_multi_sound; assumption.
  - eapply rg_seq_sound; eassumption.
  - apply rg_if_sound; assumption.
  - apply rg_while2_sound; assumption.
  - apply (rg_par_sound R G R1 G1 R2 G2 P1 P2 Q1 Q2 c1 c2); assumption.
  - eapply rg_cons_sound; eassumption.
Qed.

(** ** Reachability in context *)

Section Complete.

Variable R G : srel.
Hypothesis HG : forall s, G s s.

Lemma reach_trans : forall k0 k1 k2,
    reach R k0 k1 -> reach R k1 k2 -> reach R k0 k2.
Proof.
  intros k0 k1 k2 H1 H2. induction H2; [exact H1 | |].
  - eapply RProg; eauto.
  - eapply REnv; eauto.
Qed.

Lemma reach_step : forall k0 k1 k2,
    reach R k0 k1 -> pstep k1 k2 -> reach R k0 k2.
Proof. intros. eapply RProg; eassumption. Qed.

Lemma reach_seq : forall c2 k0 k,
    reach R k0 k ->
    reach R (PSeq (fst k0) c2, snd k0) (PSeq (fst k) c2, snd k).
Proof.
  intros c2 k0 k H. induction H.
  - apply RRefl.
  - destruct k as [c s], k' as [c' s'].
    eapply RProg; [exact IHreach | apply PS_Seq; exact H0].
  - eapply REnv; [exact IHreach | exact H0].
Qed.

(** Environment steps at [skip] carry over to any program. *)
Lemma reach_env : forall c s0 s,
    reach R (PSkip, s0) (PSkip, s) -> reach R (c, s0) (c, s).
Proof.
  intros c s0 s H. remember (PSkip, s0) as k0 eqn:E0.
  remember (PSkip, s) as k eqn:E. revert s E.
  induction H; intros s1 E; subst.
  - injection E; intros; subst. apply RRefl.
  - exfalso. assert (Hk : fst k = PSkip).
    { clear -H. induction H; auto. destruct k as [c1 s2].
      simpl in IHreach. subst c1. inversion H0. }
    destruct k as [c1 s2]. simpl in Hk. subst c1. inversion H0.
  - injection E; intros; subst. eapply REnv; [apply IHreach | exact H0].
    reflexivity.
Qed.

(** The guarantee holds on every step reachable from [P]. *)
Definition gok (P : state -> Prop) (c : pcom) : Prop :=
  forall s0 k, P s0 -> reach R (c, s0) k ->
    forall k', pstep k k' -> G (snd k) (snd k').

Lemma gok_from : forall P c P' c',
    (forall s, P' s -> exists s0, P s0 /\ reach R (c, s0) (c', s)) ->
    gok P c -> gok P' c'.
Proof.
  intros P c P' c' H V s1 k H1 Hr k' Hs.
  destruct (H s1 H1) as [s0 [H0 Hr0]].
  exact (V s0 k H0 (reach_trans _ _ _ Hr0 Hr) k' Hs).
Qed.

Lemma gok_seq1 : forall P c1 c2, gok P (PSeq c1 c2) -> gok P c1.
Proof.
  intros P c1 c2 V s0 [c s] H0 Hr [c' s'] Hs.
  exact (V s0 (PSeq c c2, s) H0 (reach_seq c2 (c1, s0) (c, s) Hr)
           (PSeq c' c2, s') (PS_Seq _ _ _ _ _ Hs)).
Qed.

Definition sp (c : pcom) (P : state -> Prop) : state -> Prop :=
  fun s => exists s0, P s0 /\ reach R (c, s0) (PSkip, s).

Definition clo (P : state -> Prop) : state -> Prop :=
  fun s => exists s0, P s0 /\ reach R (PSkip, s0) (PSkip, s).

Lemma sp_stable : forall c P, stable R (sp c P).
Proof.
  intros c P s s' [s0 [H0 Hr]] HR. exists s0.
  split; [exact H0 | eapply REnv; eassumption].
Qed.

Lemma clo_stable : forall P, stable R (clo P).
Proof. intros. apply sp_stable. Qed.

Lemma clo_incl : forall (P : state -> Prop) s, P s -> clo P s.
Proof. intros P s H. exists s. split; [exact H | apply RRefl]. Qed.

Fixpoint par_free (c : pcom) : Prop :=
  match c with
  | PPar _ _ => False
  | PSeq c1 c2 | PIf _ c1 c2 => par_free c1 /\ par_free c2
  | PWhile _ c => par_free c
  | _ => True
  end.

Ltac same := exact (fun _ h => h).
Ltac same2 := exact (fun _ _ h => h).

(** ** Completeness for sequential programs *)

Lemma rgc_sp : forall c, par_free c -> forall P, stable R P -> gok P c ->
    rgc R G P c (sp c P).
Proof.
  induction c as [| x a | c1 IH1 c2 IH2 | b c1 IH1 c2 IH2 | b c IH
                  | c1 IH1 c2 IH2 | l];
    intros Hpf P HP V; simpl in Hpf.
  - (* skip *)
    eapply RGC_Cons; [same | same2 | same2 | | apply RGC_Skip, HP].
    intros s Hs. exists s. split; [exact Hs | apply RRefl].
  - (* assignment *)
    apply RGC_Asgn; [exact HP | apply sp_stable |].
    intros s Hs. split.
    + exists s. split; [exact Hs |].
      eapply RProg; [apply RRefl | apply PS_Asgn].
    + exact (V s (PAsgn x a, s) Hs (RRefl _ _) _ (PS_Asgn x a s)).
  - (* sequencing *)
    destruct Hpf as [P1 P2].
    assert (V1 : gok P c1) by exact (gok_seq1 P c1 c2 V).
    assert (V2 : gok (sp c1 P) c2).
    { apply (gok_from P (PSeq c1 c2)); [| exact V].
      intros s [s0 [H0 Hr]]. exists s0. split; [exact H0 |].
      eapply RProg; [exact (reach_seq c2 (c1, s0) (PSkip, s) Hr) |].
      apply PS_SeqSkip. }
    eapply RGC_Cons; [same | same2 | same2 | |
      apply (RGC_Seq R G P (sp c1 P)); [exact HG | apply IH1; auto |
        apply IH2; [exact P2 | apply sp_stable | exact V2]]].
    intros s [s1 [[s0 [H0 Hr1]] Hr2]]. exists s0. split; [exact H0 |].
    eapply reach_trans; [| exact Hr2].
    eapply RProg; [exact (reach_seq c2 (c1, s0) (PSkip, s1) Hr1) |].
    apply PS_SeqSkip.
  - (* conditional *)
    destruct Hpf as [P1 P2].
    set (Pt := fun s => P s /\ beval s b = true).
    set (Pf := fun s => P s /\ beval s b = false).
    assert (G1 : gok (clo Pt) c1).
    { apply (gok_from P (PIf b c1 c2)); [| exact V].
      intros s [s0 [[H0 Hb] Hr]]. exists s0. split; [exact H0 |].
      eapply reach_trans; [| exact (reach_env c1 s0 s Hr)].
      eapply RProg; [apply RRefl | apply PS_IfT, Hb]. }
    assert (G2 : gok (clo Pf) c2).
    { apply (gok_from P (PIf b c1 c2)); [| exact V].
      intros s [s0 [[H0 Hb] Hr]]. exists s0. split; [exact H0 |].
      eapply reach_trans; [| exact (reach_env c2 s0 s Hr)].
      eapply RProg; [apply RRefl | apply PS_IfF, Hb]. }
    apply RGC_If; [exact HG | exact HP | |].
    + eapply RGC_Cons; [apply clo_incl | same2 | same2 | |
        apply IH1; [exact P1 | apply clo_stable | exact G1]].
      intros s [s1 [[s0 [[H0 Hb] Hr0]] Hr1]]. exists s0.
      split; [exact H0 |].
      eapply reach_trans; [| exact Hr1].
      eapply reach_trans; [| exact (reach_env c1 s0 s1 Hr0)].
      eapply RProg; [apply RRefl | apply PS_IfT, Hb].
    + eapply RGC_Cons; [apply clo_incl | same2 | same2 | |
        apply IH2; [exact P2 | apply clo_stable | exact G2]].
      intros s [s1 [[s0 [[H0 Hb] Hr0]] Hr1]]. exists s0.
      split; [exact H0 |].
      eapply reach_trans; [| exact Hr1].
      eapply reach_trans; [| exact (reach_env c2 s0 s1 Hr0)].
      eapply RProg; [apply RRefl | apply PS_IfF, Hb].
  - (* loops *)
    set (W := PWhile b c).
    set (I := fun s => exists s0, P s0 /\ reach R (W, s0) (W, s)).
    set (Ib := fun s => I s /\ beval s b = true).
    assert (HI : stable R I).
    { intros s s' [s0 [H0 Hr]] HR. exists s0.
      split; [exact H0 | eapply REnv; eassumption]. }
    (* from a state of [clo Ib], the body runs inside the loop *)
    assert (Into : forall s, clo Ib s -> exists s0, P s0 /\
                     reach R (W, s0) (PSeq c W, s)).
    { intros s [s1 [[[s0 [H0 Hr]] Hb] Hr1]]. exists s0. split; [exact H0 |].
      eapply reach_trans; [| exact (reach_env (PSeq c W) s1 s Hr1)].
      eapply RProg; [eapply RProg; [exact Hr | apply PS_While] |].
      apply PS_IfT, Hb. }
    assert (GB : gok (clo Ib) c).
    { apply (gok_seq1 _ c W). apply (gok_from P W); [exact Into | exact V]. }
    eapply RGC_Cons; [| same2 | same2 | same |
      apply (RGC_While R G I (sp W P) b c);
        [exact HG | exact HI | apply sp_stable | |]].
    + intros s Hs. exists s. split; [exact Hs | apply RRefl].
    + intros s [s0 [H0 Hr]] Hb. exists s0. split; [exact H0 |].
      eapply RProg; [eapply RProg; [exact Hr | apply PS_While] |].
      apply PS_IfF, Hb.
    + eapply RGC_Cons; [apply clo_incl | same2 | same2 | |
        apply IH; [exact Hpf | apply clo_stable | exact GB]].
      intros s [s1 [Hs1 Hr]]. destruct (Into s1 Hs1) as [s0 [H0 Hr0]].
      exists s0. split; [exact H0 |].
      eapply RProg; [| apply PS_SeqSkip].
      eapply reach_trans; [exact Hr0 |].
      exact (reach_seq W (c, s1) (PSkip, s) Hr).
  - (* parallel composition: excluded *)
    contradiction.
  - (* multiple assignment *)
    apply RGC_Multi; [exact HP | apply sp_stable |].
    intros s Hs. split.
    + exists s. split; [exact Hs |].
      eapply RProg; [apply RRefl | apply PS_Multi].
    + exact (V s (PMulti l, s) Hs (RRefl _ _) _ (PS_Multi l s)).
Qed.

Theorem rgc_complete_seq : forall P c Q, par_free c ->
    rg_valid R G P c Q -> rgc R G P c Q.
Proof.
  intros P c Q Hpf Vd.
  assert (V : gok (clo P) c).
  { intros s1 k [s0 [H0 Hr0]] Hr k' Hs.
    exact (proj1 (Vd s0 k H0 (reach_trans _ _ _ (reach_env c s0 s1 Hr0) Hr))
             k' Hs). }
  eapply RGC_Cons; [apply clo_incl | same2 | same2 | |
    apply rgc_sp; [exact Hpf | apply clo_stable | exact V]].
  intros s [s1 [[s0 [H0 Hr0]] Hr]].
  exact (proj2 (Vd s0 (PSkip, s) H0
                  (reach_trans _ _ _ (reach_env c s0 s1 Hr0) Hr)) eq_refl).
Qed.

End Complete.
