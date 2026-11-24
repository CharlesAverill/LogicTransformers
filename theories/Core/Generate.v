(** * Generating proof rules from the structural semantics

    Following Cousot's calculational design: the exact theory of each
    operator is calculated from its semantics, and Aczel's correspondence
    turns the calculated equations into rules. For the core language we
    generate two rule sets, once and for all, for any states and atomic
    actions:

    - [fwd_rule]: strongest postconditions, e.g.
      [sp (star c) P = ⋃ₙ Xₙ] with [X₀ = P], [Xₙ₊₁ = sp c Xₙ];
    - [bwd_rule]: weakest liberal preconditions, e.g.
      [wlp (star c) Q = ⋂ₙ Uₙ] with [U₀ = Q], [Uₙ₊₁ = wlp c Uₙ].

    Each rule is the Aczel rule of the operator's equation. The atoms enter
    only through a relation [rel]; when [rel] agrees with the semantics,

    - [fwd_rule]s are sound at both forward nodes (HL, IL) and derive
      exactly the exact triples ([fwd_theory]);
    - [bwd_rule]s are sound for HL and for the wlp-dual, and derive exact
      wlp triples ([bwd_exact]).

    Because [rel] is a parameter, the generator can also run on a relation
    read off a logic's derivations ([Core.Regenerate]). Everything here is
    constructive. *)

From LogicTransformers.Framework Require Import Language ProgramLogic Cube.
From LogicTransformers.Core Require Import Kernel.

Section Generate.

Context {Σ Act : Type} (act_sem : Act -> Σ -> Σ -> Prop).

Notation L := (KLang act_sem).
Notation kt := (@mkTriple L).
Notation kev := (kev act_sem).
Notation spk := (@img L).
Notation wlpk := (@wlp L).

Variable rel : Act -> Σ -> Σ -> Prop.

Definition sp_rel (a : Act) (P : assertion L) : assertion L :=
  fun s' => exists s, P s /\ rel a s s'.
Definition wlp_rel (a : Act) (Q : assertion L) : assertion L :=
  fun s => forall s', rel a s s' -> Q s'.

Definition kpr0 : triple L -> Prop := fun _ => False.
Definition kpr2 (x y : triple L) : triple L -> Prop := fun t => t = x \/ t = y.

Inductive gname := GSkip | GAct | GAssume | GSeq | GChoice | GStar.

Inductive fwd_rule : gname -> ruleset L :=
  | F_Skip : forall P, fwd_rule GSkip kpr0 (kt P KSkip P)
  | F_Act : forall P a, fwd_rule GAct kpr0 (kt P (KAct a) (sp_rel a P))
  | F_Assume : forall P B,
      fwd_rule GAssume kpr0 (kt P (KAssume B) (fun s => P s /\ B s))
  | F_Seq : forall P Q R c1 c2,
      fwd_rule GSeq (kpr2 (kt P c1 Q) (kt Q c2 R)) (kt P (KSeq c1 c2) R)
  | F_Choice : forall P Q1 Q2 c1 c2,
      fwd_rule GChoice (kpr2 (kt P c1 Q1) (kt P c2 Q2))
        (kt P (KChoice c1 c2) (fun s => Q1 s \/ Q2 s))
  | F_Star : forall (X : nat -> assertion L) c,
      fwd_rule GStar (fun t => exists n, t = kt (X n) c (X (S n)))
        (kt (X 0) (KStar c) (fun s => exists n, X n s)).

Inductive bwd_rule : gname -> ruleset L :=
  | B_Skip : forall Q, bwd_rule GSkip kpr0 (kt Q KSkip Q)
  | B_Act : forall Q a, bwd_rule GAct kpr0 (kt (wlp_rel a Q) (KAct a) Q)
  | B_Assume : forall Q B,
      bwd_rule GAssume kpr0 (kt (fun s => B s -> Q s) (KAssume B) Q)
  | B_Seq : forall P Q R c1 c2,
      bwd_rule GSeq (kpr2 (kt P c1 Q) (kt Q c2 R)) (kt P (KSeq c1 c2) R)
  | B_Choice : forall P1 P2 Q c1 c2,
      bwd_rule GChoice (kpr2 (kt P1 c1 Q) (kt P2 c2 Q))
        (kt (fun s => P1 s /\ P2 s) (KChoice c1 c2) Q)
  | B_Star : forall (U : nat -> assertion L) c,
      bwd_rule GStar (fun t => exists n, t = kt (U (S n)) c (U n))
        (kt (fun s => forall n, U n s) (KStar c) (U 0)).

Hypothesis Hrel : forall a s s', rel a s s' <-> act_sem a s s'.

(** ** Star lemmas *)

Lemma star_over : forall (X : nat -> assertion L) c,
    (forall n s s', X n s -> kev c s s' -> X (S n) s') ->
    forall s s', kev (KStar c) s s' -> forall n, X n s -> exists m, X m s'.
Proof.
  intros X c Hst s s' H. remember (KStar c) as k eqn:Ek.
  induction H; inversion Ek; subst; intros n HX; [exists n; exact HX |].
  apply (IHkev2 eq_refl (S n)). eapply Hst; eassumption.
Qed.

Lemma star_under : forall (X : nat -> assertion L) c,
    (forall n s', X (S n) s' -> exists s, X n s /\ kev c s s') ->
    forall n s', X n s' -> exists s, X 0 s /\ kev (KStar c) s s'.
Proof.
  intros X c Hst n. induction n as [| n IH]; intros s' HX.
  - exists s'. split; [exact HX | apply KE_StarRefl].
  - destruct (Hst n s' HX) as [s1 [H1 Hc]].
    destruct (IH s1 H1) as [s0 [H0 Hs]].
    exists s0. split; [exact H0 | eapply kev_star_snoc; eassumption].
Qed.

Lemma star_wlp_over : forall (U : nat -> assertion L) c,
    (forall n s s', U (S n) s -> kev c s s' -> U n s') ->
    forall s s', kev (KStar c) s s' -> (forall n, U n s) -> forall n, U n s'.
Proof.
  intros U c Hst s s' H. remember (KStar c) as k eqn:Ek.
  induction H; inversion Ek; subst; intros HU; [exact HU |].
  apply IHkev2; [reflexivity |]. intros n. eapply Hst; [apply HU | eassumption].
Qed.

Lemma star_wlp_dual : forall (U : nat -> assertion L) c,
    (forall n s, (forall s', kev c s s' -> U n s') -> U (S n) s) ->
    forall n s, (forall s', kev (KStar c) s s' -> U 0 s') -> U n s.
Proof.
  intros U c Hst n. induction n as [| n IH]; intros s Hw.
  - apply Hw, KE_StarRefl.
  - apply Hst. intros s1 H1. apply IH. intros s'' H2.
    apply Hw. eapply KE_StarStep; eassumption.
Qed.

(** ** Soundness of the forward rules *)


Theorem fwd_over_sound : forall r ps c,
    fwd_rule r ps c ->
    (forall t, ps t -> cube_valid Forward Over t) ->
    cube_valid Forward Over c.
Proof.
  intros r ps c HR H.
  assert (H' : forall t, ps t ->
            forall s s', pre t s -> kev (cmd t) s s' -> post t s')
    by (intros t Ht; apply (hl_valid_iff t), H, Ht).
  clear H. apply hl_valid_iff.
  destruct HR; cbn; intros s s' HP Hc.
  - inversion Hc; subst. exact HP.
  - inversion Hc; subst. exists s. split; [exact HP | apply Hrel; assumption].
  - inversion Hc; subst. split; assumption.
  - inversion Hc; subst.
    apply (H' _ (or_intror eq_refl) s1); [| assumption].
    apply (H' _ (or_introl eq_refl) s); assumption.
  - inversion Hc; subst.
    + left. apply (H' _ (or_introl eq_refl) s); assumption.
    + right. apply (H' _ (or_intror eq_refl) s); assumption.
  - apply (star_over X c) with s 0; [| exact Hc | exact HP].
    intros n x x' Hx Hc'. exact (H' _ (ex_intro _ n eq_refl) x x' Hx Hc').
Qed.

Theorem fwd_under_sound : forall r ps c,
    fwd_rule r ps c ->
    (forall t, ps t -> cube_valid Forward Under t) ->
    cube_valid Forward Under c.
Proof.
  intros r ps c HR H.
  assert (H' : forall t, ps t ->
            forall s', post t s' -> exists s, pre t s /\ kev (cmd t) s s')
    by (intros t Ht; apply (il_valid_iff t), H, Ht).
  clear H. apply il_valid_iff.
  destruct HR; cbn; intros s' Hs'.
  - exists s'. split; [exact Hs' | apply KE_Skip].
  - destruct Hs' as [s [HP Hr]]. exists s.
    split; [exact HP | apply KE_Act, Hrel, Hr].
  - destruct Hs' as [HP HB]. exists s'.
    split; [exact HP | apply KE_Assume, HB].
  - destruct (H' _ (or_intror eq_refl) s' Hs') as [s1 [HQ H2]].
    destruct (H' _ (or_introl eq_refl) s1 HQ) as [s [HP H1]].
    exists s. split; [exact HP | eapply KE_Seq; eassumption].
  - destruct Hs' as [Hq | Hq].
    + destruct (H' _ (or_introl eq_refl) s' Hq) as [s [HP Hc]].
      exists s. split; [exact HP | apply KE_ChoiceL, Hc].
    + destruct (H' _ (or_intror eq_refl) s' Hq) as [s [HP Hc]].
      exists s. split; [exact HP | apply KE_ChoiceR, Hc].
  - destruct Hs' as [n Hn]. apply (star_under X c) with n; [| exact Hn].
    intros k x' Hx'. exact (H' _ (ex_intro _ k eq_refl) x' Hx').
Qed.

(** ** Soundness of the backward rules *)

Theorem bwd_over_sound : forall r ps c,
    bwd_rule r ps c ->
    (forall t, ps t -> cube_valid Forward Over t) ->
    cube_valid Forward Over c.
Proof.
  intros r ps c HR H.
  assert (H' : forall t, ps t ->
            forall s s', pre t s -> kev (cmd t) s s' -> post t s')
    by (intros t Ht; apply (hl_valid_iff t), H, Ht).
  clear H. apply hl_valid_iff.
  destruct HR; cbn; intros s s' HP Hc.
  - inversion Hc; subst. exact HP.
  - inversion Hc; subst. apply HP, Hrel. assumption.
  - inversion Hc; subst. apply HP. assumption.
  - inversion Hc; subst.
    apply (H' _ (or_intror eq_refl) s1); [| assumption].
    apply (H' _ (or_introl eq_refl) s); assumption.
  - inversion Hc; subst.
    + apply (H' _ (or_introl eq_refl) s); [apply HP | assumption].
    + apply (H' _ (or_intror eq_refl) s); [apply HP | assumption].
  - apply (star_wlp_over U c) with s; [| exact Hc | exact HP].
    intros n x x' Hx Hc'. exact (H' _ (ex_intro _ n eq_refl) x x' Hx Hc').
Qed.

Theorem bwd_dual_sound : forall r ps c,
    bwd_rule r ps c ->
    (forall t, ps t -> dual_valid t) ->
    dual_valid c.
Proof.
  intros r ps c HR H.
  assert (H' : forall t, ps t ->
            forall s, (forall s', kev (cmd t) s s' -> post t s') -> pre t s)
    by (intros t Ht; apply H, Ht).
  clear H. destruct HR; unfold dual_valid, aimpl, wlp; cbn; intros s Hw.
  - apply Hw, KE_Skip.
  - intros s' Hr. apply Hw, KE_Act, Hrel, Hr.
  - intros HB. apply Hw, KE_Assume, HB.
  - apply (H' _ (or_introl eq_refl)). intros s1 H1.
    apply (H' _ (or_intror eq_refl)). intros s2 H2.
    apply Hw. eapply KE_Seq; eassumption.
  - split.
    + apply (H' _ (or_introl eq_refl)). intros s' Hc. apply Hw, KE_ChoiceL, Hc.
    + apply (H' _ (or_intror eq_refl)). intros s' Hc. apply Hw, KE_ChoiceR, Hc.
  - intros n. apply (star_wlp_dual U c); [| exact Hw].
    intros k x Hx. exact (H' _ (ex_intro _ k eq_refl) x Hx).
Qed.

(** ** Exactness *)

Definition fwd_base : ruleset L := fun ps c => exists r, fwd_rule r ps c.
Definition bwd_base : ruleset L := fun ps c => exists r, bwd_rule r ps c.

Lemma fwd_step : forall r ps c,
    fwd_rule r ps c -> (forall t, ps t -> fexact t) -> fexact c.
Proof.
  intros r ps c HR H. apply fexact_iff. split.
  - apply (fwd_over_sound r ps c HR). intros t Ht. apply fexact_iff, H, Ht.
  - apply (fwd_under_sound r ps c HR). intros t Ht. apply fexact_iff, H, Ht.
Qed.

Lemma bwd_step : forall r ps c,
    bwd_rule r ps c -> (forall t, ps t -> pexact t) -> pexact c.
Proof.
  intros r ps c HR H. apply pexact_iff. split.
  - apply (bwd_over_sound r ps c HR). intros t Ht. apply pexact_iff, H, Ht.
  - apply (bwd_dual_sound r ps c HR). intros t Ht. apply pexact_iff, H, Ht.
Qed.

Fixpoint sp_iter (P : assertion L) (c : kcom Σ Act) (n : nat) : assertion L :=
  match n with 0 => P | S n => spk c (sp_iter P c n) end.

Fixpoint wlp_iter (Q : assertion L) (c : kcom Σ Act) (n : nat) : assertion L :=
  match n with 0 => Q | S n => wlpk c (wlp_iter Q c n) end.

Ltac gcase der step HR pd pe :=
  eapply D_Equiv;
  [ eapply D_Rule; [eexists; exact HR | pd]
  | first [apply fexact_equiv | apply pexact_equiv];
    eapply (step _ _ _ HR); pe ].

Theorem fwd_exact : forall c P, derivable fwd_base (kt P c (spk c P)).
Proof.
  induction c; intros P.
  - gcase fwd_base fwd_step (F_Skip P) ltac:(intros t []) ltac:(intros t []).
  - gcase fwd_base fwd_step (F_Act P a) ltac:(intros t []) ltac:(intros t []).
  - gcase fwd_base fwd_step (F_Assume P B)
      ltac:(intros t []) ltac:(intros t []).
  - gcase fwd_base fwd_step (F_Seq P (spk c1 P) (spk c2 (spk c1 P)) c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply fexact_img).
  - gcase fwd_base fwd_step (F_Choice P (spk c1 P) (spk c2 P) c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply fexact_img).
  - gcase fwd_base fwd_step (F_Star (sp_iter P c) c)
      ltac:(intros t [n ->]; apply IHc)
      ltac:(intros t [n ->]; apply fexact_img).
Qed.

Theorem bwd_exact : forall c Q, derivable bwd_base (kt (wlpk c Q) c Q).
Proof.
  induction c; intros Q.
  - gcase bwd_base bwd_step (B_Skip Q) ltac:(intros t []) ltac:(intros t []).
  - gcase bwd_base bwd_step (B_Act Q a) ltac:(intros t []) ltac:(intros t []).
  - gcase bwd_base bwd_step (B_Assume Q B)
      ltac:(intros t []) ltac:(intros t []).
  - gcase bwd_base bwd_step (B_Seq (wlpk c1 (wlpk c2 Q)) (wlpk c2 Q) Q c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply pexact_wlp).
  - gcase bwd_base bwd_step (B_Choice (wlpk c1 Q) (wlpk c2 Q) Q c1 c2)
      ltac:(intros t [-> | ->]; auto)
      ltac:(intros t [-> | ->]; apply pexact_wlp).
  - gcase bwd_base bwd_step (B_Star (wlp_iter Q c) c)
      ltac:(intros t [n ->]; apply IHc)
      ltac:(intros t [n ->]; apply pexact_wlp).
Qed.

(** The forward rules derive exactly the exact triples: they are the
    Aczel presentation of the strongest-postcondition theory. *)
Theorem fwd_theory : forall t, derivable fwd_base t <-> fexact t.
Proof.
  intros t. split.
  - intros D. induction D as [ps c [r HR] _ IH | t t' _ IH He].
    + exact (fwd_step r ps c HR IH).
    + apply fexact_iff. apply fexact_iff in IH as [H1 H2].
      split; eapply cube_valid_proper; eassumption.
  - destruct t as [P c Q]. intros H.
    eapply D_Equiv; [apply fwd_exact |].
    apply triple_equiv_sym, fexact_equiv, H.
Qed.

End Generate.

Arguments fwd_rule {Σ Act act_sem} rel.
Arguments bwd_rule {Σ Act act_sem} rel.
Arguments fwd_base {Σ Act act_sem} rel.
Arguments bwd_base {Σ Act act_sem} rel.
