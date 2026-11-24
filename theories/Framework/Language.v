(** * Languages

    A language is just enough structure for the cube of program logics:
    programs, states, and a (possibly nondeterministic) input/output
    relation. Languages are first-class records so that logics and
    transformers can quantify over them. *)

Record Language : Type := mkLanguage {
  prog : Type;
  lstate : Type;
  sem : prog -> lstate -> lstate -> Prop
}.

(** The inverse language: same programs and states, with the
    input/output relation reversed. *)
Definition inv (L : Language) : Language :=
  mkLanguage (prog L) (lstate L) (fun c s s' => sem L c s' s).
