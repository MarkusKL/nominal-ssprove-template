(* This guide is part of nominal-ssprove-template *)
(* In this guide we formalize one-time CPA-security for the ElGamal public-key
   encryption scheme in Nominal-SSProve. The results and definitions in this
   formalization closely follows the narrative of Joy of Cryptography
   sections 15.1 and 15.3 (available online).

   First we define what a public-key encryption scheme is, its correctness and 
   one-time CPA-security (OTSR). Then we define the two-stage decicional
   Diffie-Hellan (DDH) computational assumption. Finally, we define the ElGamal
   public-key encryption scheme and show that it is perfectly correct and
   that one-time CPA-security reduces to DDH.

   If this file is opened in CoqIDE, the file may be interactively
   evaluated using the arrows in the top bar (mouseover to show tooltip). 
   The top-right side of the screen contains the current proof state while
   the bottom-right side of the screen contains output from certain commands.

   To begin with we state the imports. If loading any of the imports fail,
   the editor has probably not been opened within the development shell.
 *)
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From NominalSSP Require Import Prelude Group.
Import Num.Def Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.
Import GroupScope GRing.Theory.


Module PKScheme.

(* A public-key encryption scheme defines four types, three algorithms
   and stipulates, that there is a way to sample ciphertexts. *)
Record pk_scheme :=
  { Sec : choice_type (* Secret key *)
  ; Pub : choice_type (* Public key *)
  ; Mes : choice_type (* Message *)
  ; Cip : choice_type (* Ciphertext *)
  ; keygen :
      code fset0 [interface] (Sec × Pub)
  ; enc : ∀ (pk : Pub) (m : Mes),
      code fset0 [interface] Cip
  ; dec : ∀ (sk : Sec) (c : Cip),
      code fset0 [interface] Mes
  ; sample_Cip :
    code fset0 [interface] Cip
  }.


Definition ENCDEC := 0%N.

(* We define correctness as the indistinguishability of a real and ideal game,
   that both expose the I_CORR interface. The interface defines one function
   ENCDEC, which takes a message as argument and returns a message. *)
Definition I_CORR (P : pk_scheme) :=
  [interface [ ENCDEC ] : { P.(Mes) ~> P.(Mes) } ].

(* The real correctness game encrypts and decrypts. *)
Definition CORR0 (P : pk_scheme) :
  game (I_CORR P) :=
  [module no_locs ;
    [ ENCDEC ] : { P.(Mes) ~> P.(Mes) } (m) {
      '(sk, pk) ← P.(keygen) ;;
      c ← P.(enc) pk m ;;
      m' ← P.(dec) sk c ;;
      ret m'
    }
  ].

(* The ideal correctness game simply returns the message as given. *)
Definition CORR1 (P : pk_scheme) :
  game (I_CORR P) :=
  [module no_locs ;
    [ ENCDEC ] : { P.(Mes) ~> P.(Mes) } (m) {
      ret m
    }
  ].

(* We may establish correctness of a specific public-key encryption scheme
   by showing that the advantage for an adversary to distinguish the real and
   ideal correctness game is sufficiently small, i.e. the advesary is not
   able to detect if its message has been passed through the encryption and
   decryption. *)
Definition CORR P b := if b then CORR0 P else CORR1 P.


(* We define an initialization procedure that we need later to define
   one-time CPA (OTSR). The first time the procedure is called it generates
   a new set of keys. The next time it is called it simply returns the
   previously generated key. The procedure relies on a location
   (state-variable) to detect if it has been invoked before. *)
Definition init_loc (P : pk_scheme) : Location := ('option P.(Pub); 1%N).

Definition init P : raw_code (P.(Pub)) :=
  locked (
    mpk ← get init_loc P ;;
    match mpk with
    | None => 
      '(_, pk) ← P.(keygen) ;;
      #put init_loc P := Some pk ;;
      ret pk
    | Some pk => ret pk
    end ).

(* We extend the automation with a proof of the fact that init is "valid
   code" i.e. that it may be included in modules later. *)
#[export] Instance init_valid {P} {L : {fset Location}} {I : Interface}
  : init_loc P \in L → ValidCode L I (init P).
Proof.
  intros H.
  rewrite /init -lock.
  ssprove_valid.
Qed.



(* We are now ready to define one-time CPA (OTSR). The flag location is used
   to enforce that QUERY is called by the adversary at most once.
 *)
Definition flag_loc : Location := ('option 'unit; 0%N).
Definition GET := 0%N.
Definition QUERY := 1%N.

Definition I_PK_OTSR (P : pk_scheme) :=
  [interface
    [ GET ] : { 'unit ~> P.(Pub) } ;
    [ QUERY ] : { P.(Mes) ~> P.(Cip) }
  ].

(* The games use the initialization procedure to obtain the public-key.
   Both the real and ideal games are defined at once by controlling the "bit"
   argument b. When b is true the message is encryped and when b is false,
   a random ciphertext is returned.
 *)
Definition PK_OTSR (P : pk_scheme) b :
  game (I_PK_OTSR P) :=
  [module fset
    [:: init_loc P ; flag_loc ] ;
    [ GET ] : { 'unit ~> P.(Pub) } '_ {
      pk ← init P ;;
      ret pk
    } ;
    [ QUERY ] : { P.(Mes) ~> P.(Cip) } (m) {
      pk ← init P ;;
      getNone flag_loc ;;
      #put flag_loc := Some tt ;;
      if b then
        P.(enc) pk m
      else
        P.(sample_Cip)
    }
  ].

End PKScheme.


Module DDH (GP : GroupParam).

Module GT := GroupTheorems GP.
Import GP GT.

(* We define some notation and operators for working with mathcomp's
   groups in Nominal-SSProve. *)
#[export] Instance Positive_el : Positive #|el|.
Proof. apply /card_gt0P. by exists g. Qed.

#[export] Instance Positive_exp : Positive #|exp|.
Proof. apply /card_gt0P. by exists 0. Qed.

Notation " 'el " := 'fin #|el|
  (at level 3) : package_scope.

Notation " 'exp " := 'fin #|exp|
  (at level 3) : package_scope.

Definition op_g : 'el := fto g.

Definition op_mul (x y : 'el) : 'el :=
   fto (otf x * otf y).

Definition op_exp (x : 'el) (a : 'exp) : 'el :=
  fto (otf x ^+ otf a).

Definition op_expn (x : 'el) (a : 'exp) : 'el :=
  fto (otf x ^- otf a).


(* In particular we show that exponentiation
   is bijective. *)
Lemma bij_op_exp : bijective (op_exp op_g).
Proof.
  eexists (λ a, fto (log (otf a))).
  + intros x.
    rewrite /op_exp /op_g 2!otf_fto.
    rewrite -{2}(fto_otf x).
    f_equal.
    by apply expg_log.
  + intros x.
    rewrite /op_exp /op_g 2!otf_fto.
    rewrite -{2}(fto_otf x).
    f_equal.
    by apply log_expg.
Qed.

Lemma bij_op_mult_op_exp m : bijective (λ x, op_mul m (op_exp op_g x)).
Proof.
  eexists (λ a, fto (log ((otf m)^-1 * otf a))).
  + intros x.
    rewrite /op_exp /op_g 3!otf_fto.
    rewrite -{2}(fto_otf x).
    f_equal.
    rewrite mulKg.
    by apply expg_log.
  + intros x.
    rewrite /op_mul /op_exp /op_g 3!otf_fto.
    rewrite -{2}(fto_otf x).
    f_equal.
    rewrite -{2}(mulKVg (otf m) (otf x)).
    f_equal.
    by apply log_expg.
Qed.


(* We define the two-stage DDH assumption. A call to GETA returns g^a while
   a later call to GETBC returns the rest of the triple. We split the DDH
   assumption into two parts to avoid dealing with asynchronous coupling,
   which is out of scope for this guide.
 *)
Definition GETA := 0%N.
Definition GETBC := 1%N.

Definition I_DDH :=
  [interface
    [ GETA ] : { 'unit ~> 'el } ;
    [ GETBC ] : { 'unit ~> 'el × 'el }
  ].

Definition mga_loc : Location := ('option 'el; 3%N).

Definition DDH bit :
  game I_DDH :=
  [module fset [:: mga_loc ] ;
    [ GETA ] : { 'unit ~> 'el } 'tt {
      a ← sample uniform #|exp| ;;
      #put mga_loc := Some (op_exp op_g a) ;;
      ret (op_exp op_g a)
    } ;
    [ GETBC ] : { 'unit ~> 'el × 'el } 'tt {
      ga ← getSome mga_loc ;;
      #put mga_loc := None ;;
      b ← sample uniform #|exp| ;;
      if bit then
        @ret ('el × 'el) (op_exp op_g b, op_exp ga b)
      else
        c ← sample uniform #|exp| ;;
        @ret ('el × 'el) (op_exp op_g b, op_exp op_g c)
    }
  ].

End DDH.


Module ElGamal (GP : GroupParam).

Module DDH' := DDH GP.

Module GT := GroupTheorems GP.
Import GP GT.

Import PKScheme DDH'.

(* We implement the ElGamal public-key encryption scheme. *)
Definition elgamal : pk_scheme := {|
    Sec := 'exp
  ; Pub := 'el
  ; Mes := 'el
  ; Cip := 'el × 'el
  ; keygen :=
    {code
      sk ← sample uniform #|exp| ;;
      ret (sk, op_exp op_g sk)
    }
  ; enc := λ pk m,
    {code
      r ← sample uniform #|exp| ;;
      ret (op_exp op_g r, op_mul m (op_exp pk r))
    }
  ; dec := λ sk c,
    {code
      ret (op_mul (snd c) (op_expn (fst c) sk))
    }
  ; sample_Cip :=
    {code
      c₁ ← sample uniform #|el| ;;
      c₂ ← sample uniform #|el| ;;
      ret (c₁, c₂)
    }
  |}.

(* We show that the two correctness games are perfectly indistinguishable,
   i.e. any adversary (even a computationally unconstrained) will have
   advantage 0 to distinguish the correctness games *)
Theorem correct_elgamal :
  perfect (I_CORR elgamal) (CORR0 elgamal) (CORR1 elgamal).
Proof.
  (* The first three lines are standard for proofs of "perfect" *)
  eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  (* At this point we are asked to prove that each of the functions
     exposed by the two modules are pairwise perfectly indistinguishable.
     We do this in SSProve's probabilistic relational Hoare logic (pRHL). *)
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros sk.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros r.
  apply r_ret => s0 s1.
  split; subst; [| done ].
  unfold op_mul, op_exp, op_g, op_expn.
  rewrite !otf_fto expgAC -mulgA mulgV mulg1 fto_otf //.
Qed.


(* Now to the security result. To define the reduction we introduce an
   alternative initialization procedure. *)
Notation init' := (
  mpk ← get init_loc elgamal ;;
  match mpk with
  | None => 
    pk ← call GETA 'unit 'el tt ;;
    #put init_loc elgamal := Some pk ;;
    ret pk
  | Some pk =>
    ret pk
  end).

(* This reduction is supposed to act like the OTSR game while making calls
   to DDH. Importantly, the reduction cannot know of the "bit" that decides if
   DDH is real or ideal. *)
Definition RED :
  module I_DDH (I_PK_OTSR elgamal) :=
  [module fset
    [:: flag_loc; init_loc elgamal ] ;
    [ GET ] : { 'unit ~> 'el } (_) {
      pk ← init' ;;
      @ret 'el pk
    } ;
    [ QUERY ] : { 'el ~> 'el × 'el } (m) {
      _ ← init' ;;
      getNone flag_loc ;;
      #put flag_loc := Some tt ;;
      '(r, sh) ← call
        GETBC 'unit ('el × 'el) tt ;;
      @ret ('el × 'el) (r, op_mul m sh)
    }
  ].

Notation inv0 := (
  heap_ignore (fset [:: mga_loc ])
  ⋊ triple_rhs flag_loc (PKScheme.init_loc elgamal) mga_loc
      (λ f pk ga, ~~ f → pk = ga)
).

(* We now show that the reduction with DDH is able to perfectly mock the
   behavior of the OTSR games. This proof is performed by relating the two
   programs in the pRHL. *)
Lemma PK_OTSR_RED_DDH_perfect b :
  perfect (I_PK_OTSR elgamal) (PK_OTSR elgamal b) (RED ∘ DDH b).
Proof.
  nssprove_share. eapply prove_perfect.
  apply (eq_rel_perf_ind _ _ inv0).
  1: ssprove_invariant.
  1-4: simpl.
  1: fset_solve.
  1: right; left; fset_solve.
  1: left; fset_solve.
  1: right; right; fset_solve.
  1: done.

  simplify_eq_rel m.
  - rewrite /init -lock //=.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    move=> //= pk.
    destruct pk.
    1: {
      rewrite code_link_bind //=.
      apply r_ret.
      intros s0 s1 H.
      split; [ done | apply H ].
    }
    ssprove_code_simpl; simpl.
    ssprove_sync => a.
    apply r_put_rhs.
    apply r_put_vs_put.
    ssprove_restore_mem.
    2: by apply r_ret.
    ssprove_invariant.
    intros h0 h1 H f.
    by get_heap_simpl.

  - rewrite /init -lock //=.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    move=> //= pk.
    destruct pk as [pk|].
    1,2: ssprove_code_simpl; simpl.
    + apply r_get_vs_get_remember.
      1: ssprove_invariant.
      intros f.
      ssprove_sync => H.
      ssprove_swap_rhs 0%N.
      apply r_get_remember_rhs => ga.
      eapply (r_rem_triple_rhs flag_loc (PKScheme.init_loc elgamal) mga_loc).
      1-4: exact _.
      move: H => /eqP H //= H'.
      rewrite H //= in H'.
      rewrite -H' //= => {H'} {ga}.
      apply r_put_vs_put.
      apply r_put_rhs.
      ssprove_restore_mem.
      1: {
        ssprove_invariant.
        intros h0 h1 [[[[[H0 H1] H2] H3] H4] H5].
        rewrite //= /triple_rhs.
        by get_heap_simpl.
      }
      destruct b; simpl.
      * ssprove_sync => b.
        by apply r_ret.
      * eapply rsymmetry.
        eapply (r_uniform_bij _ _ _ _ _ _ _ bij_op_exp) => c1.
        eapply (r_uniform_bij _ _ _ _ _ _ _ (bij_op_mult_op_exp m)) => c2.
        by eapply r_ret.
    + apply r_forget_rhs, r_forget_lhs.
      ssprove_sync => a.
      ssprove_swap_lhs 0%N.
      ssprove_swap_rhs 1%N.
      ssprove_swap_rhs 0%N.
      apply r_get_vs_get_remember.
      1: ssprove_invariant.
      move=> //= pk.
      ssprove_swap_seq_rhs [:: 3%N; 2%N; 1%N ].
      ssprove_contract_put_get_rhs.
      ssprove_swap_lhs 0%N.
      ssprove_swap_rhs 1%N.
      ssprove_swap_rhs 0%N.
      ssprove_sync => /eqP -> {pk}.
      ssprove_code_simpl; simpl.
      ssprove_swap_rhs 2%N.
      ssprove_swap_rhs 1%N.
      ssprove_contract_put_rhs.
      apply r_put_rhs.
      do 2 apply r_put_vs_put.
      ssprove_restore_mem.
      1: by ssprove_invariant.
      destruct b; simpl.
      * ssprove_sync => b.
        by apply r_ret.
      * eapply rsymmetry.
        eapply (r_uniform_bij _ _ _ _ _ _ _ bij_op_exp) => c1.
        eapply (r_uniform_bij _ _ _ _ _ _ _ (bij_op_mult_op_exp m)) => c2.
        by eapply r_ret.
Qed.

(* Finally, we can state and prove the security statement. Namely, that for
   all adversaries, the advantage to distinguish one-time CPA is less than
   the advantage to distinguish the DDH games. So, assuming
   that the DDH assumption holds in our group of choice, the ElGamal
   public-key encryption scheme is secure.
 *)
Lemma OTSR_elgamal (A : adversary (I_PK_OTSR elgamal)) :
  AdvFor (PK_OTSR elgamal) A <= AdvFor DDH (A ∘ RED).
Proof. rewrite (AdvFor_perfect PK_OTSR_RED_DDH_perfect) Adv_sep_link //. Qed.

End ElGamal.
