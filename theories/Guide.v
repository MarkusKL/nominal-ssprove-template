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



(* We are now ready to define one-time CPA (OTSR). The flag location is used
   to enforce that QUERY is called by the adversary at most once.
 *)
Definition mpk_loc P : Location := ('option P.(Pub); 1%N).
Definition flag_loc : Location := ('option 'unit; 0%N).
Definition GET := 0%N.
Definition QUERY := 1%N.

Definition I_PK_OTSR (P : pk_scheme) :=
  [interface
    [ GET ] : { 'unit ~> P.(Pub) } ;
    [ QUERY ] : { P.(Mes) ~> P.(Cip) }
  ].

(* The games run keygen of the scheme when GET is called and saves the public
   key to mpk_loc.
   Both the real and ideal games are defined at once by controlling the "bit"
   argument b. When b is true the message is encryped and when b is false,
   a random ciphertext is returned.
 *)
Definition PK_OTSR (P : pk_scheme) b :
  game (I_PK_OTSR P) :=
  [module fset
    [:: mpk_loc P ; flag_loc ] ;
    [ GET ] : { 'unit ~> P.(Pub) } '_ {
      getNone mpk_loc P ;;
      '(_, pk) ← P.(keygen) ;;
      #put mpk_loc P := Some pk ;;
      ret pk
    } ;
    [ QUERY ] : { P.(Mes) ~> P.(Cip) } (m) {
      pk ← getSome mpk_loc P ;;
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

Notation " 'g " := (fto (g))
  (at level 3) : package_scope.

Notation " x * y " :=
   (fto (mulg (otf x) (otf y))) : package_scope.

Notation " x ^ a " :=
  (fto (otf x ^+ otf a)) : package_scope.

Notation " x ^- a " :=
  (fto (otf x ^- otf a)) : package_scope.

(* In particular we show that exponentiation
   is bijective. *)
Lemma bij_op_exp : bijective (λ x : 'exp, 'g ^ x)%pack.
Proof.
  eexists (λ a, fto (log (otf a))).
  + intros x.
    rewrite 2!otf_fto.
    rewrite -{2}(fto_otf x).
    f_equal.
    by apply expg_log.
  + intros x.
    rewrite 2!otf_fto.
    rewrite -{2}(fto_otf x).
    f_equal.
    by apply log_expg.
Qed.

Lemma bij_op_mult_op_exp m : bijective (λ x : 'exp, m * ('g ^ x))%pack.
Proof.
  eexists (λ a, fto (log ((otf m)^-1 * otf a))).
  + intros x.
    rewrite 3!otf_fto.
    rewrite -{2}(fto_otf x).
    f_equal.
    rewrite mulKg.
    by apply expg_log.
  + intros x.
    rewrite 3!otf_fto.
    rewrite -{2}(fto_otf x).
    f_equal.
    rewrite -{2}(mulKVg (otf m) (otf x)).
    f_equal.
    by apply log_expg.
Qed.

#[local] Open Scope package_scope.

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
      #put mga_loc := Some ('g ^ a) ;;
      ret ('g ^ a)
    } ;
    [ GETBC ] : { 'unit ~> 'el × 'el } 'tt {
      ga ← getSome mga_loc ;;
      #put mga_loc := None ;;
      b ← sample uniform #|exp| ;;
      if bit then
        @ret ('el × 'el) ('g ^ b, ga ^ b)
      else
        c ← sample uniform #|exp| ;;
        @ret ('el × 'el) ('g ^ b, 'g ^ c)
    }
  ].

End DDH.


Module ElGamal (GP : GroupParam).

#[local] Open Scope package_scope.

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
      ret (sk, 'g ^ sk)
    }
  ; enc := λ pk m,
    {code
      r ← sample uniform #|exp| ;;
      ret ('g ^ r, m * (pk ^ r))
    }
  ; dec := λ sk c,
    {code
      ret (snd c * (fst c ^- sk))
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
  rewrite !otf_fto expgAC -mulgA mulgV mulg1 fto_otf //.
Qed.


(* Now to the security result.
   This reduction is supposed to act like the OTSR game while making calls
   to DDH. Importantly, the reduction cannot know of the "bit" that decides if
   DDH is real or ideal. *)
Definition RED :
  module I_DDH (I_PK_OTSR elgamal) :=
  [module fset
    [:: mpk_loc elgamal ; flag_loc ] ;
    [ GET ] : { 'unit ~> 'el } (_) {
      getNone mpk_loc elgamal ;;
      pk ← call GETA 'unit 'el tt ;;
      #put mpk_loc elgamal := Some pk ;;
      ret pk
    } ;
    [ QUERY ] : { 'el ~> 'el × 'el } (m) {
      _ ← getSome mpk_loc elgamal ;;
      getNone flag_loc ;;
      #put flag_loc := Some tt ;;
      '(r, sh) ← call
        GETBC 'unit ('el × 'el) tt ;;
      @ret ('el × 'el) (r, m * sh)
    }
  ].

Notation inv0 := (
  heap_ignore (fset [:: mga_loc ])
  ⋊ triple_rhs flag_loc (mpk_loc elgamal) mga_loc
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
  - ssprove_code_simpl.
    eapply r_get_vs_get_remember.
    1: ssprove_invariant.
    intros pk.
    ssprove_sync => /eqP -> {pk}.
    ssprove_sync => pk.
    apply r_put_rhs.
    apply r_put_vs_put.

    ssprove_restore_mem.
    2: by apply r_ret.
    ssprove_invariant.
    intros h0 h1 H f.
    by get_heap_simpl.

  - apply r_get_vs_get_remember.
    1: ssprove_invariant.
    move=> //= pk.
    ssprove_code_simpl.
    ssprove_sync => H.
    destruct pk as [pk|] => //= {H}.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    intros f.
    ssprove_sync => H.
    ssprove_swap_rhs 0%N.
    apply r_get_remember_rhs => ga.
    eapply (r_rem_triple_rhs flag_loc (mpk_loc elgamal) mga_loc).
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
