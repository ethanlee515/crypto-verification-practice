From mathcomp Require Import all_algebra.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import reals.
From mathcomp Require Import distr probability.
From SSProve Require Import FreeProbProg.
From SSProve.Crypt Require Import ChoiceAsOrd choice_type.
From SSProve.Crypt Require Import SubDistr.
From SSProve Require Import Theta_dens.
From SSProve Require Import Axioms.
Import OrderEnrichedCategory.
Import OrderEnrichedRelativeMonadExamples.
Import choice.

Open Scope real_scope.
Open Scope bool_scope.

Section coin_flips.

Definition fair_coin_distr := dflip (1 / 2 : R).
Definition coin_op : P_OP := existT _ chBool fair_coin_distr.
Definition flip := callrFree P_OP P_AR coin_op.

Definition prog :=
  bindrFree P_OP P_AR flip (fun b1 =>
  bindrFree P_OP P_AR flip (fun b2 =>
    retrFree P_OP P_AR chBool (b1 && b2)
  )).

Lemma probability_fact :
  \dlet_(s <- dflip (1 / 2 : R))
  \dlet_(s0 <- dflip (1 / 2 : R))
    dunit (s && s0) =
  dflip (1 / 4 : R).
Proof.
(* This is in mathcomp land. *)
Admitted.

Lemma prog_semantics :
  unary_ThetaDens0 chBool prog = dflip (1 / 4 : R).
Proof.
  rewrite /unary_ThetaDens0 //=.
  rewrite /SDistr_bind /SDistr_unit //=.
  rewrite /fair_coin_distr //=.
  exact probability_fact.
Qed.

End coin_flips.

