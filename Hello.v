Set Warnings "-notation-overridden".
From mathcomp Require Import all_algebra.
Set Warnings "notation-overridden".
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

End coin_flips.

