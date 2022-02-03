Require Import Reals Psatz Omega.
From Coq Require Export Sorted.
From iris.program_logic Require Export weakestpre prob_adequacy.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Export lang adequacy.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac_auth auth gset.
From iris.heap_lang Require Import proofmode notation par spin_lock.
From mathcomp Require Import seq fintype.

Module Type LAZYLIST_PARAMS.
  Parameter INT_MIN : Z.
  Parameter INT_MAX : Z.
  Parameter (HMIN_MAX: INT_MIN < INT_MAX).
End LAZYLIST_PARAMS.

Definition node_rep : Type := Z * loc * val * val.
Definition node_key (n: node_rep) : Z := n.1.1.1.
Definition node_next (n: node_rep) : loc := n.1.1.2.
Definition node_mark (n: node_rep) : val := n.1.2.
Definition node_lock (n: node_rep) : val := n.2.

Definition nodeKey : val := λ: "l", Fst "l".
Definition nodeNext : val := λ: "l", Fst (Snd "l").
Definition nodeMark : val := λ: "l", Fst (Snd (Snd "l")).
Definition nodeLock : val := λ: "l", Snd (Snd (Snd "l")).

Definition rep_to_node (n: node_rep) : val :=
  (#(node_key n), (#(node_next n), (node_mark n, (node_lock n)))).

Lemma fold_rep_to_node np':
  ((#(node_key np'), (#(node_next np'), (node_mark np', (node_lock np')))))%E =
  rep_to_node np'.
Proof. done. Qed.


Module Lazylist (Params: LAZYLIST_PARAMS).
  Import Params.
  
  Definition tail : node_rep :=
    (INT_MAX, xH, #false, #(LitLoc xH)).

  Definition new : val :=
    λ: <>, (#INT_MIN, (ref (rep_to_node (tail))), #false, newlock #()).

  Definition validate : val := 
    λ: "pred" "curr", 
    let: "pred_mark" := (nodeMark "pred") in
    let: "curr_mark" := (nodeMark "curr") in
    let: "curr'" := !(nodeNext "pred") in
    ("pred_mark" = #false) && ("curr_mark" = #false) && ("curr'" = "curr").
  
  Definition contains : val := 
    rec: "find" "head" "k" :=
    let: "ck" := (nodeKey "head") in
    let: "cm" := (nodeMark "head") in
    if: "k" ≤ "ck"
    then ("k" = "ck") && ("cm" = #false)
    else "find" (nodeNext "head") "k".
  
  Definition add : val := 
    rec: "find" "pred" "k" :=
    let: "curr" := (nodeNext "pred") in
    let: "ck" := (nodeKey "curr") in
    if: "k" ≤ "ck"
    then
      acquire (nodeLock "pred");;
      acquire (nodeLock "curr");;
      if: (validate "pred" "curr")
      then 
        if: ("ck" = "k")
        then
          release (nodeLock "curr");;
          release (nodeLock "pred");;
          #false
        else
          let: "node" := ("k", ("curr", (#false, newlock #()))) in
          (nodeNext "pred") <- "node";;
          release (nodeLock "curr");;
          release (nodeLock "pred");;
          #true
      else
        release (nodeLock "curr");;
        release (nodeLock "pred");;
        "find" "pred" "k" (* Retry *)
    else
      "find" "curr" "k".
  
  Definition remove : val := 
    rec: "find" "pred" "k" :=
    let: "curr" := (nodeNext "pred") in
    let: "ck" := (nodeKey "curr") in
    if: "k" ≤ "ck"
    then
      acquire (nodeLock "pred");;
      acquire (nodeLock "curr");;
      if: (validate "pred" "curr")
      then 
        if: ("ck" = "k")
        then
          (nodeMark "curr") <- #true;;
          (nodeNext "pred") <- (nodeNext "curr");;
          release (nodeLock "curr");;
          release (nodeLock "pred");;
          #true
        else
          release (nodeLock "curr");;
          release (nodeLock "pred");;
          #false
      else
        release (nodeLock "curr");;
        release (nodeLock "pred");;
        "find" "pred" "k" (* Retry *)
    else
      "find" "curr" "k".
End Lazylist.
