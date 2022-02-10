Require Import Utf8.
From stdpp Require Import base.

Class DisjointList A := disjoint_list : list A → Prop.
Hint Mode DisjointList ! : typeclass_instances.
Instance: Params (@disjoint_list) 2 := {}.
Notation "## Xs" := (disjoint_list Xs) (at level 20, format "##  Xs") : stdpp_scope.
Notation "##@{ A } Xs" :=
  (@disjoint_list A _ Xs) (at level 20, only parsing) : stdpp_scope.

Section disjoint_list.
  Context `{Disjoint A, Union A, Empty A}.
  Implicit Types X : A.

  Inductive disjoint_list_default : DisjointList A :=
    | disjoint_nil_2 : ##@{A} []
    | disjoint_cons_2 (X : A) (Xs : list A) : X ## ⋃ Xs → ## Xs → ## (X :: Xs).
  Global Existing Instance disjoint_list_default.

  Lemma disjoint_list_nil  : ##@{A} [] ↔ True.
  Proof. split; constructor. Qed.
  Lemma disjoint_list_cons X Xs : ## (X :: Xs) ↔ X ## ⋃ Xs ∧ ## Xs.
  Proof. split. inversion_clear 1; auto. intros [??]. constructor; auto. Qed.
End disjoint_list.
