Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import TypeclassHierarchy.Interfaces.Semigroup.

Instance List_Semigroup :
  forall A : Set, Semigroup (list A) := { sg_op             := @app A
                                   ; sg_op_associative := @app_assoc A
                                   }.

Instance List_Monoid :
  forall A : Set, Monoid (list A) := { monoid_semigroup := List_Semigroup A
                                ; unit             := nil
                                ; left_identity    := @app_nil_l A
                                ; right_identity   := @app_nil_r A
                                }.