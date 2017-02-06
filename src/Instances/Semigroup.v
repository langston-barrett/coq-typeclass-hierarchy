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

Section Nat_Monoid.
  Instance Nat_Semigroup : Semigroup nat :=
    { sg_op             := plus
    ; sg_op_associative := Plus.plus_assoc
    }.

  Instance Nat_Monoid : Monoid nat :=
    { monoid_semigroup := Nat_Semigroup
    ; unit             := 0
    }.
  Proof.
    { (* Left identity *)
      unfold sg_op.
      unfold Nat_Semigroup.
      apply plus_O_n.
    }
    {
      unfold sg_op.
      unfold Nat_Semigroup.
      intros a.
      apply (eq_sym (x := a) (y := a + 0)).
      apply plus_n_O.
    }
  Defined.
End Nat_Monoid.