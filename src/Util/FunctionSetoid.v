Require Import Relation_Definitions.
Require Import Coq.Setoids.Setoid.

(**
  The only worthwhile instances of typeclasses are lawful ones. Therefore, this
  library packages the interfaces together with proofs that the laws hold.
  However, some laws include assertions of function equality (think `fmap id =
  id`), which is not a native concept to Coq. Therefore, we use a Setoid which
  encodes extensional equality and allows us to use the setoid rewriting tactics
  when proving it.
 *)

Section ExtensionalEquality.
  Variable A B : Type.

  Definition extensional_equality (f g : A -> B) : Prop := forall a : A, f a = g a.

  (* do we need a class? *)
  (* Class ExtensionallyEqual (f g : A -> B) : Prop := *)
  (*   { extensionally_equal : extensional_equality f g; }. *)

  (* This was the common component of all three proofs *)
  Ltac dnry x := unfold x; intros; unfold extensional_equality in *; intros.

  Lemma extensional_equality_refl : reflexive _ extensional_equality.
    dnry reflexive.
    trivial.
  Qed.

  Lemma extensional_equality_sym: symmetric _ extensional_equality.
    dnry symmetric.
    apply eq_sym.
    apply (H a).
  Qed.

  Lemma extensional_equality_trans: transitive _ extensional_equality.
    dnry transitive.
    rewrite (H a).
    apply (H0 a).
  Qed.

  Add Parametric Relation : (A -> B) extensional_equality
  reflexivity proved by extensional_equality_refl
  symmetry proved by extensional_equality_sym
  transitivity proved by extensional_equality_trans
  as extensional_equality_rel.

End ExtensionalEquality.

(**
 Since composition is the most common operation on functions, we also provide a
 proof that it is proper with respect to extensional equality as defined above
 as a Lemma.
 *)

Require Import MathClasses.interfaces.canonical_names.

Section Composition.
  Variable A B C : Type.
  Lemma composition_proper : Proper ((@extensional_equality B C) ==> (@extensional_equality A B) ==> (@extensional_equality A C)) (∘).
    compute.
    intros.
    rewrite (H0 a).
    now rewrite (H (y0 a)).
  Qed.
End Composition.