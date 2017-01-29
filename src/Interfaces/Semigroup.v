(**
 A semigroup is a Type with equipped with an associative binary operation.

 The only law is associativity:
   - sg_op a (sg_op b c) = sg_op (sg_op a b) c

 As always, lot of the notation (e.g. setoid/extensional equality) is desugared
 to reduce the need for (slow and somewhat unreliable) type inference.
 *)

Class Semigroup (A : Set) : Set :=
  { sg_op             : A -> A -> A
  ; sg_op_associative : forall a b c : A, sg_op a (sg_op b c) = sg_op (sg_op a b) c
  }.


(**
 A monoid is a semigroup with an identity element.

 The only additional law is identity:
   - sg_op unit a = a = sg_op a unit
 *)

Class Monoid (A : Set) : Set :=
  { monoid_semigroup :> Semigroup A
  ; unit             : A
  ; left_identity    : forall a : A, sg_op unit a = a
  ; right_identity   : forall a : A, sg_op a unit = a
  }.