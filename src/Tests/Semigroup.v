Require Import Init.Datatypes.
Require Import Coq.Lists.List.
Require Import TypeclassHierarchy.Interfaces.Semigroup.
Require Import TypeclassHierarchy.Instances.Semigroup.

Definition test1 : sg_op (5::nil) (6::nil) = (5::6::nil). now compute. Defined.
Definition test2 : sg_op (5::nil) nil = (5::nil). now compute. Defined.
Definition test3 : sg_op (5::unit) unit = (5::unit). now compute. Defined.
Definition test4 : sg_op (5::unit) nil = (5::unit). now compute. Defined.