Require Import Coq.Program.Basics.
Require Import TypeclassHierarchy.Instances.Functor.Identity.
Require Import TypeclassHierarchy.Instances.Functor.Maybe.
Require Import TypeclassHierarchy.Instances.Functor.Writer.
Require Import TypeclassHierarchy.Instances.Semigroup.
Require Import TypeclassHierarchy.Interfaces.Functor.

(** Functor *)
Definition f1 : fmap S (Id 5) = Id 6. now compute. Defined.
Definition f2 : fmap S (Just 5) = Just 6. now compute. Defined.
Definition f3 : fmap (fmap S) (Id (Id 5)) = Id (Id 6). now compute. Defined.
Definition f4 : fmap (@fmap Maybe Maybe_Functor nat nat S) (Id (Just 5)) = Id (Just 6).
  now compute.
Defined.

(** TODO: Apply *)

(** Applicative *)
Definition a5 : ap (Just S) (pure 5) = pure 6. now compute. Defined.
Definition a6 : ap (Nothing : Maybe (nat -> nat)) (pure 5) = Nothing. now compute. Defined.
Definition a7 : ap (Just S) Nothing = Nothing. now compute. Defined.

(** TODO: Bind *)

(** Monad *)
Definition m1 : bind (Just 5) pure = Just 5. now compute. Defined.
Definition m2 : bind (Just 0) (compose pure S) = Just 1. now compute. Defined.
Definition m3 : forall A, bind (Nothing : Maybe A) pure = Nothing. now compute. Defined.
Definition m4 : bind (bind (Just 5) (compose pure S)) (compose pure S) = Just 7.
  now compute.
Defined.

Definition m5 : @pure (Writer (list nat)) Writer_Applicative nat 5  = (nil, 5).
  now compute.
Defined.
Definition m6 : @fmap (Writer (list nat)) SG_Writer_Functor nat nat S (@pure (Writer (list nat)) Writer_Applicative nat 5)  = (nil, 6).
  now compute.
Defined.