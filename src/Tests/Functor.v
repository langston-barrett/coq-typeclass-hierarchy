Require Import TypeclassHierarchy.Interfaces.Functor.
Require Import TypeclassHierarchy.Instances.Functor.

Definition t1 : fmap S (Id 5) = Id 6. now compute. Defined.
Definition t2 : fmap S (Just 5) = Just 6. now compute. Defined.
Definition t3 : fmap (fmap S) (Id (Id 5)) = Id (Id 6). now compute. Defined.
Definition t4 : fmap (@fmap Maybe Maybe_Functor nat nat S) (Id (Just 5)) = Id (Just 6).
  now compute.
Defined.

Definition t5 : ap (Just S) (pure 5) = pure 6. now compute. Defined.
Definition t6 : ap (Nothing : Maybe (nat -> nat)) (pure 5) = Nothing. now compute. Defined.
Definition t7 : ap (Just S) Nothing = Nothing. now compute. Defined.

