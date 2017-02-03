Require Import Coq.Program.Basics.
Require Import TypeclassHierarchy.Util.FunctionSetoid.
Require Import TypeclassHierarchy.Interfaces.Functor.

Inductive Identity (T : Type) : Type := Id : T -> Identity T.
Arguments Id {T} _.

Definition Id_fmap (A B : Type) (f : A -> B) (a : Identity A) : Identity B :=
  match a with
    Id a => Id (f a)
  end.

Instance Identity_Functor : Functor Identity := { fmap := Id_fmap }.
Proof.
  { (* fmap_proper *)
    intros A B.
    compute.
    intros x y Hyp a.
    case a.
    intros b.
    now rewrite (Hyp b).
  }
  { (* fmap_id *)
    intros A.
    compute.
    intros a.
    now case a.
  }
  { (* fmap_comp *)
    intros A B C h g.
    compute.
    intros a.
    now case a.
  }
Defined.