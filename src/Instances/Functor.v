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

Inductive Maybe (T : Type) : Type :=
  | Just : T -> Maybe T
  | Nothing : Maybe T.
Arguments Nothing {T}.
Arguments Just {T} _.

Definition Maybe_fmap (A B : Type) (f : A -> B) (a : Maybe A) : Maybe B :=
  match a with
    | Just j => Just (f j)
    | Nothing => Nothing
  end.

Instance Maybe_Functor : Functor Maybe := { fmap := Maybe_fmap }.
Proof.
  { (* fmap_proper *)
    intros A B.
    compute.
    intros x y Hyp a.
    case a.
    { (* Just *)
      intros b.
      now rewrite (Hyp b).
    }
    { (* Nothing *)
      trivial.
    }
  }
  { (* fmap_id *)
    intros A.
    compute.
    intros a.
    case a; trivial.
  }
  { (* fmap_comp *)
    intros A B C h g.
    compute.
    intros a.
    case a; trivial.
  }
Defined.

Definition Maybe_ap (A B : Type) (f : Maybe (A -> B)) (a : Maybe A) : Maybe B :=
  match f with
    | Just f' => fmap f' a
    | Nothing => Nothing
  end.

Instance Maybe_Apply :
  Apply Maybe := { apply_functor := Maybe_Functor
                 ; ap            := Maybe_ap
                 }.
Proof.
  intros.
  compute.
  case g; try trivial.
  case f; try trivial.
  case a; trivial.
Defined.

Instance Maybe_Applicative :
  Applicative Maybe := { applicative_apply := Maybe_Apply
                       ; pure              := (fun _ x => Just x)
                       }.
Proof.
  { (* ap_identity *)
    intros.
    compute.
    case a; trivial.
  }
  { (* ap_homomorphism *)
    now compute.
  }
  { (* ap_interchange *)
    intros.
    compute.
    case f; try intros; trivial.
  }
  { (* ap_composition *)
    intros.
    compute.
    case g; case f; case a; trivial.
  }
Defined.

Definition Maybe_bind (A B : Type) (x : Maybe A) (f : A -> Maybe B) : Maybe B :=
  match x with
    | Just x' => f x'
    | Nothing => Nothing
 end.

Instance Maybe_Bind :
  Bind Maybe := { bind_apply := Maybe_Apply
                ; bind       := Maybe_bind
                }.
Proof.
  compute.
  intros.
  case x; try trivial.
Defined.

Instance Maybe_Monad :
  Monad Maybe := { monad_applicative := Maybe_Applicative
                 ; monad_bind        := Maybe_Bind
                 }.
Proof.
  { (* left identity *)
    trivial.
  }
  { (* right identity *)
    intros A B f x.
    case x; try trivial.
  }
Defined.