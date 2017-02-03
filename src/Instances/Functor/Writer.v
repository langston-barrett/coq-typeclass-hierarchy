Require Import TypeclassHierarchy.Interfaces.Semigroup.
Require Import TypeclassHierarchy.Interfaces.Functor.

Definition SG_Writer (W : Set) {SW : Semigroup W} (A : Type) : Type := (W * A).

Section SG_Writer_Bind.
  Context `{Semigroup W}.

  Definition SG_Writer_fmap (A B : Type) (f : A -> B) (a : SG_Writer W A) : SG_Writer W B :=
    match a with
      | (first, second) => (first, f second)
    end.

  Instance SG_Writer_Functor : Functor (SG_Writer W) :=
    { fmap := SG_Writer_fmap }.

  Proof.
    { (* fmap is proper w/r/t extensional equality *)
      (* this proof is turn-key, might want to consider something better *)
      intros A B.
      unfold Morphisms.Proper.
      unfold Morphisms.respectful.
      intros f g.
      unfold FunctionSetoid.extensional_equality.
      intros Hyp.
      destruct a as [log a'].
      unfold SG_Writer_fmap.
      now rewrite Hyp.
    }
    { (* fmap id = id *)
      intros A.
      unfold FunctionSetoid.extensional_equality.
      intros a.
      unfold SG_Writer_fmap.
      destruct a as [log a'].
      now unfold canonical_names.id.
    }
    { (* fmap f . fmap g = fmap (f . g) *)
      intros A B C h g.
      unfold FunctionSetoid.extensional_equality.
      intros a.
      destruct a as [log a'].
      now unfold SG_Writer_fmap.
    }
  Defined.

  Definition SG_Writer_ap
    (A B : Type) (f : SG_Writer W (A -> B)) (a : SG_Writer W A)
      : SG_Writer W B :=
    match f with
      | (log1, f') =>
        match a with
          | (log2, a') => (sg_op log1 log2, f' a')
        end
    end.

  Instance SG_Writer_Apply : Apply (SG_Writer W) :=
    { apply_functor := SG_Writer_Functor
    ; ap            := SG_Writer_ap
    }.
  Proof.
    intros A B C f g a.
    (* Managing complexity using clever names? Maybe. *)
    destruct a as [log_a a'].
    destruct f as [log_f f'].
    destruct g as [log_g g'].
    unfold SG_Writer_ap.
    now rewrite sg_op_associative.
  Defined.

  Definition SG_Writer_bind
             (A B : Type) (a : SG_Writer W A) (f : A -> SG_Writer W B) : SG_Writer W B :=
    match a with
      | (log1, a') =>
        match f a' with
          | (log2, fa) => (sg_op log1 log2, fa)
        end
    end.

  Instance SG_Writer_Bind : Bind (SG_Writer W) := { bind := SG_Writer_bind }.
  Proof.
    intros A B C x f g.
    destruct x as [log_x x'].
    unfold SG_Writer_bind.
    destruct f as [log_f b].
    destruct g as [log_g c].
    now rewrite sg_op_associative.
  Defined.
End SG_Writer_Bind.

Definition Writer (W : Set) {MW : Monoid W} (A : Type) : Type :=
  @SG_Writer W monoid_semigroup A.

Section Writer_Monad.
  Context `{Monoid W}.

  (* This is used a couplle times in the next proof *)
  Ltac unfold_applicative :=
    unfold ap; unfold SG_Writer_Apply; unfold SG_Writer_ap.

  Instance Writer_Applicative : Applicative (Writer W) :=
      { applicative_apply := SG_Writer_Apply
      ; pure              := (fun _ x => (unit : W, x))
      }.
  Proof.
    { (* ap pure id = id *)
      intros A a.
      destruct a as [log_a a].
      unfold canonical_names.id.
      unfold_applicative.
      now rewrite left_identity.
    }
    { (* ap_homomorphism *)
      intros A B f a.
      unfold_applicative.
      now rewrite left_identity.
    }
    { (* ap_interchange *)
      intros A B f a.
      unfold_applicative.
      case f.
      intros w b.
      rewrite left_identity.
      now rewrite right_identity.
    }
    { (* ap_composition *)
      intros A B C f g a.
      unfold_applicative.
      destruct f as [log_f f'].
      destruct g as [log_g g'].
      destruct a as [log_a a'].
      rewrite sg_op_associative.
      rewrite left_identity.
      now unfold Basics.compose.
    }
  Defined.

  Instance Writer_Monad : Monad (Writer W) :=
      { monad_applicative := Writer_Applicative
      ; monad_bind        := SG_Writer_Bind
      }.
  Proof.
    { (* left bind identity *)
      intros A B f x.
      unfold pure; unfold Writer_Applicative.
      unfold bind; unfold SG_Writer_Bind; unfold SG_Writer_bind.
      destruct f as [log_f f'].
      now rewrite left_identity.
    }
    { (* right bind identity *)
      intros A B f x.
      destruct x as [log_x x'].
      unfold pure; unfold Writer_Applicative.
      unfold bind; unfold SG_Writer_Bind; unfold SG_Writer_bind.
      now rewrite right_identity.
    }
  Defined.
End Writer_Monad.