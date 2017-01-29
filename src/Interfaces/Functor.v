Require Import Coq.Program.Basics.
Require Import MathClasses.interfaces.canonical_names.
Require Import TypeclassHierarchy.Util.FunctionSetoid.

(* math-classes uses (=) to denote equivalence, but we will use it for equality *)
Infix "=" := eq : type_scope.
Notation "(=)" := eq (only parsing) : mc_scope.
Notation "( x =)" := (eq x) (only parsing) : mc_scope.
Notation "(= x )" := (λ y, eq y x) (only parsing) : mc_scope.
(* Notation "(≠)" := (λ x y, ¬x = y) (only parsing) : mc_scope. *)
(* Notation "x ≠ y":= (¬x = y): type_scope. *)
(* Notation "( x ≠)" := (λ y, x ≠ y) (only parsing) : mc_scope. *)
(* Notation "(≠ x )" := (λ y, y ≠ x) (only parsing) : mc_scope. *)

(**
 A functor contains data in such a way that a function can be applied uniformly
 across the contained objects.

 The functor follows three (classical) laws:
   - fmap id = id
   - fmap (g ∘ h) = (fmap g) ∘ (fmap h)

 We additionally require that fmap is proper with respect to the equivalence
 relation on functions, i.e. if f and g are extensionally equal, fmap f and
 fmap g are as well.

 A lot of the notation (e.g. setoid/extensional equality) is desugared here,
 because Coq has trouble inferring the types.

 We use Type rather than Set, as Functors must live in Set+1, and we want to be able to compose Functors.
 *)

Class Functor (F : Type -> Type) : Type :=
  { fmap : forall {X Y : Type}, (X -> Y) -> F X -> F Y
  ; fmap_proper :
      forall {A B : Type}, Proper ((@extensional_equality A B) ==>
                             (@extensional_equality (F A) (F B))) (@fmap A B)
  ; fmap_identity :
      forall {A : Type}, @extensional_equality (F A) (F A) (@fmap A A id) id
  ; fmap_composition :
      forall {A B C: Type} (h : A -> B) (g : B -> C),
        @extensional_equality (F A) (F C) (@fmap A C (g ∘ h)) (@fmap B C g ∘ @fmap A B h)
  }.
Arguments fmap {F} {Functor} {X} {Y} _ _.

(**
 An applicative is a functor that also allows for both applying functions inside
 the functor to arguments inside the functor, and embedding arbitrary objects in
 the functor.

 In addition to the functor laws, an applicative follows three others:
   - ap (pure id) v = v
   - ap (pure f) (pure x) = pure (f x)
   - ap u (pure y) = ap (pure (fun f => f y)) u
   - ap u (ap v w) = ap (pure (∘)) (ap u (ap v w))

 As always, lot of the notation (e.g. setoid/extensional equality) is desugared
 to reduce the need for (slow and somewhat unreliable) type inference.
 *)

Class Applicative (F : Type -> Type) : Type :=
  { applicative_functor : Functor F
  ; pure : forall {A : Type}, A -> F A
  (* ; pure_proper : *)
  (*     forall {A B : Type}, Proper (@extensional_equality A (F A)) (@pure A) *)
  ; ap   : forall {A B : Type}, F (A -> B) -> F A -> F B
  ; ap_identity :
      forall {A : Type} (a : F A), @ap A A (@pure (A -> A) id) a = a
  ; ap_homomorphism :
      forall {A B : Type} (f : A -> B) (a : A), @ap A B (pure f) (pure a) = pure (f a)
  ; ap_interchange : 
      forall {A B : Type} (f : F (A -> B)) (a : A),
        @ap A B f (pure a) = @ap (A -> B) B (pure (fun g => g a)) f
  ; ap_composition :
      forall {A B C : Type} (f : F (A -> B)) (g : F (B -> C)) (a : F A),
        ap g (ap f a) = ap (ap (ap (pure (∘)) g) f) a
  }.