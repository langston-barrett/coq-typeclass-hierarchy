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
 An apply is a halfway point between functor and applicative/bind. It's not very
 useful in and of itself, but exists to unify the notation between binds and
 applicatives.

 In addition to the functor laws, an apply follows one more:
   - ap g (ap f a) = ap (ap (fmap (∘) g) f) a
 *)

Class Apply (F : Type -> Type) : Type :=
  { apply_functor : Functor F
  ; ap   : forall {A B : Type}, F (A -> B) -> F A -> F B
  ; apply_composition :
      forall {A B C : Type} (f : F (A -> B)) (g : F (B -> C)) (a : F A),
        @ap B C g (@ap A B f a) = @ap A C (ap (fmap (∘) g) f) a
  }.

(**
 An applicative is a functor that also allows for both applying functions inside
 the functor to arguments inside the functor, and embedding arbitrary objects in
 the functor.

 In addition to the apply laws, an applicative follows three others:
   - ap (pure id) v = v
   - ap (pure f) (pure x) = pure (f x)
   - ap u (pure y) = ap (pure (fun f => f y)) u
   - ap u (ap v w) = ap (pure (∘)) (ap u (ap v w))

 As always, lot of the notation (e.g. setoid/extensional equality) is desugared
 to reduce the need for (slow and somewhat unreliable) type inference.

 In particular, we often have the following let clause:
 "app := @ap F applicative_apply" which specializes the "ap" method to the
 current functor. If this is confusing, just think of "app" as "ap".
 *)

Class Applicative (F : Type -> Type) : Type :=
  { applicative_apply : Apply F
  ; pure : forall {A : Type}, A -> F A
  (* ; pure_proper : *)
  (*     forall {A B : Type}, Proper (@extensional_equality A (F A)) (@pure A) *)
  ; ap_identity :
      forall {A : Type} (a : F A),
      @ap F applicative_apply A A (@pure (A -> A) id) a = a
  ; ap_homomorphism :
      forall {A B : Type} (f : A -> B) (a : A),
      let app := @ap F applicative_apply A B
      in @app (@pure (A -> B) f) (@pure A a) = @pure B (f a)
  ; ap_interchange :
      forall {A B : Type} (f : F (A -> B)) (a : A),
      let app := @ap F applicative_apply
      in @app A B f (pure a) = @app (A -> B) B (@pure ((A -> B) -> B) (fun g => g a)) f
  ; ap_composition :
      forall {A B C : Type} (f : F (A -> B)) (g : F (B -> C)) (a : F A),
      let app := @ap F applicative_apply
      (* TODO: fill in more implicit args. I don't understand the types :( *)
      in app B C g (app A B f a) = app A C (ap (ap (pure (∘)) g) f) a
  }.

(**
 A bind is an apply with an additional operation that takes the output of
 one computation and feeds it into the next, composing the two in a chain.

 In addition to the apply laws, binds must follow one other:
   - bind (bind x f) g = bind x (fun y => bind (f y) g)
 *)

Class Bind (F : Type -> Type) : Type :=
  { bind_apply : Apply F
  ; bind : forall {A B : Type}, F A -> (A -> F B) -> F B
  ; bind_associative :
      forall {A B C : Type} (x : F A) (f : A -> F B) (g : B -> F C),
      @bind B C (@bind A B x f) g = @bind A C x (fun y => @bind B C (f y) g)
  }.

(**
 A monad is a lot of things, but really just an applicative and a bind together.
 It supports chaining of functions, and embedding of objects into the type
 constructor.

 In addition to the laws provided by apply and bind, it has identities:
  - bind (pure x) f = f x
  - bind x pure = x
 *)

Class Monad (M : Type -> Type) : Type :=
  { monad_applicative : Applicative M
  ; monad_bind     : Bind M
  ; monad_id_left  : forall {A B : Type} (f : A -> M B) (x : A), bind (pure x) f = f x
  ; monad_id_right : forall {A B : Type} (f : A -> M B) (x : M A), bind x pure = x
  }.