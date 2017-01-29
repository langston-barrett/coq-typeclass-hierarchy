# coq-typeclass-hierarchy

This project aims to bring a full-featured hierarchy of typeclasses for
functional programming to Coq, inspired by Haskell
and [PureScript][purescript-prelude].

## The Hierarchy

![Typeclass Hierarchy Inclusion Diagram](./doc/diagram.png)
 
 - Solid arrows point from the general to the specific - if there is an arrow from
`Foo` to `Bar` it means that every `Bar` is a `Foo`.
 - Green nodes are complete, with documentation and (at least one) instance(s).
 - Black nodes are defined, but have no accompanying instances or documentation.
 - Red nodes are incomplete, but planned.
 
## Installation and Usage

You can build this package using the [Nix][nix] package manager:
```
nix-build . && ls result/lib/coq/8.5/user-contrib/TypeclassHierarchy/
```
Alternatively, you can use the the standard
```
./configure && make
```

If you're using [Nix][nix], you can easily intergrate this library with your own
package's `default.nix` or `shell.nix`, and your `COQPATH` environment variable
will automatically be set correctly.
```nix
{ stdenv, coq }:
let
  coq_typeclasses = 
    pkgs.callPackage ./path/to/coq-typeclass-hierarchy/default.nix { };
in stdenv.mkDerivation {
  name = "my-coq-project";
  src = ./.;
  buildInputs = [ coq coq_typeclasses ];
  ...
}
```
Otherwise, just copy what you built to somewhere that Coq will find it.

## Documentation
Run
```
./configure && make html && firefox html/toc.html
```
to build the API documentation with `coqdoc`.
 
## Design and Related Work

Here, we'll examine the key design principles and how they differ from similar
libraries:

 * Scope: This project defines only those typeclasses that have compelling use
   cases for functional programming. This gives us slightly more than Haskell,
   but fewer than PureScript.
     - [math-classes][math-classes] is focused on building the Algebraic
       Hierarchy, rather than one for functional programming.
     - [coq-haskell](https://github.com/jwiegley/coq-haskell) brings the Haskell
       typeclasses to Coq, but also includes many other parts of the Haskell
       standard library.
     - [haskell-coq](https://github.com/domdere/haskell-coq) is also similar,
       but is limited to the Haskell typeclasses, and seems stalled at the
       moment.
 * Bundling of Laws and Functional Extensionality: The only worthwhile instances
   of typeclasses are lawful ones. Therefore, this library packages the
   interfaces (`fmap`, `bind`) together with proofs that the laws hold. However,
   some laws include assertions of function equality (think `fmap id = id`),
   which is not a native concept to Coq. Therefore, we use a Setoid which
   encodes extensional equality and allows us to use the setoid rewriting
   tactics when proving it.
     - [coq-haskell](https://github.com/jwiegley/coq-haskell) uses the function
       extensionality axiom in the limited sections where it proves the laws for
       its instances. This approach is less flexible than one based on Setoids,
       and since the library (rightly) doesn't want to require users to accept
       this axiom, the laws and interfaces are unbundled, as in Haskell. This
       causes us to lose the compile-time guarantees of Coq.

[nix]: https://nixos.org/nix/
[math-classes]: https://github.com/math-classes/math-classes
[purescript-prelude]: https://github.com/purescript/purescript-prelude
