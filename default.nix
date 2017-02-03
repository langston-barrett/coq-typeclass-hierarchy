{
  pkgs ? import <nixpkgs> { }
}:

# To use: run `nix-shell` or `nix-shell --run "exec zsh"`
# https://nixos.org/wiki/Development_Environments
# http://nixos.org/nix/manual/#sec-nix-shell

let
  # Pin a nixpkgs version
  pinned_pkgs = import (pkgs.fetchFromGitHub {
    owner  = "NixOS";
    repo   = "nixpkgs";
    # This is the commit that included math-classes. Thanks @vbgl!
    rev    = "d486fb053b3f148e5989d6cd3e07a69eaf75d0bf";
    sha256 = "14s283bwh77266zslc96gr7zqaijq5b9k4wp272ry27j5q8l3h4i";
  }) {};

  coq = pinned_pkgs.coq_8_5;

in with pinned_pkgs; stdenv.mkDerivation {
  name = "coq${coq.coq-version}-typeclass-hierarchy";
  src = ./.;
  buildInputs = [ coq coqPackages_8_5.math-classes ];
  enableParallelBuilding = true;
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  shellHook = ''
    export COQPATH=$COQPATH:$PWD
  '';

  meta = with stdenv.lib; {
    homepage = https://github.com/siddharthist/coq-typeclass-hierarchy;
    description = "A full-featured hierarchy of typeclasses for functional programming in Coq";
    maintainers = with maintainers; [ siddharthist ];
    platforms = coq.meta.platforms;
  };
}
