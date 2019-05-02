
{ pkgs ? import <nixpkgs> {} }: with pkgs;

stdenv.mkDerivation {
  name = "agda-exercises";
  src = ./.;
  buildInputs = [
    haskellPackages.Agda
  ];
}
