{ pkgs ? import <nixpkgs> {} }:
let
  open-adt          = pkgs.haskellPackages.callCabal2nix "open-adt"
                        ./open-adt {};
  open-adt-tutorial = pkgs.haskellPackages.callCabal2nix "open-adt-tutorial"
                        ./open-adt-tutorial { inherit open-adt; };
in
  { inherit open-adt open-adt-tutorial; }
