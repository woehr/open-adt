{ nixpkgs ? import <nixpkgs> {}, compiler ? "default", doBenchmark ? false }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, base, constraints, recursion-schemes
      , row-types, stdenv, template-haskell
      }:
      mkDerivation {
        pname = "open-adt";
        version = "1.1";
        src = ./.;
        libraryHaskellDepends = [
          base constraints recursion-schemes row-types template-haskell
        ];
        homepage = "https://github.com/woehr/open-adt";
        description = "Open algebraic data types";
        license = stdenv.lib.licenses.bsd3;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  variant = if doBenchmark then pkgs.haskell.lib.doBenchmark else pkgs.lib.id;

  drv = variant (haskellPackages.callPackage f {});

in

  if pkgs.lib.inNixShell then drv.env else drv
