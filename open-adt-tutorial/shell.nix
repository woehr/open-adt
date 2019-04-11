{ nixpkgs ? import <nixpkgs> {}, compiler ? "default", doBenchmark ? false }:

let

  inherit (nixpkgs) pkgs;

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  open-adt = haskellPackages.callCabal2nix "open-adt" ../open-adt {};

  f = { mkDerivation, base, constraints, deriving-compat
      , recursion-schemes, row-types, stdenv, template-haskell
      }:
      mkDerivation {
        pname = "open-adt-tutorial";
        version = "1.1";
        src = ./.;
        isLibrary = true;
        isExecutable = true;
        libraryHaskellDepends = [
          base constraints deriving-compat open-adt recursion-schemes
          row-types template-haskell
        ];
        executableHaskellDepends = [ base ];
        homepage = "https://github.com/woehr/open-adt";
        description = "Open algebraic data type examples";
        license = stdenv.lib.licenses.bsd3;
      };

  variant = if doBenchmark then pkgs.haskell.lib.doBenchmark else pkgs.lib.id;

  drv = variant (haskellPackages.callPackage f {});

in

  if pkgs.lib.inNixShell then drv.env else drv
