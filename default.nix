{ mkDerivation, base, stdenv, ghc-mod }:
mkDerivation {
  pname = "fast-nats";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [ base ];
  buildDepends = [ ghc-mod ];
  description = "Natural Numbers with no overhead";
  license = stdenv.lib.licenses.mit;
}
