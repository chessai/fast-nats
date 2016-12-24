{ mkDerivation, base, stdenv }:
mkDerivation {
  pname = "fast-nats";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [ base ];
  description = "Natural Numbers with no overhead";
  license = stdenv.lib.licenses.mit;
}
