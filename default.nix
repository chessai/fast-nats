{ mkDerivation, base, singletons, stdenv }:
mkDerivation {
  pname = "fast-nats";
  version = "0.1.0.1";
  src = ./.;
  libraryHaskellDepends = [ base singletons ];
  description = "Natural Numbers with no overhead";
  license = stdenv.lib.licenses.mit;
}
