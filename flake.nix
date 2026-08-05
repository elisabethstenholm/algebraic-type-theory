{
  description = "Algebraic type theory";
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    unilib.url = "git+ssh://git@git.app.uib.no/Hakon.Gylterud/unilib.git?ref=elli";
    nixpkgs.follows = "unilib/nixpkgs";
  };

  outputs = { self, nixpkgs, flake-utils, unilib }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        theLib = pkgs.agdaPackages.mkDerivation {
          meta = {};
          pname = "Algebraic type theory";
          version = "1.0.0";
          src = ./.;
          buildInputs = [
            unilib.packages.${system}.default
          ];
        };
      in
        {
          packages.default = theLib;
        });
}

