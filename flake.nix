{
  description = "Algebraic type theory";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    unilib.url = "git+ssh://git@git.app.uib.no/Hakon.Gylterud/unilib.git?ref=elli";
    unilib.inputs.nixpkgs.follows = "nixpkgs";
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

