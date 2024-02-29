{
  inputs = {
    nixpkgs = {
      url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    };
    flake-utils = {
      url = "github:numtide/flake-utils";
    };
    cornelis = {
      url = "github:isovector/cornelis";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    { self
    , nixpkgs
    , flake-utils
    , cornelis
    , ...
    } @ inputs : flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            cornelis.overlays.cornelis
          ];
        };
      in
      with pkgs; {
        devShell = mkShell {
          buildInputs = [
            ### Main

            pkgs.cornelis
            (pkgs.agda.withPackages (ps: [
              ps.standard-library
            ]))
            # BUG: broken
            # pkgs.haskellPackages.agda-language-server
            pkgs.ghc
            pkgs.stack
          ];
        };
    });
}
