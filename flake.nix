{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = nixpkgs.legacyPackages.${system};
      in {
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            (agda.withPackages
              (ps: [
                ps.standard-library
                (ps.agda-categories.overrideAttrs (_: {
                  version = "master";
                  src = fetchFromGitHub {
                    repo = "agda-categories";
                    owner = "agda";
                    rev = "master";
                    #hash = "sha256-BGmIKethGvWXMuLHkIYe9V1cvDDPsNIQz1/HdpRQvCo=";
                    hash = "sha256-/h0KeRkEc1bW//P/I4p61FGFIR03W7dC//WmEDFruk0=";
                  };
                }))
              ]))
          ];
        };
      }
    );
}
