{
  description = "Custom Representations of Inductive Families";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
    let 
      pkgs = nixpkgs.legacyPackages.${system};
      agda = pkgs.agda.withPackages (ps: with ps; [
        # NOTE: keep up-to-date with agda-lib file
        standard-library
      ]);
    in {
      formatter = pkgs.nixpkgs-fmt;

      devShell = pkgs.mkShell {
        buildInputs = with pkgs; [
          # Idris build deps
          gnumake
          gcc
          coreutils
          gmp
          chez
          # Agda
          agda
        ];

        shellHook = ''
          export PATH="$HOME/.pack/bin:$PATH"
        '';
      };
    });
}
