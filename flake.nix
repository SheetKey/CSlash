{
  description = "A Haskell project template.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";

    # Example of adding or overriding a package:
    # "example-input" should be added to the outputs,
    # i.e., "output = { self, nixpkgs, flake-utils, example-input }:"
    # exapmle-input = {
    #   url = "github:SheetKey/tigris";
    #   flake = true;
    # };

  };

  outputs = { self, nixpkgs, flake-utils }: 
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        haskellPackages = pkgs.haskell.packages.ghc910;

        packageName = "csl";

        jailbreakUnbreak = pkg:
          pkgs.haskell.lib.doJailbreak (pkg.overrideAttrs (_: { meta = { }; }));

      in {
        packages.${packageName} = # (ref:haskell-package-def)
          haskellPackages.callCabal2nix packageName self rec {
            # Dependency overrides go here
            # Ex with gi-gtk-declarative:
            # If version is broken then:
            # gi-gtk-declarative = jailbreakUnbreak haskeppPackages.gi-gtk-declarative;
            # or if tests failing: 
            # gi-gtk-declarative = pkgs.haskell.lib.dontCheck haskellPackages.gi-gtk-declarative;

            #example = haskellPackages.callCabal2nix "example" example-input { };

            # ghc = pkgs.haskellPackages.ghc_9_10_1.override {
            #   ghc-boot = haskellPackages.ghc_9_10_1;
            #   ghc-heap = haskellPackages.ghc-heap_9_10_1;
            #   template-haskell = haskellPackages.template-haskell_2_22_0_0.override {
            #     ghc-boot-th = haskellPackages.ghc-boot-th_9_10_1;
            #   };
            # };
            #base = haskellPackages.base_4_20_0_0;
          };

        defaultPackage = self.packages.${system}.${packageName};

        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            ghc
            cabal-install
            haskell-language-server
            haskellPackages.implicit-hie
            alex
            happy
          ];
          inputsFrom = builtins.attrValues self.packages.${system};
        };
      }
    );
}
