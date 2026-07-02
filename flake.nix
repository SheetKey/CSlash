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

        haskellPackages = pkgs.haskell.packages.ghc912;

        packageName = "csl";

        jailbreakUnbreak = pkg:
          pkgs.haskell.lib.doJailbreak (pkg.overrideAttrs (_: { meta = { }; }));

        my-pkg = haskellPackages.callCabal2nix packageName self { };
        my-post-install-phase = ''
          cp llvm-targets $out/lib
          cp llvm-passes $out/lib
        '';
        my-pkg-post-install-files =
          pkgs.haskell.lib.overrideCabal my-pkg
            (old_pkg: { postInstall = (old_pkg.postInstall or "") + my-post-install-phase; });
            
      in {
        # OLD
        # packages.${packageName} = # (ref:haskell-package-def)
        #   haskellPackages.callCabal2nix packageName self rec {
        #     # Dependency overrides go here
        #     # Ex with gi-gtk-declarative:
        #     # If version is broken then:
        #     # gi-gtk-declarative = jailbreakUnbreak haskeppPackages.gi-gtk-declarative;
        #     # or if tests failing: 
        #     # gi-gtk-declarative = pkgs.haskell.lib.dontCheck haskellPackages.gi-gtk-declarative;

        #     #example = haskellPackages.callCabal2nix "example" example-input { };

        #     # ghc = pkgs.haskellPackages.ghc_9_10_1.override {
        #     #   ghc-boot = haskellPackages.ghc_9_10_1;
        #     #   ghc-heap = haskellPackages.ghc-heap_9_10_1;
        #     #   template-haskell = haskellPackages.template-haskell_2_22_0_0.override {
        #     #     ghc-boot-th = haskellPackages.ghc-boot-th_9_10_1;
        #     #   };
        #     # };
        #     #base = haskellPackages.base_4_20_0_0;
        #   };
        # END OLD
        packages.${packageName} = my-pkg-post-install-files;

        defaultPackage = self.packages.${system}.${packageName};

        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            haskell.compiler.ghc912
            # cabal-install
            haskellPackages.haskell-language-server
            # haskellPackages.implicit-hie
            haskellPackages.alex
            haskellPackages.happy

            llvm_18
          ];
          inputsFrom = builtins.attrValues self.packages.${system};
        };
      }
    );
}
