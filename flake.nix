{
  # Dev shell for this specification set: the Lean toolchain the formal layer needs
  # (ADR-0023), and the Python the document gates need, the vector gate's two
  # libraries included. PyYAML is there as well, for reading
  # .github/workflows/gates.yml: briefs and reviewers parse the workflow; no gate does.
  #
  # Lean comes from nixpkgs rather than elan so the version is pinned by flake.lock
  # and the binaries run on NixOS unpatched. Mathlib is not a dependency; if it ever
  # is, it must match this Lean version exactly (the Mathlib tag named `v<lean
  # version>`) or `lake` rebuilds it from source.
  description = "btc-policy specification gates and Lean toolchain";

  # Pinned to the revision provisiond-spec pinned on 2026-09-12: it has lean4 4.30.0
  # in the binary cache. Later nixos-unstable revisions shipped a lean4 whose install
  # step wrote to /usr/local and had no cache entry.
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/aff8a0b28396750446e5537a96461bc4facdb287";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
      python = pkgs: pkgs.python3.withPackages (ps: [ ps.argon2-cffi ps.cryptography ps.pyyaml ]);
    in {
      devShells = forAll (pkgs: {
        default = pkgs.mkShell {
          packages = [
            pkgs.lean4        # lean, lake, leanchecker
            # tools/check_*.py; argon2 + secp256k1 for check_vectors.py,
            # PyYAML for reading gates.yml
            (python pkgs)
            pkgs.git          # lake fetches dependencies over git
          ];
        };
      });

      # `nix flake check` runs the same gates CI does, the Lean build included.
      checks = forAll (pkgs: {
        # runCommandCC, not runCommand: lake compiles the gate executables' C output.
        gates = pkgs.runCommandCC "btc-policy-spec-gates"
          { nativeBuildInputs = [ (python pkgs) pkgs.bash pkgs.lean4 ]; } ''
          export HOME="$TMPDIR"
          cp -r ${self} src && chmod -R u+w src && cd src
          bash tools/check-all.sh
          touch $out
        '';
      });
    };
}
