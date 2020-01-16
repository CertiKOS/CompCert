let pkgs =import <nixpkgs> {}; 
in
with pkgs;

stdenv.mkDerivation {
  name = "certikos";

  buildInputs = with ocamlPackages; [
 (callPackage ~/.nix-defexpr/channels/nixpkgs/pkgs/development/ocaml-modules/menhir { version = "20170712"; })

    camlp4
    ocaml findlib coq_8_6
    coqPackages_8_6.flocq
  ];

}
