{ pkgs ? import <nixpkgs> {} }:
  pkgs.mkShell {
    buildInputs = [pkgs.ninja pkgs.opam pkgs.gmp pkgs.m4 pkgs.mpfr pkgs.pkg-config pkgs.libffi pkgs.adoptopenjdk-jre-bin pkgs.ghc pkgs.pandoc];
}

