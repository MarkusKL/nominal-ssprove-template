# Nominal-SSProve Project Template
This repository serves as a project template for getting started with Nominal-SSProve.
Installation instructions are found below, and the file `theories/Guide.v` shows how to
use Nominal-SSProve by working through an example. To start your own project, simply copy,
clone, or fork this repository and create new files in `theories/`.

## Installation Instructions

Nominal-SSProve is easiest to install with the [nix package manager](https://nixos.org/)
following the steps below.

1. Install the [nix package manager](https://nixos.org/).
   Check if nix is available with `nix --version`.
2. Add Rocq build caches, so that the Rocq dependencies are downloaded rather than built locally.
   To add the build caches, run the following commands:
   ```
   nix-shell -p cachix --command "cachix use coq"
   nix-shell -p cachix --command "cachix use coq-community"
   nix-shell -p cachix --command "cachix use math-comp"
   ```
   It is recommended to add build caches to significantly speed up initial environment setup time.
   Building locally takes around an hour, while downloading from cache takes around five minutes.
3. Run `nix develop` to install Rocq dependencies and to enter a development shell.
   Exit development shell with command `exit`.

## Getting started

After following the installation instructions use `nix develop` to enter the development environment.
The development environment supports CoqIDE, vim (with coq-tail installed) and vscode
(to be installed separately and requires the VsCoq extension).

CoqIDE is easiest to get started with for users that are new to Rocq.
Open the guide in CoqIDE using `coqide theories/Guide.v`.

## Next steps

There are many possible next steps from here. Here are a few suggestions:
* Read more about SSProve in the README (..) and DOC (..).
* Explore other examples in Nominal-SSProve (..) and SSProve (..)
* Begin to formalize a cryptographic argument of your own.
