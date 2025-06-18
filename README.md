# Nominal-SSProve Project Template
This repository serves as a project template for getting started with [Nominal-SSProve](https://github.com/MarkusKL/nominal-ssprove).
Installation instructions are found below, and the file [`theories/Guide.v`](https://github.com/MarkusKL/nominal-ssprove-template/blob/main/theories/Guide.v) shows how to
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
3. Enable flakes in nix by appending the local nix config file with the following command:
   ```
   echo 'experimental-features = nix-command flakes' >> ~/.config/nix/nix.conf
   ```
4. Run `nix develop` to install Rocq dependencies and to enter a development shell.
   Exit the development shell with command `exit`.

## Getting Started

After following the installation instructions use `nix develop` to enter the development shell.
The development shell supports CoqIDE, vim (with coq-tail installed) and vscode
(to be installed separately and requires the VsCoq extension).

CoqIDE is easiest to get started with for users that are new to Rocq.
Open the guide file in CoqIDE using `coqide theories/Guide.v`.

## Next Steps

There are many possible next steps from this point. Here are a few suggestions:
* Read more about SSProve in the [README](https://github.com/ssprove/ssprove) and [DOC](https://github.com/SSProve/ssprove/blob/main/DOC.md).
* Explore other [examples in Nominal-SSProve](https://github.com/MarkusKL/nominal-ssprove/tree/master/theories/Example) and [examples in SSProve](https://github.com/SSProve/ssprove/tree/main/theories/Crypt/examples).
* Begin to formalize a cryptographic argument of your own.
