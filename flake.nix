# derived from ssprove/flake.nix
{
  inputs = {
    nixpkgs.url        = github:nixos/nixpkgs;
    flake-utils.url    = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    let
      nominalsspPkg = { lib, mkCoqDerivation, coq
                  , equations, extructures, deriving
                  , mathcomp-analysis, mathcomp-ssreflect
                  , ssprove, fetchFromGitHub }:
        mkCoqDerivation {
          pname = "nominal-ssprove";
          owner = "MarkusKL";
          version = "1.1.7";
          src = fetchFromGitHub {
            owner = "MarkusKL";
            repo = "nominal-ssprove";
            rev = "v1.1.7";
            hash = "sha256-T2P07TFxtkx1mBsIKBcYJl76RR/fEmLKSgGu0v8mTUo=";
          };
          propagatedBuildInputs = [ ssprove ];
          meta = {
            description = "Extending SSProve with nominals";
            license = lib.licenses.mit;
          };
        };
      localProject = { lib, mkCoqDerivation, coq
                  , equations, extructures, deriving
                  , mathcomp-analysis, mathcomp-ssreflect
                  , ssprove, fetchFromGitHub, coqPackages_8_19 }:
        mkCoqDerivation {
          pname = "local-project";
          owner = "unknown";
          version = "0.0.1";
          src = ./.;
          propagatedBuildInputs = [
            coqPackages_8_19.nominal-ssprove
          ];
        };
      vimPkg = { vim_configurable, vimPlugins }:
        (vim_configurable.customize {
            name = "vim";
            vimrcConfig = {
              packages.myVimPackage.start = with vimPlugins; [
                Coqtail
                vim-unicoder
              ];
              customRC = ''
                syntax on
                colorscheme default
                set number
                let &t_ut='''
                set tabstop=2
                set shiftwidth=2
                set softtabstop=2
                set expandtab
                set backspace=indent,eol,start
                filetype plugin on
                filetype indent on
                hi def CoqtailChecked      ctermbg=7
                hi def CoqtailSent         ctermbg=3
                hi def link CoqtailError   Error
                hi def link CoqtailOmitted coqProofAdmit

                " Additional vim config here:

              '';
            };
        });
    in {
      overlays.default = final: prev: {
        coqPackages_8_19 = prev.coqPackages_8_19.overrideScope (self: super: {
          # version fix from SSProve /flake.nix
          mathcomp = super.mathcomp.override { version = "2.2.0"; };
          nominal-ssprove = self.callPackage nominalsspPkg {};
          local-project = self.callPackage localProject {};
        });
      };
    } // flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ self.overlays.default ];
        };
      in {
        packages.default = pkgs.coqPackages_8_19.local-project;
        devShells.default = pkgs.stdenv.mkDerivation {
          name = "nominal-ssprove-shell";
          buildInputs = [
            pkgs.glibcLocales
            pkgs.coqPackages_8_19.coq
            pkgs.coqPackages_8_19.ssprove
            pkgs.coqPackages_8_19.nominal-ssprove
            pkgs.coqPackages_8_19.vscoq-language-server
            pkgs.coqPackages_8_19.coqide
            (pkgs.callPackage vimPkg {})
          ];
        };
      });
}
