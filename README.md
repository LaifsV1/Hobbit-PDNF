[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.11128050.svg)](https://doi.org/10.5281/zenodo.11128050)

# Pushdown Normal-Form Bisimulation Tool

`Hobbit-PDNF` is a bounded verification tool for bisimulation of higher-order terms based on [`Hobbit`](https://github.com/LaifsV1/Hobbit). 

It implements [*Pushdown Normal-Form Bisimulation*](https://arxiv.org/pdf/2311.01325) from the paper published at LICS 2024. It takes inspiration from *Pushdown Systems* to design a *Stackless Labelled Transition System* without loss of precision, which sits at the core of this verification tool. By being *stackless*, the technique is fully abstract for contextual equivalence while also decidable for a class of program terms that can reach configurations of unbounded size, so long as the source of unboundedness is the call stack.

A script is provided to run all the examples:
```
bash run-tests.sh
```
To run the tool on specific examples:
```
./hobbit_pdnf.native -i <path>
```
## Examples
This repository contains 140 equivalences and 78 inequivalences. Of those, 11 equivalences with a `pdnf_` prefix are new examples that implement instances of the *well-bracketed state change* problem (10 inspired by Event Handlers in Android, JavaScript, Java Swing, jQuery, and the DOM Framework; and 1 based on a simplification of a CDMA-WLAN handoff protocol). *Well-bracketed state change* is a difficult problem for verification tools, which showcases our tool's ability to fully-automatically handle problems of unbounded stack.

Examples can be found under `programs/equiv` for equivalences and `programs/inequiv` for inequivalences. Except for those marked with a `pdnf_` prefix, all examples were obtained from [`Hobbit`](https://doi.org/10.1007/978-3-030-99527-0_10).


## Installation

Instructions below were tested for Linux and macOS. `opam` is not yet officially supported for Windows.

Dependencies:
- OCaml 4.08+ with `ocamlbuild`
- Opam
- Menhir
- Z3 with OCaml bindings

### Installing OCaml's Package Manager `opam`

All dependencies are obtainable through OCaml's official package manager [`opam`](http://opam.ocaml.org/doc/Install.html). Installation of `opam` is system specific so you may need to refer to their website linked above. Instructions for some popular systems are listed below:
#### Ubuntu
```
add-apt-repository ppa:avsm/ppa
apt update
apt install opam
```
#### Fedora, CentOS and RHEL
```
dnf install opam
```
#### macOS
```
# Homebrew
brew install gpatch
brew install opam

# MacPort
port install opam
```

### Initialising `opam`

`opam` needs to be set up after installation, and this may be system dependent. First one needs to initialise it:
```
opam init
```
After initialisation, one has to create the switch to a specific compiler. Any version 4.08 and over works. The command below uses `4.08.1`, but one can use the latest version listed.
```
opam switch create 4.08.1
```
If this does not work, it could be because `opam` is missing a dependency. Depending on how minimal the installation of the system is, one may have to install many dependencies. You may need to check the error messages to know what is missing. In our experience, these are the dependencies typically missing e.g. for Ubuntu:
```
apt install build-essential
apt install gcc
apt install bubblewrap
```
The above correspond to `make`, `gcc` and `bwrap`, which are often missing in fresh installations.

Finally, initialising `opam` updates your `~/.profile` file, so you may have to source it on e.g. Ubuntu:
```
source ~/.profile
```

### Installing dependencies

With `opam` set up, installing dependencies becomes very easy.
```
opam install ocamlbuild
opam install menhir
opam install z3
```
Note that Z3 takes a long time to install.

With all dependencies installed and `~/.profile` sourced, call the make file:
```
make
```
This produces a `pdnf_bisim.native` binary.
