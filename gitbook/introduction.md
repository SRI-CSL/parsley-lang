# Introduction

# Installation

- Install opam

- `opam install menhir dune`

- Clone the parsley-lang repo `git clone git@github.com:SRI-CSL/parsley-lang.git`

- `cd parsley-lang`

- `make`

You should now see a file `parsleyc.exe` in `parsley-lang/_build/default/src`. 

This is the executable we will use to run the Parsley language type checker. The type checker takes one command line argument--a Parsley syntax file. 

Let us try this on the files in the example folder `test/lang/examples.ply`.

