
Interpreter for the Parsley data definition language.

Building
--------

The easiest way to get the dependencies is via opam:

https://opam.ocaml.org/

Ensure your opam is up-to-date before installing the dependencies:

```
$ opam update && opam upgrade
$ opam install menhir dune cmdliner yojson ppx_deriving_yojson
```

Then,
```
$ make
```
should leave the compiler executable in `./parsleyc.exe`.

Documentation
-------------

The Parsley language is documented in a [reference
manual](doc/readme.adoc) and a [tutorial](doc/tutorial/overview.adoc)
explains its use for some well-known formats.
