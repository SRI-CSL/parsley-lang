
Syntax and parser for the Parsley data definition language.

Building
--------

The easiest way to get the dependencies is to install opam:

https://opam.ocaml.org/

Then, install the dependencies using opam:

```
$ opam install menhir dune
```

Then,
```
$ make
```
should build the compiler executable in `_build/default/src/parsleyc.exe`.


Using our Docker Container
---------

Our Parsley repository also includes a `Dockerfile`. You can follow the following steps to use the Docker container to test the Parsley language.

- Clone the repo and `cd` into it.
```
$ git clone git@github.com:SRI-CSL/parsley-lang.git
```

- Build the Docker container.
```
$ docker build -t parsley/v1 .
```

- Connect to the Docker container.

```
$ docker run -it parsley/v1
```

- In the Docker shell you should see a `parsleyc.exe` executable and a `test` folder with `.ply` files you can test the executable against.
