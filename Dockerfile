from ocaml/opam

# This opam docker container has a bunch of permission issues if we use any user other than root
USER root

# Dependencies for Parsley
RUN opam install -y menhir dune

# Parsley-lang Repo copied over to the root folder
COPY . /parsley-lang

# Add dune to the PATH
ENV PATH="/home/opam/.opam/4.11/bin/:${PATH}"

# Building Parsley
RUN cd /parsley-lang/ && make

# Copying over test files for users to try out
RUN cp -r /parsley-lang/test test/

# Parsleyc.exe is the Parsley type checker executable
RUN cp /parsley-lang/_build/default/src/parsleyc.exe .


