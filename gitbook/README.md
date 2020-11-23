# Introduction

To open the manuals on gitbook, just run the following: 

`docker run --rm -v "$PWD/gitbook:/gitbook" -p 4000:4000 billryan/gitbook gitbook serve` 

If you point your browser to `localhost:4000` you should see the generated documentation there.

If you wish to use a pdf version of the documentation, you can generate is by running the following command:

`docker run --rm -v "$PWD/gitbook:/gitbook" -p 4000:4000 billryan/gitbook gitbook pdf`

A file called `book.pdf` should have been generated in the gitbook folder.
