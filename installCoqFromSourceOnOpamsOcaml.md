# Installing Coq from source using an OCaml version provided by opam

Say you want to use Coq master, but you want to install it in a way which does not interfere with your existing Coq installation(s).

Here's one way to do this:

First, install opam (these instructions were tested with opam 2.0.3).

Start by running

```
opam update
```

to fetch the latest package metadata.

Then, run

```
opam switch list-available
```

to list the available OCaml versions, and choose an OCaml version you think will be compatible with the Coq version you're going to install.

In our example, we choose OCaml version 4.09.0, and give it the name `OnlyOcaml4.09.0`:

```
opam switch create OnlyOcaml4.09.0 4.09.0
```

Then run

```
eval $(opam env)
```

and after that, if `ocamlc --version` prints `4.09.0`, OCaml should be installed correctly.

We also need these dependencies (add `lablgtk3-sourceview3` if you want CoqIDE):

```
opam install num ocamlfind
```

Then `cd` to a directory of your choice (let's call it `$MYDIR`) and do

```
git clone git@github.com:coq/coq.git
cd coq
./configure -local
make -j4
```

where `-j4` indicates to use 4 processor cores during compilation and can be adapted depending on your machine.

After this, in any terminal where you want to use this Coq version, run the following command:

```
export PATH=$MYDIR/coq/bin/:$PATH
```

Helpful commands to test if you indeed have to version you want:

```
which coqc
coqc -v
```
