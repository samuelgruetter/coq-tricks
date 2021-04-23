Say you need an old Coq version, but don't want it to interfere with your other installations.

First, make sure you have opam installed (these instructions were tested with opam 2.0.3), and that you have the Coq repos added (you might need a command like `opam repo add coq-released https://coq.inria.fr/opam/released`).

Start by running

```
opam update
```

to fetch the latest package metadata.

```
opam show coq
```

lists all available versions.
For this example, we pick `8.4pl2`, and run

```
opam show coq.8.4pl2
```

which lists, under "Version-specific details", its supported OCaml versions (`{>= "3.11.2" & < "4.02.0"}`).

Then, run

```
opam switch list-available
```

to list the available OCaml versions, and choose an OCaml version you think will be compatible with the Coq version you're going to install.

In our example, we choose OCaml version 4.01.0, and give the name `MyCoq842Switch` to the new switch we're creating:

```
opam switch create MyCoq842Switch 4.01.0
```

This will download and install OCaml.

Next, pin the desired Coq version:

```
opam pin add coq 8.4pl2
```

which will calculate the required dependencies, and ask you if you want to install all of it. Answer `Y`.

After this, in any terminal where you want to use this old Coq version, run the following two commands:

```
opam switch MyCoq842Switch
eval $(opam env)
```

Helpful commands to test if you indeed have to version you want:

```
which coqc
coqc -v
```
