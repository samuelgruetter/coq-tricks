Say you need an old Coq version, but don't want it to interfere with your other installations.

First, install opam (these instructions were tested with opam 1.2.2, opam 2 commands are given as well where they differ).

Start by running

```
opam update
```

to fetch the latest package metadata.

Then, run

```
# opam 1:
opam switch
# opam 2:
opam switch list-available
```

to list the available OCaml versions, and choose an OCaml version you think will be compatible with the Coq version you're going to install.

In our example, we choose OCaml version 4.05.0, and give the name `MyCoq87Switch` to the new switch we're creating:

```
# opam 1:
opam switch -A 4.05.0 MyCoq87Switch
# opam 2:
opam switch create MyCoq87Switch 4.05.0
```

This will download and install OCaml. Then, list the available versions of Coq:

```
opam show coq
```

Pick the one you need, and pin it:

```
opam pin add coq 8.7.2
```

which will calculate the required dependencies, and ask you if you want to install all of it. Answer `Y`.

After this, in any terminal where you want to use this old Coq version, run the following two commands:

```
# opam 1:
opam switch MyCoq87Switch
eval `opam config env`
# opam 2:
opam switch MyCoq87Switch
eval $(opam env)
```

Helpful commands to test if you indeed have to version you want:

```
which coqc
coqc -v
```
