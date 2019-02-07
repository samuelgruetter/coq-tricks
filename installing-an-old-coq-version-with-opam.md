Say you need an old Coq version, but don't want it to interfere with your other installations.

First, install opam (these instructions were tested with opam 1.2.2).

Then, run

```
opam switch
```

to list the available OCaml versions, and choose an OCaml version you think will be compatible with the Coq version you're going to install.

In our example, we choose OCaml version 4.05.0, and give the name `MyCoq87Switch` to the new switch we're creating:

```
opam switch -A 4.05.0 MyCoq87Switch
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
opam switch MyCoq87Switch
eval `opam config env`
```

Helpful commands to test if you indeed have to version you want:

```
which coq
coqc -v
```
