Say you need an old Coq version, but don't want to interfere it with your other installations.

First, install opam.

Then, create a new switch:

```
opam switch -A 4.05.0 MyCoq87Switch
```

List the available versions of Coq:

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
