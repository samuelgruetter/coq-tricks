# Installing Coq 8.9 with nix instead of opam

Installing locally, in a way which doesn't interfere with any other installations, and does not require opam.

First, install [nix](https://nixos.org/nix/).

Next, clone coq and `cd` into it:

```
mkdir /home/sam/installs/CoqV8.9/
cd /home/sam/installs/CoqV8.9/
git clone --branch V8.9.0 --depth=1 git@github.com:coq/coq.git
cd coq/
```

Then, open a nix shell (which will download, install and put into `$PATH` all dependencies as specified by `./default.nix`):

```
nix-shell
```

Inside that nix shell, do

```
./configure -local
make -j2
```

Done!

Now, in any terminal (does not have to be a nix shell), to use this coq version, run

```
export PATH=/home/sam/installs/CoqV8.9/coq/bin/:$PATH
```
