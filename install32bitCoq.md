
## Installing 32bit Coq/CoqIDE on Fedora 25

Most of Coq's memory is used for pointers, and if each pointer takes only 32bit instead of 64bit, you can save a lot of memory. The only downside of the 32bit mode is that Coq can't use more than `2^32` bytes of memory (4GB), but that's usually enough.

If you have a 64bit machine and a 64bit OS and install Coq, you'll get the 64bit Coq, but by compiling OCaml and Coq from source with the right options, you can get 32bit Coq on a 64bit system:


### Prerequisites

For OCaml:

    sudo dnf install glibc-devel.i686

For CoqIDE:

    sudo dnf install gtksourceview2-devel.i686 gtk2-devel.i686 gtk+-devel.i686 gtk+extra-devel.i686 pango-devel.i686 pcre-devel.i686 pixman-devel.i686 zlib-devel.i686 bzip2-devel.i686 libpng-devel.i686 expat-devel.i686 mesa-libEGL-devel.i686 libdrm-devel.i686 libX11-devel.i686 libxcb-devel.i686 libXau-devel.i686 libXext-devel.i686 libXdamage-devel.i686 libXfixes-devel.i686 libXxf86vm-devel.i686 mesa-libGL-devel.i686 libXrender-devel.i686 harfbuzz-devel.i686 graphite2-devel.i686 gdk-pixbuf2-devel.i686 atk-devel.i686 libxml2-devel.i686



### OCaml

(following https://github.com/ocaml/ocaml/blob/trunk/INSTALL.adoc)

    mkdir ~/tmp

    export TMPDIR=~/tmp

    mkdir ~/installs

    mkdir ~/installs/ocaml32

    cd some/dir/for/clones

    git clone git@github.com:ocaml/ocaml.git

    cd ocaml/

    git checkout 4.04.0

    ./configure -cc "gcc -m32" -as "as --32" -aspp "gcc -m32 -c" -host i386-linux -partialld "ld -r -melf_i386" -prefix ~/installs/ocaml32/

    make world

    make opt

    make opt.opt

    make install

    make clean

Run the following command whenever you want to use the 32bit OCaml/Coq/CoqIDE. It only applies to the current shell, so you can keep using other installations.

    export PATH=$PATH:~/installs/ocaml32/bin/



### Camlp5

(following https://github.com/camlp5/camlp5/blob/master/INSTALL)

    cd some/dir/for/clones

    git clone git@github.com:camlp5/camlp5.git

    cd camlp5/

    git checkout rel617

This prints the installation directory, which should automatically be the same as the ocaml installation dir:

    ./configure

    make world.opt

    make install



### lablgtk (for CoqIDE)

(following the [README](https://forge.ocamlcore.org/plugins/scmgit/cgi-bin/gitweb.cgi?p=lablgtk/lablgtk.git;a=blob_plain;f=README;hb=2e9eaac675adc36053a602935fef003d123bd4b6))

    cd some/dir/for/clones

    git clone https://forge.ocamlcore.org/anonscm/git/lablgtk/lablgtk.git

    cd lablgtk

    git checkout 2e9eaac675adc36053a602935fef003d123bd4b6

By default, `pkg-config` looks at `/usr/lib64` and `/usr/share/pkgconfig`. To make sure it looks at the 32bit header files (located at `/usr/lib`), we have to set the following environment var (which is typically not set before):

    export PKG_CONFIG_LIBDIR=/usr/lib/pkgconfig:/usr/share/pkgconfig
    
    ./configure --prefix /home/sam/installs/ocaml32/lib --with-libdir=/home/sam/installs/ocaml32/lib --with-gtksourceview2=yes CC='gcc -m32'

    make world

Since the new `make install` needs ocamlfind, which is only installed if you have opam, we have to use old-install:

    make old-install
    
Copy some files that old-install forgot to copy:

    cp src/*.so ~/installs/ocaml32/lib/lablgtk2/
    


### Coq

(following https://github.com/coq/coq/blob/V8.5pl2/INSTALL and https://github.com/coq/coq/blob/V8.5pl2/INSTALL.ide)

    cd some/dir/for/clones
    git clone git@github.com:coq/coq.git
    cd coq
    git checkout V8.5pl2

Optional, to get the Ltac profiler:

```
wget https://raw.githubusercontent.com/coq/opam-coq-archive/master/core-dev/packages/coq.8.5.dev%2Bltacprof/files/ltac-profiling-0.9-8.5.patch
patch -p1 < ltac-profiling-0.9-8.5.patch
```

```
./configure -prefix ~/installs/ocaml32 -lablgtkdir ~/installs/ocaml32/lib/lablgtk2 -arch i686
```

```
make world
```

```
make install
```


## Installation of some more tools


### Ocamlbuild 

(following https://github.com/ocaml/ocamlbuild)

    cd some/dir/for/clones

    git clone git@github.com:ocaml/ocamlbuild.git

    cd ocamlbuild/

This one automatically sets the installation dir to the same as the Ocaml's:

    make configure

    make

    make install



### Menhir

Download source from http://gallium.inria.fr/~fpottier/menhir/, unpack.

    cd menhir-20170101/

    make PREFIX=/home/sam/installs/ocaml32/ USE_OCAMLFIND=false all

    make PREFIX=/home/sam/installs/ocaml32/ install

    make PREFIX=/home/sam/installs/ocaml32/ USE_OCAMLFIND=false all




