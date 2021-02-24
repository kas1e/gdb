# GDB
WIP port of GDB (v7.5.1 at the moment) to AmigaOS4.

To build you need:

1. cross-compiler with GCC 8.4.0 minimum.
2. latest SDK.
3. termcap library: http://os4depot.net/share/development/library/misc/termcap.lha

Download repo and:

```
cd gdb-7.5.1
mkdir gdb-build
cd gdb-build
../configure --host=ppc-amigaos --target=ppc-amigaos --build=x86_64 --disable-nls --disable-werror --disable-sim LDFLAGS="-lunix"
make -j4
```
