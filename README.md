# GDB
WIP port of GDB (v7.5.1 at the moment) to AmigaOS4.

You need crosscompiler with GCC 8.4.0 minimum and the latest SDK.

Download repo and:

```
cd gdb-7.5.1
mkdir gdb-build
cd gdb-build
../configure --host=ppc-amigaos --target=ppc-amigaos --build=x86_64 --disable-nls --disable-werror
```
