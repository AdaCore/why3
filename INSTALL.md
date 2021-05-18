Installation instructions
=========================


Installation from a source distribution (tarball)
-------------------------------------------------

After unpacking, installation is done by

    ./configure
    make
    make install       # as super-user if needed

To also install Why3's OCaml library, do

    make byte
    make install-lib   # as super-user if needed


Installation from the git repository
------------------------------------

First run

    autoconf

to build the `./configure` file, then follow the instructions from the
section above.


Detailed instructions
---------------------

For detailed instructions and required dependencies, please see
the manual [doc/latex/manual.pdf](http://why3.lri.fr/manual.pdf), Chapter 5
[Compilation, Installation](http://why3.lri.fr/doc/install.html).
