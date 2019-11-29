Instructions to build TryWhy3
-----------------------------

  * Install Ace

      - get the sources of Ace and put them in directory `src/trywhy3/`


            cd src/trywhy3
            git clone git://github.com/ajaxorg/ace-builds.git

      - copy the `mode-why3.js` file to the `ace-builds/src-min-noconflict/` directory:

            cp mode-why3.js ace-builds/src-min-noconflict

  * Install Alt-Ergo

      - get the sources of Alt-Ergo 2.0 and put them in directory `src/trywhy3/`,
        e.g., in `src/trywhy3/alt-ergo/`

            cd src/trywhy3
            wget http://alt-ergo.ocamlpro.com/http/alt-ergo-2.0.0/alt-ergo-2.0.0.tar.gz
            tar xzf alt-ergo-2.0.0.tar.gz
            mv alt-ergo-2.0.0 alt-ergo

      - apply the patch `alt-ergo.patch`

            cd alt-ergo
            patch -p1 < ../alt-ergo.patch

      - compile Alt-Ergo

            ./configure
            make byte

  * If necessary, change the following line of `Makefile.in` to point to Alt-Ergo sources

        ALTERGODIR=src/trywhy3/alt-ergo

  * [optional] If you want to build a standalone trywhy3 that can be
    run without a web server, the example files must be present at
    compile time. See the step 'To add predefined examples' in the
    'customization' section below and populate the `examples/`
    directory of the trywhy3 source directory accordingly *before*
    building trywhy3.

  * Compile with

        make trywhy3

  * You can build a package with

        make trywhy3_package

    this creates a tarball containing a directory `trywhy3/` which you can put on a web server.
    You may want to add a symbolic link from `index.html` to `trywhy3.html` (or rename the file).

Customization
-------------

  * Install a file `trywhy3_help.html` that will be shown when clicking
    the help button.

  * To change the theme used by the ace editor widget, add the
    relevant `theme-*.js` file to the `ace-builds/src-min-noconflict/`
    directory and update the variable definition at the top of the
    `trywhy3.html` file.

  * To change the look and feel of the rest of the application, edit
    the file `trywhy3_custom.css`.

  * To add some predefined examples, put some `.mlw` or `.why` files in the
    `examples/` subdirectory and generate an index as follows:

        cp some_file.mlw examples/
        cd examples/
        ../gen_index.sh *.mlw > index.txt

  * [optional] If you want trywhy3 to only use its embedded files,
    change the variable declaration `var load_embedded_files = false;`
    to `var load_embedded_files = true;` in the header section of
    `trywhy3.html`.

    Note that this is the default behavior when `trywhy3.html` is opened from
    a `file://` URL rather than a `http(s)://` URL, regardless of the value of
    the `load_embedded_files` variable.
