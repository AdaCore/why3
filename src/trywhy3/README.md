Instructions to build TryWhy3
-----------------------------

  * Install Ace

      - put the sources of Ace in directory `src/trywhy3` and copy
        the `mode-why3.js` file into them:

            cd src/trywhy3
            git clone git://github.com/ajaxorg/ace-builds.git
            cp mode-why3.js ace-builds/src-min-noconflict/

  * Install Alt-Ergo

      - put the sources of Alt-Ergo in directory `src/trywhy3` and
        compile the JavaScript worker:

            cd src/trywhy3
            git clone git://github.com/OCamlPro/alt-ergo.git
            cd alt-ergo
            opam exec make js-worker
            cp alt-ergo-worker.js ..

      - alternatively, recover `alt-ergo-worker.js` from a GitHub workflow
        at https://github.com/OCamlPro/alt-ergo/actions/workflows/build_js.yml
        and put it in directory `src/trywhy3`.

  * Compile with

        make trywhy3

  * Test by opening http://0.0.0.0:8080/trywhy3.html after starting a local server:

        cd src/trywhy3
        python3 -m http.server 8080

  * (Optional) Build a package with

        make trywhy3.tar.gz

    This creates a tarball containing a directory `trywhy3/` which you
    can put on a web server. You may want to add a symbolic link from
    `index.html` to `trywhy3.html` (or rename the file).

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

  * To add some predefined examples, put some `.mlw` files in the
    `examples/` subdirectory and generate an index as follows:

        cp some_file.mlw examples/
        cd examples/
        ../gen_index.sh *.mlw > index.txt
