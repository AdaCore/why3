Instructions to build TryWhy3
-----------------------------

  * Compile with

        make trywhy3

  * (Optional) Build a package with

        make trywhy3.tar.gz

    This creates a tarball that can be used if the following steps are
    performed on a different machine or if only the Why3 components need
    to be updated. Do not forget about `mode-why3.js` in that case (see below).

  * Install Ace

      - download the Ace editor to directory `src/trywhy3` and
        copy the file `mode-why3.js` there:

            cd src/trywhy3
            git clone --depth=1 git@github.com:ajaxorg/ace-builds.git
            cp mode-why3.js ace-builds/src-min-noconflict/

  * Install Alt-Ergo

      - download the sources of Alt-Ergo, compile the JavaScript worker,
        and copy it to directory `src/trywhy3`:

            git clone git@github.com:OCamlPro/alt-ergo.git
            cd alt-ergo
            opam exec make js-worker
            cp alt-ergo-worker.js .../why3/src/trywhy3/

      - alternatively, recover `alt-ergo-worker.js` from a GitHub workflow
        at https://github.com/OCamlPro/alt-ergo/actions/workflows/build_js.yml

  * Test by opening http://0.0.0.0:8080/trywhy3.html after starting a local server:

        cd src/trywhy3
        python3 -m http.server 8080

  * (Optional) Build a package with

        make trywhy3-full.tar.gz

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

  * To change the default step limits, edit the `#why3-setting-dialog`
    part of `trywhy3.html`.

  * To add some predefined examples, put the files in the `examples/`
    subdirectory and modify `examples/config.json` accordingly.
