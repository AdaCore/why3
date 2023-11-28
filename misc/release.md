# Making a release

* perform a sanity check
  - check the BTS
  - check that nightly bench is OK
  - `make xml-validate-local`
    (see below: copy the dtd on the web)
  - `make trywhy3`
  - run `make detect-unused` and remove unused files
  - run `make update-doc-png` and check if some pictures need to be updated
  - check `lib/why3/META.in` (e.g., against `EXTPKGS` in `Makefile.in`)
  - check the gallery, especially the new examples (see below)

* change version number `VERSION=1.3 RELEASE=1.3.0`
  - update the first line of `configure.in` using `$RELEASE`
  - update the `version` and `release` fields in `doc/conf.py` around line 60
  - check `CHANGES.md`, add the release date
  - update the date in `doc/index.rst`

* check/update authors and copyright
  - update the content of the About dialog in `src/ide/gconfig.ml`
    around lines 680-700
  - update the `copyright` field in `doc/conf.py` around line 50
  - update `doc/foreword.rst`
  - update `src/trywhy3/trywhy3.html`
  - check headers, modify `misc/header.txt` and run `make headers` if needed

* generate documentation
  - `make doc`
    (check that the PDF manual is also generated, `doc/latex/manual.pdf`)
  - `make stdlibdoc`
  - `make apidoc`

* prepare the archive
  - make a last commit:
    ```
    git commit -am "Version $RELEASE"
    git tag $RELEASE
    ```
  - `make dist`
  - test `distrib/why3-$RELEASE.tar.gz`
  - push the commit:
    ```
    git push
    git push --tags
    ```
  - upload `distrib/why3-$RELEASE.tar.gz` to https://gitlab.inria.fr/why3/releases
    ```
    git clone git@gitlab.inria.fr:why3/releases.git why3-releases
    cd why3-releases
    cp .../distrib/why3-$RELEASE.tar.gz releases/
    git add releases/why3-$RELEASE.tar.gz
    git commit -m "Add release $RELEASE."
    git push
    ```

* upload the documentation on the web page
  ```
  DEST=/users/www-perso/projets/why3
  rm -rf $DEST/doc-$VERSION $DEST/stdlib-$VERSION $DEST/api-$VERSION
  cp share/why3session.dtd $DEST/
  cp doc/latex/manual.pdf $DEST/download/manual-$VERSION.pdf
  cp -r doc/html $DEST/doc-$VERSION
  cp -r doc/stdlibdoc $DEST/stdlib-$VERSION
  cp -r doc/apidoc $DEST/api-$VERSION
  ln -s -n -f download/manual-$VERSION.pdf $DEST/manual.pdf
  ln -s -n -f doc-$VERSION $DEST/doc
  ln -s -n -f stdlib-$VERSION $DEST/stdlib
  ln -s -n -f api-$VERSION $DEST/api
  ```

* update the main HTML page; sources are in https://gitlab.inria.fr/why3/www
  - edit `index.html`, change at least all occurrences of the version, and
    update the url for download
  - `make` (to check validity)
  - `make export`
  - update TryWhy3
    ```
    make trywhy3
    make trywhy3.tar.gz
    rm -r $DEST/try
    mkdir $DEST/try
    tar xzf trywhy3.tar.gz -C $DEST/try/ --strip-components=1
    ln -s trywhy3.html $DEST/try/index.html
    ```

* prepare the OPAM package
  - update `opam/why3{,-ide,-coq}.opam` with correct dependencies on external packages
  - clone https://github.com/ocaml/opam-repository if not already done:
    ```
    git clone git@github.com:.../opam-repository.git
    cd opam-repository/
    git remote add opam https://github.com/ocaml/opam-repository.git
    opam repository add --all-switches --kind=git local .
    ```
  - reinitialize the repository if not fresh:
    ```
    git fetch opam
    git reset --hard opam/master
    git push
    ```
  - create version directories:
    - `mkdir packages/why3/why3.$RELEASE packages/why3-coq/why3-coq.$RELEASE packages/why3-ide/why3-ide.$RELEASE`
    - copy the `opam` files from the directories of the previous release
    - reconcile with the changes from Why3's repository
  - url and checksum of `why3.tar.gz`:
    - `md5sum .../distrib/why3-$RELEASE.tar.gz`
    - update the `url` section of all three opam files
  - test opam files:
    ```
    git commit ...
    opam update local
    opam install why3 why3-ide why3-coq
    ```
  - `git push`
  - make a pull request on github

* produce the Why3 part of Toccata gallery
  - update the git repository of Toccata
  - have `GALLERYDIR` point to the sub-directory `gallery` of that git repository,
    e.g., `export GALLERYDIR=.../toccata/web/gallery`
  - in Why3 sources, run `make gallery`;
    it exports to `$GALLERYDIR` all the Why3 programs for which there is a session
  - now move to the directory `$GALLERYDIR`
  - check the examples that are currently untracked in the Toccata repository
    and update `examples.rc` accordingly
  - put the directories of the broken examples in `.gitignore`
  - run `make`; this requires to have installed the newly released Why3;
    the presence of `.prehtml.new` files means that something went wrong,
    hopefully only for non-Why3 examples
  - `git add` the new files
    (except for the `.html` files, which should go in `web/gallery/.gitignore`)
  - commit and push the modified files

* announce the release using the features of `CHANGES.md`
