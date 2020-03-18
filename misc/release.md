# Making a release

* perform a sanity check
  - check the BTS
  - check that nightly bench is OK
  - `make xml-validate-local`
    (see below: copy the dtd on the web)
  - `make trywhy3`
  - run `make detect-unused` and remove unused files
  - run `make update-doc-png` and check if some pictures need to be updated

* change version number `VERSION=1.3 RELEASE=1.3.0`
  - update the first line of `configure.in` using `$RELEASE`
  - update the `version` and `release` fields in `doc/conf.py` around line 60
  - check `CHANGES.md`, add the release date
  - update the date in `doc/index.rst`

* check/update authors and copyright
  - update the content of the About dialog in `src/ide/gconfig.ml`
    around lines 630-670
  - update the `copyright` field in `doc/conf.py` around line 50
  - update `doc/foreword.rst`
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
  - upload `distrib/why3-$RELEASE.tar.gz` to https://gforge.inria.fr/frs/?group_id=2990

* upload the documentation on the web page
  ```
  DEST=/users/www-perso/projets/why3
  cp share/why3session.dtd $DEST/
  cp doc/latex/manual.pdf $DEST/download/manual-$VERSION.pdf
  ln -s -n -f download/manual-$VERSION.pdf $DEST/manual.pdf
  rm -rf $DEST/doc-$VERSION $DEST/stdlib-$VERSION $DEST/api-$VERSION
  cp -r doc/html $DEST/doc-$VERSION
  ln -s -n -f doc-$VERSION $DEST/doc
  cp -r doc/stdlibdoc $DEST/stdlib-$VERSION
  ln -s -n -f stdlib-$VERSION $DEST/stdlib
  cp -r doc/apidoc $DEST/api-$VERSION
  ln -s -n -f api-$VERSION $DEST/api
  ```

* update the main HTML page (sources are in repository `why3-www`)
  - edit `index.html`, change at least all occurrences of the version, and
    update the url for download
  - `make` (to check validity)
  - `make export`
  - update TryWhy3
    ```
    make trywhy3
    make trywhy3_package
    tar xzf trywhy3.tar.gz -C $DEST/try/ --strip-components=1
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
  - have `GALLERYDIR` set to the sub-directory `gallery/` of the git sources
    of the Toccata web site, e.g.
    `export GALLERYDIR=/users/vals/filliatr/toccata/web/gallery`
  - in Why3 sources, do `make gallery`; it exports to `$GALLERYDIR` all
    Why3 programs for which there is a session
  - now move to the Toccata web site sources, and
    - update `web/gallery/examples.rc` to include new examples
    - `git add` the files for these new examples (those currently untracked
      in git) or simply remove them if they should not go on-line
    - do `make` in `web/gallery/`
    - do `make install-gallery` in `web/`

* announce the release using the features of `CHANGES.md`
