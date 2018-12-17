# Making a release

* perform a sanity check
  - check the BTS
  - check that nightly bench is OK
  - `make xml-validate-local`
    (see below: copy the dtd on the web)
  - `make trywhy3`

* change version number
  ```
  VERSION=1.1.0
  echo "VERSION=$VERSION" > Version
  ./config.status
  ```
  - check/update the content of the About dialog in `src/ide/gconfig.ml`
    around lines 600-650
  - check headers
  - check the file `CHANGES.md`, add the release date

* generate documentation
  - update the date in `doc/manual.tex` (near `\whyversion{}`)
  - check/update the authors in `doc/manual.tex`
  - check that macro `\todo` is commented out in `doc/macros.tex`
  - `make doc`
    (check that manual in HTML is also generated, `doc/html/index.html`)
  - `make stdlibdoc`
  - `make apidoc`

* prepare the archive
  - make a last commit:
    ```
    git commit -am "Version $VERSION"
    git tag $VERSION
    ```
  - `make dist`
  - test `distrib/why3-$VERSION.tar.gz`
  - push the commit:
    ```
    git push
    git push --tag
    ```
  - upload `distrib/why3-$VERSION.tar.gz` to https://gforge.inria.fr/frs/?group_id=2990

* upload the documentation on the web page
  ```
  cp share/why3session.dtd /users/www-perso/projets/why3/
  cp doc/manual.pdf /users/www-perso/projets/why3/download/manual-$VERSION.pdf
  ln -s -n -f download/manual-$VERSION.pdf /users/www-perso/projets/why3/manual.pdf
  cp -r doc/html /users/www-perso/projets/why3/doc-$VERSION
  ln -s -n -f doc-$VERSION /users/www-perso/projets/why3/doc
  cp -r doc/stdlibdoc /users/www-perso/projets/why3/stdlib-$VERSION
  ln -s -n -f stdlib-$VERSION /users/www-perso/projets/why3/stdlib
  cp -r doc/apidoc /users/www-perso/projets/why3/api-$VERSION
  ln -s -n -f api-$VERSION /users/www-perso/projets/why3/api
  ```

* update the main HTML page (sources are in repository `why3-www`)
  - edit `index.html`, change at least all occurrences of `1.0.0` by `1.1.0`, and
    update the url for download
  - `make` (to check validity)
  - `make export`
  - update TryWhy3
    ```
    make trywhy3
    make trywhy3_package
    tar xzf trywhy3.tar.gz -C /users/www-perso/projets/why3/try/ --strip-components=1
    ```

* next commit: add `+git` to the version in file `Version`

* prepare the OPAM package
  - update `why3{,-ide,-coq}.opam/descr` if necessary
  - update `why3{,-ide,-coq}.opam/opam` with correct dependencies on external packages
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
    - `mkdir packages/why3/why3.$VERSION packages/why3-coq/why3-coq.$VERSION packages/why3-ide/why3-ide.$VERSION`
    - copy the opam files from the directories of the previous release (Opam 2.0 format)
  - update `why3{-ide,-coq}.$VERSION/opam` with the dependency on why3
  - url and checksum of `why3.tar.gz`:
    - `md5sum .../distrib/why3-$VERSION.tar.gz`
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

* once the OPAM package is pulled in the main OPAM repository:
  - announce the release
  - What to put in the announcement: see New Features above
