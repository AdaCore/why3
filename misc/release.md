# Making a release

* assuming some variables
  - `VERSION=1.3`
  - `RELEASE=1.3.0`

* perform a sanity check
  - check the BTS
  - check that the nightly bench is OK
  - `make xml-validate-local` (see below for `why3session.dtd`)
  - check `CHANGES.md`
  - run `make detect-unused` and remove unused files
  - run `make update-doc-png` and check if some pictures need to be updated
  - run `make doc/latex/manual.pdf` and check the manual
  - run `make dist` and check the content of `distrib/why3-X.X.X.tar.gz`
  - check `lib/why3/META.in` (e.g., against `EXTPKGS` in `Makefile.in`)
  - update `opam/why3{,-ide,-coq}.opam` with correct dependencies on external packages
  - check the gallery, especially the new examples (see below)
  - run the manual job `trywhy3-extra` to build Alt-Ergo for TryWhy3 if needed (see below)

* check/update authors and copyright
  - update the content of the About dialog in `src/ide/gconfig.ml`
    around lines 680-700
  - update the `copyright` field in `doc/conf.py` around line 50
  - update `doc/foreword.rst`
  - update `src/trywhy3/trywhy3.html`
  - check headers, modify `misc/header.txt` and run `make headers` if needed
  - commit as needed

* perform and push the release commit
  - create a branch if needed, `git checkout -b bugfix/v$VERSION master`
  - or just move to it, `git checkout bugfix/v$VERSION`
  - update the first line of `configure.in` using `$RELEASE`
  - update the `version` and `release` fields in `doc/conf.py` around line 60
  - add the release date to `CHANGES.md`
  - update the date in `doc/index.rst`
  - make a last commit
    ```
    git commit -am "Version $RELEASE"
    git tag $RELEASE
    git push
    git push --tags
    ```

* prepare and upload the archive to https://gitlab.inria.fr/why3/releases
  - `make dist`
  - get the Git repository of the releases and move to it
    ```
    cp .../distrib/why3-$RELEASE.tar.gz releases/
    git add releases/why3-$RELEASE.tar.gz
    git commit -m "Add release $RELEASE."
    git push
    ```

* update the repository, if this is the most recent release
  - forward the `stable` branch of the Why3 repository:
    `git push origin bugfix/v$VERSION:stable`
  - merge back the changes to the `master` branch
  - update the first line of `configure.in` using `$RELEASE+git`,
    commit and push the change to `master`

* update the website, if this is the most recent release
  - get the sources from https://gitlab.com/why3project/why3project.gitlab.io
  - update `index.html` with the new url for download
  - update `.gitlab-ci.yml` if the Alt-Ergo worker was rebuilt (job `trywhy3-extra`)
  - update `why3session.dtd` with the current version
  - wait for completion of the pipeline of the `stable` branch
  - commit and push the changes, to trigger an update of the website

* prepare and upload the OPAM packages to https://github.com/ocaml/opam-repository
  - reinitialize the repository if not fresh:
    ```
    git remote add upstream https://github.com/ocaml/opam-repository.git
    git fetch upstream
    git reset --hard upstream/master
    ```
  - `mkdir packages/why3/why3.$RELEASE packages/why3-coq/why3-coq.$RELEASE packages/why3-ide/why3-ide.$RELEASE`
  - copy the `opam` files from the directories of the previous release
  - reconcile with the changes from Why3's repository
  - update the `url` section of all three `opam` files
  - push and make a pull request on Github
  - check whether some downstream developments were broken
    and update the pull request accordingly

* produce the Why3 part of Toccata gallery, if this is the most recent release
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
