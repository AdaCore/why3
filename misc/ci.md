Continuous integration is run inside Docker containers.

The corresponding Docker image is loaded from the Gitlab registry. It
is built from the `misc/Dockerfile.build` description. Changes to this
file do not automatically lead to a new Docker image. One should first
modify the image name in the `BUILD_IMAGE` variable of
`.gitlab-ci.yml`, using the current date in the name.

Push your changes in a branch, then go to Why3's gitlab page of
pipelines, https://gitlab.inria.fr/why3/why3/-/pipelines, click on the
"Run pipeline" blue button on the right, to manually trigger a
pipeline. Put the name of your branch, and then give the extra
parameters there, provide here the `NEW_BUILD_IMAGE` variable with any
non-empty value.
