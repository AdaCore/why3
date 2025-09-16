Continuous integration is run inside Docker containers.

The corresponding Docker image is loaded from the Gitlab registry. It
is built from the `misc/Dockerfile.build` description. Changes to this
file do not automatically lead to a new Docker image. One should first
modify the image name in the `BUILD_IMAGE` variable of
`.gitlab-ci.yml`, using the current date in the name.
