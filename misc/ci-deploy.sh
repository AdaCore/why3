#!/bin/sh

set -e

autoconf && (automake --add-missing 2> /dev/null || true)
docker build -t bench-image-system-stable -f misc/Dockerfile.init .
IMAGE=$CI_REGISTRY_IMAGE:$(echo $CI_COMMIT_REF_NAME | tr -cs "[:alnum:].\n" "-")
docker build -t $IMAGE -f misc/Dockerfile.deploy .
docker login -u $CI_REGISTRY_USER -p $CI_REGISTRY_PASSWORD $CI_REGISTRY
docker push $IMAGE
docker rmi $IMAGE
