#!/bin/bash

set -e

autoconf && (automake --add-missing 2> /dev/null || true)
docker build -t bench-image-$COMPILER -f misc/Dockerfile.init --build-arg compiler=$COMPILER .
CID=$(docker create --rm -i -w /home/why3/why3 bench-image-$COMPILER /bin/sh)
docker start $CID
docker cp . $CID:/home/why3/why3
docker exec -u root $CID chown -R why3:why3 /home/why3/why3
docker attach $CID <<EOF
exec $@
EOF
