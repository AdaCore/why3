#!/bin/bash

set -e

autoconf && (automake --add-missing 2> /dev/null || true)
if test -n "$PACKAGES"; then
  IMAGE=bench-image-$COMPILER--$(echo $PACKAGES | sed -e 's/ /--/g')
else
  IMAGE=bench-image-$COMPILER
fi
docker build -t $IMAGE -f misc/Dockerfile.init --build-arg compiler=$COMPILER --build-arg packages="$PACKAGES" .
CID=$(docker create --rm -i -w /home/why3/why3 $IMAGE /bin/sh)
docker start $CID
docker cp . $CID:/home/why3/why3
docker exec -u root $CID chown -R why3:why3 /home/why3/why3
docker attach $CID <<EOF
exec $@
EOF
