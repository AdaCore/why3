#!/bin/sh

sed -i -e "s/Timeout, [^,]*,/Timeout, 30,/g" \
    -e "s/Timeout, [^,]*$/Timeout, 30/g" \
    -e "s/Unknown: \"Unknown\", [^,]*,/Unknown: \"Unknown\", 30,/g" \
    -e "s/Unknown: \"Unknown\", [^,]*$/Unknown: \"Unknown\", 30/g" \
    -e "s/InternalFailure, [^,]*,/InternalFailure, 30,/g" \
    -e "s/InternalFailure, [^,]*$/InternalFailure, 30/g" \
    -e "s/HighFailure, [^,]*,/HighFailure, 30,/g" \
    -e "s/HighFailure, [^,]*$/HighFailure, 30/g" \
    "$@"