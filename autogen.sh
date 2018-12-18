#!/bin/sh -eux

if [ ! -f "configure" ]; then
  autoconf
  automake --add-missing || true
fi
