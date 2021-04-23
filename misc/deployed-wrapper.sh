#!/bin/dash

[ "$1" != "ide" -o "$WHY3IDE" != "web" ] && exec why3 "$@"

broadwayd &
sleep 1
export GDK_BACKEND=broadway
why3 "$@"
