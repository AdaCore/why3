#!/bin/sh

headache -c misc/headache_config.txt -h misc/header.txt "$@"
sed -i -e '
    s/Francois Bobot/François Bobot/g;
    s/Jean-Christophe Filliatre/Jean-Christophe Filliâtre/g;
    s/Claude Marche/Claude Marché/g' -- "$@"

