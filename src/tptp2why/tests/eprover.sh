#!/bin/sh

exec eprover -s -xAuto -tAuto --memory-limit=Auto --tstp-in --cpu-limit=2 $@
