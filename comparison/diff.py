#!/usr/bin/env python
#-*- coding: UTF-8 -*-

import sys

# ce script donne la différence entre les résultats des 2 prouveurs en entrée

if len(sys.argv) <= 1:
  print """usage: ./diff prover1,prover2[,prover3,[...]]"""


provers = sys.argv[1]
provers = [p.strip() for p in provers.split(",")]

print "compare les prouveurs", ", ".join(provers)

if len(provers) <= 1:
  print "erreur, il faut au moins 2 prouveurs !"
  sys.exit(1)


# se connecte à la DB

import sqlite3

db_file = "output.db"

conn = sqlite3.connect(db_file)
cursor = conn.cursor()

# utilise la lib pour calculer les différences

import lib

table = []

for p1, p2 in [(p1, p2) for p1 in provers for p2 in provers if p1 < p2]:

  diffs = lib.diff(cursor, p1, p2)

  table += diffs


lib.print_columns(table)
