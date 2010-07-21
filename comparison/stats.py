#!/usr/bin/env python
#-*- coding: UTF-8 -*-


# ce script collecte des statistiques sur les prouveurs

import sys

import lib

# connexion DB
import sqlite3

conn = sqlite3.connect("output.db")
cursor = conn.cursor()

# trouver les prouveurs

provers = cursor.execute("select distinct prover from runs").fetchall()
provers = [unicode(line[0]) for line in provers]

print "prouveurs trouvés :", ", ".join(provers)

lib.print_sep()
print ""


# collecter les statistiques (succès, échecs) de chaque prouveur

stats = {}

for prover in provers:

  successes = cursor.execute("""
    SELECT DISTINCT file,goal FROM runs
    WHERE result = "Valid"
    AND prover = "%s"
    """ % prover).fetchall()


  failures = cursor.execute("""
    SELECT DISTINCT file,goal FROM runs
    WHERE result <> "Valid"
    AND prover = "%s"
    """ % prover).fetchall()

  stats[prover] = (len(successes), len(failures))

sys.stdout.flush()
# mettre en forme

table = [["prouveur", "nombre de succes", "nombre d'echecs", "nombre total"]]

for prover in provers:

  entry = [prover, stats[prover][0], stats[prover][1], stats[prover][0] + stats[prover][1]]
  table.append(entry)

lib.print_columns(table, sep = u" ")

# trouver quels prouveurs sont supérieurs les uns aux autres

lib.print_sep()

order = {}

tuples = [(p1,p2) for p1 in provers for p2 in provers if p1 != p2]
max_len = 0
for prover in provers:
  max_len = max(max_len, len(prover))
for tuple in tuples:
  p1,p2 = tuple

  current = ("compare " + p1 + " "+ p2).ljust(12+2*max_len, " ")
  print current ,"(%.2f %%)" % (float(tuples.index(tuple)) / len(tuples)*100),
  sys.stdout.flush()
  sups = lib.superior(cursor, p1, p2)

  # effacer la ligne
  lib.erase_line()

  order[ (p1, p2) ] = len(sups)

print "\n"

# affiche l'ordre partiel

table = {}

for ((p1,p2), num) in order.iteritems():
  table[ (p1,p2) ] = unicode(num)

lib.printTab(table)
