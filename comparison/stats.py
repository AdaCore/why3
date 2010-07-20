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
provers = [line[0] for line in provers]

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
    WHERE result = "Timeout"
    AND prover = "%s"
    """ % prover).fetchall()

  stats[prover] = (len(successes), len(failures))


# mettre en forme

table = [["prouveur", u"nombre de succès", u"nombre d'échecs", "nombre total"]]

for prover in provers:

  entry = [prover, stats[prover][0], stats[prover][1], stats[prover][0] + stats[prover][1]]
  table.append(entry)

lib.print_columns(table, sep = " ")
