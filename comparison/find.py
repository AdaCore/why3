#!/usr/bin/env python
#-*- coding: UTF-8 -*-


# ce script cherche un but qui corresponde aux critères demandés

import sys


# connexion DB
import sqlite3

conn = sqlite3.connect("output.db")
cursor = conn.cursor()



# utilitaires
import lib

# les prouveurs
provers = cursor.execute("select distinct prover from runs").fetchall()

provers = [p[0] for p in provers]

# les 2 uplets de prouveurs
provers_combinaisons = [(p1,p2) for p1 in provers for p2 in provers if p1 < p2]

diffs = []
diffs = cursor.execute("""SELECT r1.file,r1.goal, r1.prover, r1.result, r2.prover, r2.result
  FROM runs r1
  INNER JOIN runs r2
  WHERE r1.file = r2.file
    AND r1.goal = r2.goal
    AND r1.result = "Valid"
    AND r2.result = "Timeout"
  ORDER BY r1.file ASC""").fetchall()

tptp = ["spass", "eprover"]

# garder les lignes représentant une différence entre un tptp et un smt
diffs = [line for line in diffs if (line[2] in tptp) ^ (line[4] in tptp)]

# afficher
lib.print_columns(diffs)
