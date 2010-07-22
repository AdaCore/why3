#!/usr/bin/env python
#-*- coding: UTF-8 -*-


# ce script cherche les (file,goal) pour lesquels un prouveur SMT et
# un prouveur TPTP ont des résultats différents.

import sys


# connexion DB
import sqlite3

conn = sqlite3.connect("output.db")
cursor = conn.cursor()


# utilitaires
import lib

# les prouveurs (demander à la DB)
provers = cursor.execute("select distinct prover from runs").fetchall()

provers = [p[0] for p in provers]

# les 2 uplets de prouveurs, sans redondances
provers_combinaisons = [(p1,p2) for p1 in provers for p2 in provers if p1 < p2]

# trouver les couples de prouveurs dont l'un échoue et l'autre réussit,
# pour chaque (fichier,but)
diffs = []
diffs = cursor.execute("""SELECT r1.file,r1.goal, r1.prover, r1.result, r2.prover, r2.result
  FROM runs r1
  INNER JOIN runs r2
  WHERE r1.file = r2.file
    AND r1.goal = r2.goal
    AND r1.result = "Valid"
    AND r2.result <> "Valid"
  ORDER BY r1.file ASC""").fetchall()


# comment différencier un prouveur TPTP d'un prouveur SMT ?
tptp = ["spass", "eprover"]

def isTptp(x):
  "x est-il le nom d'un prouveur tptp ?"
  for t in tptp:
    if x.find(t) >= 0:
      return True
  return False

# garder les lignes représentant une différence entre un tptp et un smt
diffs = [line for line in diffs if (isTptp(line[2]) ^ isTptp(line[4]))]

# afficher
lib.print_columns(diffs)
