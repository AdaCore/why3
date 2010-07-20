#!/usr/bin/env python
#-*- coding: UTF-8 -*-


# ce script lance un prouveur sur un fichier .mlw (grâce à why3)
# et stocke la sortie dans la base output.db

import sys
from os import path

from subprocess import Popen, PIPE

import getopt

#------------------------------------------------
# parse les arguments

db_file = "output.db"

try:
  opt, args = getopt.getopt(sys.argv[1:], "df:C:", [])

  target_file = args[0]
  provers = args[1]
  provers = provers.split(",")

  opt = dict(opt)
  if '-d' in opt:
    debug = True
    print >> sys.stderr, u"debug activé !"
  else:
    debug = False

  if '-f' in opt:
    db_file = opt['-f']

  if '-C' in opt:
    config_file = opt['-C']
  else:
    config_file = None

except:
  print """usage:
  process_file [-d] [-f file] [-C config_file] file prover[,prover[,prover...]]
  -d : active le mode debug
  -f <file> : stocke les résultats dans <file>
  -C <file> : utilise le fichier de configuration <file>"""
  sys.exit(1)

print >> sys.stderr, "utilise le(s) prouveur(s) %s sur %s (db : %s)" % \
  (provers, target_file, db_file)


#------------------------------------------------
# ouvre la DB

import sqlite3

conn = sqlite3.connect(db_file)
cursor = conn.cursor()

try:
  cursor.execute("""create table runs
    (file string, goal string, prover string, result string, time float)""")
except sqlite3.OperationalError:
  print >> sys.stderr, "base trouvée dans %s" % db_file



#------------------------------------------------
# lance whyml3 sur le fichier

def launch_whyml(target_file, prover):
  target_file = path.abspath(target_file)

  command_list = ["whyml3", "-P", prover, "-a", "split_goal"]
  if config_file:
    command_list += ["-C", config_file]
  command_list.append(target_file)

  command = " ".join(command_list)
  print >> sys.stderr, command

  why_instance = Popen(command, shell=True, stdout=PIPE)
  results = why_instance.communicate()[0]

  return results


#------------------------------------------------
# parser la sortie

def getFile(x):
  "récupère le nom de fichier"
  return path.basename(x.partition(".mlw")[0] + ".mlw")

def getGoal(x):
  "récupère le nom du but"
  return x.strip().split(" ")[-1]

def getResult(x):
  "récupère le résultat"
  return x.strip().partition(" ")[0]

def getTime(x):
  "récupère le temps de calcul"
  time = x.strip().partition(" ")[2]
  try:
    time = time[1:-2] # (0.02s) --> 0.02
    time = float(time)
    return time
  except:
    return 0

def process_results(results):
  "traite les résultats bruts"
  # découper en lignes
  lines = results.splitlines()
  # découper les lignes à ':'
  lines = [line.partition(":") for line in lines]
  # parser la partie gauche et la partie droite
  lines = [(getFile(x), getGoal(x), getResult(y), getTime(y)) for (x,_,y) in lines]

  return lines


#------------------------------------------------
# enregistrer dans la DB

def protect(x):
  'ajoute des " autour de x'
  return '"' + x + '"'

# pour se rappeler des buts précédents
cache = {}

def process_lines(lines):
  "lit les lignes, et stocke le résultat dans la BDD"

  for line in lines:

    filename = line[0]
    goal = line[1]
    result = line[2]
    time = line[3]

    cur_index = cache.get((filename, goal, prover), None)
    if cur_index == None:
      cache[(filename, goal, prover)] = 0
    else:
      cache[(filename, goal, prover)] = cur_index+1
      goal += str(cur_index)

    filename = protect(filename)
    goal = protect(goal)
    cur_prover = protect(prover)
    result = protect(result)
    time = str(time)

    delete_query = "delete from runs where file = %s and goal = %s and prover = %s" % \
      (filename, goal, cur_prover)

    if debug:
      print delete_query
    cursor.execute(delete_query)

    query = "insert into runs values "
    query += "("
    query += ", ".join([filename, goal, cur_prover, result, time])
    query += ")"

    if debug:
      print query
    cursor.execute(query)



#---------------------------------------------------
# afficher les résultats

import lib

def print_lines(lines):
  lib.print_columns(lines)

#---------------------------------------------------
# effectuer le traitement réel

def process(prover):
  "toute la chaine de traitement pour un prouveur donné"

  prover = prover.strip()
  results = launch_whyml(target_file, prover)
  lines = process_results(results)
  process_lines(lines)
  print_lines(lines)

# on y est !
for prover in provers:
  process(prover)

#------------------------------------------------
# fermeture
cursor.close()
conn.commit()
conn.close()

print "sauvegarde effectuée"

