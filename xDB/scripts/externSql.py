#!/usr/bin/env python3
# respond to a TPTP format query from Vampire, as a SUO-KIF format query
# of the SQL DB and convert it back to TPTP format

import sys, os
import sqlite3
from typing import Iterable, Sequence

#CREATE TABLE stmts(pred text NOT NULL, arg1 text NOT NULL, arg2 text NOT NULL, arg3 text, arg4 text, arg5 text);
#CREATE TABLE arity (pred text NOT NULL, value integer NOT NULL);

debug = False

##########################################
# init database connection
def init():
  path = os.getenv('XDB')
  if debug:
    print(path)
  sqliteConnection = sqlite3.connect(path + '/db/stmts.db')
  cursor = sqliteConnection.cursor()
  return sqliteConnection, cursor

##########################################
# Decompose the TPTP query into predicate and list of arguments
def decompQuery(q:str):
  pred,rest = q.split("(")
  if pred.startswith("s__"):
    pred = pred[3:]
  assert rest.endswith(")")
  rest = rest[:-1]
  args = rest.split(",")
  newargs = []
  for arg in args:
    if arg.startswith("s__"):
      newargs.append(arg[3:])
    else:
      newargs.append(arg)
  return pred, newargs, args

##########################################
# build SQL query from predicate and list of arguments
def buildQuery(pred:str, args:Sequence, origArgs:Sequence):
  query = 'SELECT '
  hasArg = 0
  for n in range(0,len(args)):
    if debug:
      print("n:",n)
    if (origArgs[n].istitle()):
      query = query + 'arg' + str(n+1) + ', '
      hasArg = 1
  if hasArg:
    query = query[0:(len(query)-2)]
  else:
    query = 'SELECT *'
  query = query + ' FROM stmts'
  selection = "pred='" + pred + "' "
  for n in range(0,len(args)):
    if not (origArgs[n].istitle()): # if it's not a variable, add a restriction
      selection = selection + 'AND arg' + str(n+1) + '="' + args[n] + '" '
  if selection:
    query = query + " WHERE " + selection + ";"
  return query

########################################
# turn SQL results into TPTP tuples
def processResults(results:Iterable, pred:str, args:Sequence, origArgs:Sequence):
  if results == []:
    return ""
  resstr = ""
  for res in results:
    if debug:
      print('DB result: ',res)
      print('args: ',args)
    resstr = resstr + "s__" + pred + "("
    resindx = 0
    for n in range(0,len(args)):
      if debug:
        print('in progress: ',resstr)
        print('resindx: ',resindx)
      if (origArgs[n].istitle()):  # if query argument is a variable fill in with SQL result
        if (res[resindx].isnumeric()):
          resstr = resstr + res[resindx]
        else:
          resstr = resstr + "s__" + res[resindx]
        resindx = resindx + 1
      else:
        resstr = resstr + origArgs[n]
      if n == len(args)-1:
        resstr = resstr + ")\n"
      else:
        resstr = resstr + ","
  if debug:
    print("TPTP converted result: " + resstr)
  return resstr

#################################
# start the process

if __name__ == "__main__":
  sqliteConnection = None
  try:
    sqliteConnection, cursor = init()
    pred,args,origArgs = decompQuery(sys.argv[1])
    if debug:
      print('origArgs: ' + str(origArgs))
      print('args: ' + str(args))
    query = buildQuery(pred,args,origArgs)
    if debug:
      print("query: ",query)
    cursor.execute(query)
    results = cursor.fetchall()
    if debug:
      print("results:", results)
    resstr = ""
    if results:
      resstr = processResults(results,pred,args,origArgs)
    else:
      if debug:
        print("Error: no results for query: " + query)
    if debug:
      print("results: ")
    print(resstr)
    cursor.close()

  # Handle errors
  except sqlite3.Error as error:
    print('Error occurred - ', error)

  # Close DB Connection irrespective of success
  # or failure
  finally:
    if sqliteConnection:
        sqliteConnection.close()
        #print('SQLite Connection closed')

  exit(0)

