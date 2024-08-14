#!/usr/bin/env python3

import sys, os
import sqlite3

#sqlite> CREATE TABLE stmts(pred text NOT NULL, arg1 text NOT NULL, arg2 text NOT NULL, arg3 text, arg4 text, arg5 text);
#sqlite> INSERT INTO stmts VALUES ("capitalCity","prague","czechia","","","");
#sqlite> INSERT INTO stmts VALUES ("capitalCity","berlin","germany","","","");
#sqlite> INSERT INTO stmts VALUES ("capitalCity","washingtonDCUnitedStates","unitedStates","","","");
#sqlite> CREATE TABLE arity (pred text NOT NULL, value integer NOT NULL);

if __name__ == "__main__":
  try:
    query = sys.argv[1]
    pred,rest = query.split("(")
    assert rest.endswith(")")
    rest = rest[:-1]
    args = rest.split(",")
    sqliteConnection = sqlite3.connect(os.path.join(os.path.dirname(os.path.realpath(__file__)),'stmts.db'))
    #print("pred and args", pred, args)

    assert len(args) == 2

    cursor = sqliteConnection.cursor()
    #print('DB Init')
    query = 'SELECT * FROM stmts'
    selection = ""
    for n in range(0,len(args)):
      if not (args[n].istitle()):
        selection = selection + 'arg' + str(n+1) + '="' + args[n] + '" '
    if selection:
      query = query + " WHERE " + selection + ";"
    # print("query",query)
    cursor.execute(query)
    while result := cursor.fetchone():
      args = ",".join(result[1:3])
      print(f"{pred}({args})")
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

