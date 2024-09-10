#!/usr/bin/env python3
# shell of a program to convert statements in YAGO into an SQL database and update them to be current with SUMO

import sys
import sqlite3

if __name__ == "__main__":
  try:
    query = sys.argv[1]
    name,rest = query.split(".")
    assert rest.endswith(")")
    sqliteConnection = sqlite3.connect(name + '.db')
      
     cursor = sqliteConnection.cursor()
     #print('DB Init')
     query = 'SELECT city FROM capitals WHERE country="' + args[1] + '";'
     #print(query)
     cursor.execute(query)
     sqliteConnection.commit()
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
  
