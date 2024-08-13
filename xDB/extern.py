#!/usr/bin/env python3

import sys

if __name__ == "__main__":
  query = sys.argv[1]

  pred,rest = query.split("(")
  assert rest.endswith(")")
  rest = rest[:-1]
  args = rest.split(",")

  capitals = {"czech_republic":"prag", "germany":"berlin", "austria":"vienna"}
  if pred == "capitalOf":
    assert len(args) == 2
    if args[1] in capitals:
      print(f"capitalOf({capitals[args[1]]},{args[1]})")

  exit(0)