# Vampire-XDB 

A port of SPASS-XDB to Vampire for use with SUMO.  The first step is to replicate all the tests at
[XSB Testing](https://tptp.cs.miami.edu/Seminars/SPASS-XDB/Testing.html)

Three directories below this one are
  - problems - TPTP language problem files with the new 'external' formula tag.
  - scripts - programs invoked from the 'external' tag
  - db - for sample databases that can be accessed from the scripts.  Currently just
     has small sample data that needs to be expanded with YAGO content for proper performance
     testing


### Test Problems
  - `problems/composer.tff` - working
  - `problems/capitalCity.p` - working
  - `Lincoln.p` - working
  - `problems/curie.p` - not tested
  - `problems/flood.p` - not tested


## Installation
  - compile vampire XDB - check out the martin-XDB branch then compiles as usual with cmake and make
  - set `$XDB` environment variable to point to your local vampire github repository plus `/xDB`
  - run vampire with options '~/workspace/vampire/vampire-xdb --input_syntax tptp -qa plain -tha off -s 0 $XDB/problems/composer.tff'
  - problems that make heavy use of arithmetic may benefit from the options
    `--decode lrs+10_1:1_canc=force:tha=some:to=lpo_10`

## Examples
```
~/workspace/vampire/vampire-xdb --input_syntax tptp -qa plain -tha off -s 0 $XDB/problems/composer.tff
```


## Database content

- SPASS-XDB used database content from YAGO.  TODO - update that content (from 2006) to conform more closely
to (current) SUMO.
- finish script `scripts/YAGOtoDB.py`


## Possible TODOs

- SPASS-XDB's preemptive requests for axioms (-IANo=0) ?
- Allow `$evaleq` from SPASS-XDB or just use the `extern` and write a python evaluation function?
- Create an automatic mode that allows arithmetic to work without having to use `-tha off -s 0`?
- Do UNA/CWA's `$different` work with XDB?

## Component Testing

The python DB access script can be tested with

```
python3 $XDB/scripts/externSql.py "birthdate(X,Y)"
```