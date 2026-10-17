#!/usr/bin/env python3
"""Separate parser checks, solver command presence, and observed activation."""
import argparse,hashlib,json,pathlib

INTROSPECTION={'--help','-h','--show_options','--show_experimental_options','--version'}
SOLVING_MODES={'vampire','casc','casc_sat','portfolio','smtcomp'}

def option_value(command,*flags):
    found=None
    for index,token in enumerate(command):
        if token in flags and index+1<len(command): found=command[index+1]
    return found

def solver_command(row):
    command=row.get('command',[])
    if not command or pathlib.Path(command[0]).name not in ('vampire', 'vampire.exe'): return False,'not a primary Vampire command'
    if row['name'].startswith('options/'): return False,'parser test'
    if row['name'].startswith('discovery/'): return False,'discovery command'
    for flag in INTROSPECTION:
        if flag in command and option_value(command,flag) not in ('off','false','0'): return False,'introspection command'
    if option_value(command,'--explain_option','-explain') is not None: return False,'option documentation command'
    # -m is memory_limit, never a mode alias.
    mode=option_value(command,'--mode')
    if mode is not None and mode not in SOLVING_MODES: return False,'non-solving or unclassified mode: '+mode
    exact_smt_answer=row.get('check')=='exact' and str(row.get('expected','')).splitlines()[:1] in (['sat'],['unsat'])
    if row.get('check') not in ('szs','smt-proof','finite-model') and not exact_smt_answer and 'semantic_outcome' not in row:
        return False,'no declared logical-answer check'
    if row.get('check') in ('reject','reject-regex','unsupported','contains','once','exact','exit','roundtrip','option-boundary') and not exact_smt_answer:
        return False,'non-solving, rejection, or unclassified check'
    return True,'explicit logical-solver command; activation requires separate evidence'

def build(run,extensions):
    catalogue=json.loads((run/'option-inputs/catalogue.json').read_text())
    summary=json.loads((run/'summary.json').read_text())
    base=summary['results']; extra=[];sources=[]
    for folder in extensions:
        data=json.loads((folder/'summary.json').read_text())
        sources.append({'path':str(folder),'summary_sha256':hashlib.sha256((folder/'summary.json').read_bytes()).hexdigest()})
        for row in data['results']: extra.append({**row,'name':'extension/'+folder.name+'/'+row['name']})
    entries=[]
    for entry in catalogue['compiled_options']:
        flags={'--'+entry['name']}
        if entry['short']: flags.add('-'+entry['short'])
        parser=[r for r in base if r['name'].startswith('options/') and flags.intersection(r['command'])]
        discovery=[r for r in base if r['name'].startswith('discovery/') and flags.intersection(r['command'])]
        baseline=[r['name'] for r in base if solver_command(r)[0] and flags.intersection(r['command'])]
        added=[r['name'] for r in extra if solver_command(r)[0] and flags.intersection(r['command'])]
        observed=[{'case':r['name'],'artifacts':r['artifacts'],'semantic_outcome':r['semantic_outcome'],
                   'memory_outcome':r.get('memory_outcome','not-instrumented'),'evidence':r['activation_matches']}
                  for r in extra if r['option']==entry['name'] and r['activation']=='observed' and r['semantic_outcome']=='pass']
        excluded=[{'case':r['name'],'reason':solver_command(r)[1]} for r in base
                  if not r['name'].startswith('options/') and flags.intersection(r['command']) and not solver_command(r)[0]]
        entries.append({'name':entry['name'],'short':entry['short'],
            'parser_results':{state:sum(r['outcome']==state for r in parser) for state in ['pass','fail','inconclusive']},
            'discovery_cases':[r['name'] for r in discovery],'baseline_solver_commands':baseline,
            'extension_solver_commands':added,'confirmed_activation':observed,'excluded_non_parser_commands':excluded})
    def counts(rows):
        return {'compiled_options':len(rows),'options_with_parser_cases':sum(any(e['parser_results'].values()) for e in rows),
                'options_with_baseline_solver_commands':sum(bool(e['baseline_solver_commands']) for e in rows),
                'options_with_any_solver_commands':sum(bool(e['baseline_solver_commands'] or e['extension_solver_commands']) for e in rows),
                'options_with_confirmed_runtime_activation':sum(bool(e['confirmed_activation']) for e in rows)}
    return {'baseline_run':str(run),'baseline_summary_sha256':hashlib.sha256((run/'summary.json').read_bytes()).hexdigest(),
            'extension_sources':sources,'counts':counts(entries),'options':entries,
            'classification':'Conservative primary logical-answer solver commands only. Parser/help/discovery, transformations, expected rejection and unclassified checks are excluded.',
            'limitations':['Command presence does not establish acceptance or feature activation.',
                           'Decoded strategies, defaults, secondary round-trip solver commands, and shell scripts are not expanded.',
                           'Activation is confirmed only by the named extension counters or validated model-size traces.',
                           'A positive counter is bounded activation evidence, not full implementation coverage.',
                           'Memory failures remain recorded separately and do not erase observed activation.']}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run',type=pathlib.Path,required=True)
    p.add_argument('--extension',type=pathlib.Path,action='append',default=[]);p.add_argument('--output',type=pathlib.Path,required=True)
    args=p.parse_args();data=build(args.run,args.extension)
    args.output.parent.mkdir(parents=True, exist_ok=True);args.output.write_text(json.dumps(data,indent=2)+'\n');print(json.dumps(data['counts'],indent=2))

if __name__=='__main__':main()
