"""Bounded runtime-option fixtures with independent propositional reductions."""
import itertools
from dataclasses import dataclass, asdict


@dataclass
class Case:
    name: str
    option: str
    value: str
    text: str
    clauses: list
    justification: str
    marker: str | None
    extra: list
    model: dict | None = None
    activation_required: bool = True

    @property
    def expected(self):
        if self.model is not None: return 'Satisfiable'
        return 'Satisfiable' if truth_table(self.clauses) is not None else 'Unsatisfiable'


def truth_table(clauses):
    atoms = sorted({literal.lstrip('~') for clause in clauses for literal in clause})
    for bits in itertools.product((False, True), repeat=len(atoms)):
        assignment = dict(zip(atoms, bits))
        if all(any(assignment[x.lstrip('~')] != x.startswith('~') for x in clause) for clause in clauses):
            return assignment
    return None


def cnf(clauses, prefix='c'):
    return ''.join(f'cnf({prefix}{i},axiom,({" | ".join(c) if c else "$false"})).\n' for i,c in enumerate(clauses))


def cases():
    result=[]
    def add(option, values, suffix, text, clauses, reason, marker, extra=()):
        for value in values:
            enabled=value not in ('off','0')
            result.append(Case(f'{option}-{suffix}-{value}',option,value,text,clauses,reason,
                               marker if enabled else None,list(extra), activation_required=enabled and not (option == 'predicate_elimination' and suffix == 'multi-occurrence' and value == 'on')))
    square=[['p','q'],['~p','q'],['p','~q'],['~p','~q']]
    for unsat in (False,True):
        tag='unsat' if unsat else 'sat'
        core=square if unsat else square[:3]
        blocked=[['blocked_p','blocked_q'],['~blocked_p','~blocked_q']]
        add('blocked_clause_elimination',['off','on'],tag,cnf(blocked+core),blocked+core,
            'The truth table evaluates the complete ground clause set; the first two clauses are blocked on either atom.',
            r'Blocked clauses\s*[:|]\s*[1-9]\d*')
        erd='cnf(resolve,axiom,(X!=a | p(X))).\n'+('cnf(neg,axiom,~p(a)).\n' if unsat else '')
        add('equality_resolution_with_deletion',['off','on'],tag,erd,[['p']]+([['~p']] if unsat else []),
            'For X=a the universal clause forces p(a); every other X satisfies its disequality. A singleton p=true model proves the SAT variant.',
            r'Equality resolution\s*[:|]\s*[1-9]\d*', ['--show_preprocessing','on'])
        split='cnf(split,axiom,(p(X) | q(Y))).\ncnf(np,axiom,~p(a)).\n'+('cnf(nq,axiom,~q(b)).\n' if unsat else '')
        add('general_splitting',['off','on'],tag,split,[['p','q'],['~p']]+([['~q']] if unsat else []),
            'Instantiate X=a,Y=b for UNSAT; for SAT use a singleton with p=false and q=true.',
            r'General splitting\s*[:|]\s*[1-9]\d*')
        inequality='cnf(split,axiom,(f(f(f(a)))!=b | p)).\ncnf(eq,axiom,f(f(f(a)))=b).\n'+('cnf(np,axiom,~p).\n' if unsat else '')
        add('inequality_splitting',['0','1'],tag,inequality,[['p']]+([['~p']] if unsat else []),
            'The equation makes the disequality false, so p is forced. The SAT witness is a singleton with p=true and the unique total unary function.',
            r'Split inequalities\s*[:|]\s*[1-9]\d*')
        add('predicate_elimination',['off','on','multi'],tag,cnf(core),core,
            'Exhaustive truth table over the complete propositional input.',
            r'Eliminated predicates\s*[:|]\s*[1-9]\d*')
        deftext='fof(def,axiom,![X]:(unused(X)<=>(p(X)&q(X)))).\n'+cnf([[x.replace('p','p(a)').replace('q','q(a)') for x in c] for c in core])
        add('unused_predicate_definition_removal',['off','on'],tag,deftext,core,
            'The fresh unused predicate can always be interpreted as p AND q. The ground constraints are exactly the displayed two-atom truth table.',
            r'Unused predicate definitions\s*[:|]\s*[1-9]\d*')
        cond='cnf(repeated,axiom,(p(X) | p(Y))).\ncnf(link,axiom,(~p(a) | q)).\n'+('cnf(nq,axiom,~q).\n' if unsat else '')
        add('condensation',['off','fast','on'],tag,cond,[['p'],['~p','q']]+([['~q']] if unsat else []),
            'Taking X=Y forces p everywhere; conversely p everywhere satisfies the repeated clause. Singleton p=q=true proves SAT.',
            r'Condensation\s*[:|]\s*[1-9]\d*', ['--forward_subsumption_resolution','off'])
        inner='cnf(rewrite,axiom,(f(a)!=a | p(f(a)))).\ncnf(eq,axiom,f(a)=a).\n'+('cnf(np,axiom,~p(a)).\n' if unsat else '')
        add('inner_rewriting',['off','on'],tag,inner,[['p']]+([['~p']] if unsat else []),
            'The equation forces p(f(a))=p(a). Singleton p=true is a SAT witness; its negation contradicts the clause in every model.',
            r'Inner rewriting\s*[:|]\s*[1-9]\d*', ['--forward_demodulation','off','--backward_demodulation','off'])
        horn=[['~p','~q','r'],['p'],['q']]+([['~r']] if unsat else [])
        add('unit_resulting_resolution',['off','on'],tag,cnf(horn),horn,
            'Exhaustive truth table of a Horn implication and its antecedents; the UNSAT case also negates the consequent.',
            r'Unit resulting resolution\s*[:|]\s*[1-9]\d*', ['--forward_subsumption_resolution','off'])
    # Multi-occurrence clauses distinguish the multi mode from ordinary elimination.
    multi='cnf(multi,axiom,(p(X) | p(Y))).\ncnf(np,axiom,~p(a)).\n'
    add('predicate_elimination',['off','on','multi'],'multi-occurrence',multi,[['p'],['~p']],
        'Instantiate X=Y=a. This directly contradicts ~p(a); no domain-size assumption is needed.',
        r'Predicate elimination resolvents\s*[:|]\s*[1-9]\d*')
    text='fof(domain,axiom,![X]:(X=a0 | X=a1)).\nfof(distinct,axiom,a0!=a1).\nfof(f0,axiom,f(a0)=a1).\nfof(f1,axiom,f(a1)=a0).\n'
    relation=[[True,False],[False,True]]
    for i in range(2):
        for j in range(2): text+=f'fof(r{i}{j},axiom,{"" if relation[i][j] else "~"}r(a{i},a{j})).\n'
    oracle={'size':2,'function':[1,0],'relation':relation,'names':{'constants':['a0','a1'],'function':'f','relation':'r'}}
    for value in ('1','2'):
        for cnf_mode in ('off','on'):
            result.append(Case(f'fmb_start_size-{value}-cnf-{cnf_mode}','fmb_start_size',value,text,[],
                'Exactly two distinct elements with a swapping unary function and identity relation; the emitted interpretation is independently checked.',
                None,['-sa','fmb','-newcnf',cnf_mode,'--fmb_adjust_sorts','off'],oracle))
    return result


def arguments(case):
    if case.model is not None:
        return ['--statistics','full','-p','tptp','-t','5','--bad_option','hard','--'+case.option,case.value]+case.extra
    argv=['-sa','discount','-av','off','-updr','off','--statistics','full','-p','tptp','-t','5','--bad_option','hard']
    if case.option=='unused_predicate_definition_removal': argv=argv[:4]+argv[6:]
    if case.option in ('equality_resolution_with_deletion','inequality_splitting','inner_rewriting'): argv+=['-fde','none']
    argv+=['--'+case.option,case.value]+case.extra
    return argv


def record(case):
    return {**asdict(case),'expected':case.expected,'truth_table_witness':truth_table(case.clauses) if case.model is None else None,
            'arguments':arguments(case)}
