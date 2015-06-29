/**
 * @file DefinitionIntroduction.hpp
 * Defines class DefinitionIntroduction.
 */

#ifndef __DefinitionIntroduction__
#define __DefinitionIntroduction__

#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Lib/Environment.hpp"
#include "Lib/DHMap.hpp"

#include "Forwards.hpp"

namespace FMB {

  //TODO mark as an actual iterator?
  class DefinitionIntroduction{

  public:
    DefinitionIntroduction(ClauseIterator cit) : _cit(cit) {
      _ng = env.options->fmbNonGroundDefs();
    }


    bool hasNext(){
      TimeCounter tc(TC_FMB_DEF_INTRO);
      CALL("DefinitionIntroduction::hasNext");
      // first see if we have any processed clauses
      if(_processed.length()==0){
        // if there are clauses left to process then do these 
        if(_todo.length()!=0) process(_todo.pop());
        // if not, process the next clause if it exists
        else if(_cit.hasNext()) process(_cit.next());
        // there's nothing left to do
        else return false;
      } 
      return true; 
    }

    Clause* next(){
      TimeCounter tc(TC_FMB_DEF_INTRO);
      CALL("DefinitionIntroduction::next");
      ASS_G(_processed.length(),0);
      return _processed.pop();
    }

  private:

    void process(Clause* c){
      CALL("DefinitionIntroduction::process");

      //cout << "Process " << c->toString() << endl;

      static Stack<Literal*> lits; // to rebuild the clause
      lits.reset();

      for(unsigned i=0;i<c->length();i++){
        Literal* l = (*c)[i];
        bool updated = false;

        //cout << " process " << l->toString() << endl;

        Stack<TermList> args; 
        for(TermList* ts = l->args(); ts->isNonEmpty(); ts = ts->next()){
          // do not add definitions for variables or constants
          if(ts->isVar() ||  ts->term()->arity()==0){
            args.push(*ts);
          }
          else{
            updated=true;
            Term* t;
            if(ts->term()->ground()){
              t = addGroundDefinition(ts->term(),c);
            }
            else{
              t = addNonGroundDefinition(ts->term(),c);
            }
            ASS(t->shared());
            args.push(TermList(t)); 
          }
        }
        if(!updated || (l->isEquality() && args[0]==args[1])){
          lits.push(l); 
        }
        else{
          Literal* nl = Literal::create(l,args.begin());
          lits.push(nl);
        }
      }

      Clause* cl = Clause::fromStack(lits,c->inputType(),
                     new Inference1(Inference::FMB_DEF_INTRO,c));
      _processed.push(cl);
    }

    Term* addGroundDefinition(Term* t, Clause* from){
      CALL("DefinitionIntroduction::addGroundDefinition");
      //cout << "Adding definition for " << t->toString() << endl;
      Term* c;
      if(!_introduced.find(t,c)){
        unsigned newConstant = env.signature->addFreshFunction(0,"fmbdef");
        c = Term::createConstant(newConstant); 
        _introduced.insert(t,c);

        unsigned sort = SortHelper::getResultSort(t); //TODO set sort of c as this
        Literal* l = Literal::createEquality(true,TermList(t),TermList(c),sort);
        static Stack<Literal*> lstack;
        lstack.reset();
        lstack.push(l);
        Clause* def = Clause::fromStack(lstack,from->inputType(),
                    new Inference1(Inference::FMB_DEF_INTRO,from));

        //cout << "creating def " << def->toString() << endl;
        //TODO check if we can push directly onto processed
        _todo.push(def); 
      }
      return c;
    }

    Term* addNonGroundDefinition(Term* t, Clause* from){
      CALL("DefinitionIntroduction::addNonGroundDefinition");

      // currently don't do anything until I've fixed it
      return t;

      // only do something if using option
      if(!_ng) return t;

      // The idea is to replace a complex non-ground term such as
      //  f(g(x,a),f(b,g(y,z)) with n(x,y,z)
      // in C and then introduce definition n(x,y,z) = f(g(x,a),f(b,g(y,z))
      // this should lead to fewer variables in flattened clauses

      // this is the new function symbol
      unsigned newf;

      //check if 
      if(!_introducedNG.find(t,newf)){

        // first count the variables in t
        unsigned vars = t->vars();

        // then create a fresh function symbol for the definition
        newf = env.signature->addFreshFunction(vars,"fmbdef");
        // and save it
        _introducedNG.insert(t,newf);
        

        // next create the definition clause
        Stack<TermList> varTerms;
        for(unsigned v=0;v<vars;v++){
          TermList vt(v,false);
          varTerms.push(vt);
        }
        Term* nt = Term::create(newf,vars,varTerms.begin()); 

        unsigned sort = SortHelper::getResultSort(t); //TODO set sort of newf
        Literal* l = Literal::createEquality(true,TermList(t),TermList(nt),sort);

        static Stack<Literal*> lstack;
        lstack.reset();
        lstack.push(l);
        Clause* def = Clause::fromStack(lstack,from->inputType(),
                    new Inference1(Inference::FMB_DEF_INTRO,from));

        _todo.push(def);
      }
      // Finally create the correct instance of this definition for this one
      // note that the variables may not be in the same order as the def
      // i.e. it might be f(x,g(a,y)) in one place and f(y,g(a,x)) elsewhere

      // currently don't do anything!
      return t;
    }

    bool _ng;

    ClauseIterator _cit;
    Stack<Clause*> _processed;
    Stack<Clause*> _todo;

    DHMap<Term*,Term*> _introduced;
    DHMap<Term*,unsigned> _introducedNG;

  };

} // namespace FMB
#endif
