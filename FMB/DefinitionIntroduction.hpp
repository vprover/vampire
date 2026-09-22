/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file DefinitionIntroduction.hpp
 * Defines class DefinitionIntroduction.
 */

#ifndef __DefinitionIntroduction__
#define __DefinitionIntroduction__

#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Kernel/Clause.hpp"

#include "Lib/Environment.hpp"
#include "Lib/DHMap.hpp"

#include "Forwards.hpp"

namespace FMB {

  //TODO mark as an actual iterator?
  class DefinitionIntroduction{
  public:
    DefinitionIntroduction(ClauseIterator cit) : _cit(std::move(cit)) {
    }


    bool hasNext(){
      TIME_TRACE(TimeTrace::FMB_DEFINITION_INTRODUCTION);
      // first see if we have any processed clauses
      if(_processed.length()==0){
        // process the next clause if it exists
        if(_cit.hasNext()) process(_cit.next());
        // there's nothing left to do
        else return false;
      } 
      return true; 
    }

    Clause* next(){
      TIME_TRACE(TimeTrace::FMB_DEFINITION_INTRODUCTION);
      ASS_G(_processed.length(),0);
      return _processed.pop();
    }


  private:

    void process(Clause* c){
      //std::cout << "Process " << c->toString() << std::endl;

      static Stack<Literal*> lits; // to rebuild the clause
      lits.reset();

      bool anyUpdated = false;

      for(unsigned i=0;i<c->length();i++){
        Literal* l = (*c)[i];
        bool updated = false;

        //std::cout << " process " << l->toString() << std::endl;

        Stack<TermList> args; 
        for(TermList* ts = l->args(); ts->isNonEmpty(); ts = ts->next()){
          // do not add definitions for variables or constants
          if(ts->isVar() ||  ts->term()->arity()==0 || !ts->term()->ground()){
            args.push(*ts);
          }
          else{
            ASS(ts->term()->ground());
            Term* t = addGroundDefinition(ts->term(),c);
            ASS(t->shared());
            args.push(TermList(t)); 
            updated |= (t != ts->term());
          }
        }
        if(!updated){
          lits.push(l); 
        }
        else{
          anyUpdated = true;
          Literal* nl = Literal::create(l,args.begin());
          lits.push(nl);
        }
      }

      if(anyUpdated){
        Clause* cl = Clause::fromStack(lits,NonspecificInference1(InferenceRule::FMB_DEF_INTRO,c));
         _processed.push(cl);
      }else{
         _processed.push(c);
      }
    }

    Term* addGroundDefinition(Term* term, Clause* from){
      //std::cout << "Adding defs for " << term->toString() << std::endl;
      ASS(term->ground());
      if(term->arity()==0) return term;

      Term* retC=0;
      if(_introduced.find(term,retC)){ return retC; }

      PolishSubtermIterator it(term);
      while(it.hasNext() || retC==0){
        Term* t = it.hasNext() ? it.next().term() : term;
        //std::cout << "Considering " << t->toString() << std::endl;
        if(t->arity()==0) continue;
        if(!_introduced.find(t)){
          TermList srt = SortHelper::getResultSort(t);
          unsigned newConstant = env.signature->addFreshFunction(OperatorType::getConstantsType(srt),"fmbdef");
          // no need to mark it as used: it occurs in the definition clause pushed below,
          // which this iterator yields along with the rest
          Term* c = Term::createConstant(newConstant); 
          _introduced.insert(t,c);
          if(term==t) retC=c;

          //Now apply definitions to t
          bool updated = false;
          Stack<TermList> args;
          for(TermList* ts = t->args(); ts->isNonEmpty(); ts = ts->next()){
            ASS(ts->term()->ground());
            // do not add definitions for constants
            if(ts->term()->arity()==0){args.push(*ts);}
            else{
              Term* argT = _introduced.get(ts->term());
              args.push(TermList(argT));
              updated = true; 
            }
          }
          if(updated){
            t = Term::create(t,args.begin());
          }
          TermList sort = SortHelper::getResultSort(t); //TODO set sort of c as this
          Literal* l = Literal::createEquality(true,TermList(t),TermList(c),sort);
          static Stack<Literal*> lstack;
          lstack.reset();
          lstack.push(l);
          Clause* def = Clause::fromStack(lstack,NonspecificInference1(InferenceRule::FMB_DEF_INTRO,from));

          //std::cout << "creating def " << def->toString() << std::endl;
          _processed.push(def); 
        }
      }
      ASS(retC);
#if VDEBUG
      Term* otherRetC = 0;
      ASS(_introduced.find(term,otherRetC));
      ASS(retC==otherRetC);
#endif
      return retC;
    }

    ClauseIterator _cit;
    Stack<Clause*> _processed;

    DHMap<Term*,Term*, FnvHash, PtrIdentityHash> _introduced;
  };

} // namespace FMB
#endif
