/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "LPOComparator.hpp"

#include "RobSubstitution.hpp"

namespace Kernel {

using namespace std;
using namespace Lib;
using namespace Shell;

using Instruction = LPOComparator::Instruction;
using Branch = Instruction::Branch;
using BranchTag = Instruction::BranchTag;

bool unify(TermList tl1, TermList tl2, TermList& orig1, TermList& orig2)
{
  RobSubstitution rsubst;
  if (!rsubst.unify(tl1, 0, tl2, 0)) {
    return false;
  }
  Substitution temp;
  VariableIterator vit1(orig1);
  while (vit1.hasNext()) {
    auto v = vit1.next();
    auto vS = rsubst.apply(v,0);
    TermList t;
    if (vS.isVar() && !temp.findBinding(vS.var(), t)) {
      temp.bind(vS.var(), v);
    }
  }
  VariableIterator vit2(orig2);
  while (vit2.hasNext()) {
    auto v = vit2.next();
    auto vS = rsubst.apply(v,0);
    TermList t;
    if (vS.isVar() && !temp.findBinding(vS.var(), t)) {
      temp.bind(vS.var(), v);
    }
  }
  orig1 = SubstHelper::apply(rsubst.apply(orig1,0), temp);
  orig2 = SubstHelper::apply(rsubst.apply(orig2,0), temp);
  return true;
}

ostream& operator<<(ostream& out, const Branch& b)
{
  switch (b.tag) {
    case BranchTag::T_EQUAL:
      out << "=";
      break;
    case BranchTag::T_GREATER:
      out << ">";
      break;
    case BranchTag::T_INCOMPARABLE:
      out << "?";
      break;
    case BranchTag::T_JUMP:
      out << b.jump_pos;
      break;
  }
  return out;
}

ostream& operator<<(ostream& out, const Instruction& n)
{
  out << "instr " << n.lhs << " " << n.rhs << " " << n.bs[0] << " " << n.bs[1] << " " << n.bs[2];
  return out;
}

std::string LPOComparator::toString() const
{
  std::stringstream str;
  switch (_res) {
    case BranchTag::T_EQUAL:
      str << "equal" << endl;
      break;
    case BranchTag::T_GREATER:
      str << "greater" << endl;
      break;
    case BranchTag::T_INCOMPARABLE:
      str << "incomparable" << endl;
      break;
    case BranchTag::T_JUMP:
      for (unsigned i = 0; i < _instructions.size(); i++) {
        str << i << " " << _instructions[i] << endl;
      }
      break;
  }
  return str.str();
}

void Branch::update(Branch eqBranch, Branch gtBranch, Branch incBranch, unsigned jump_offset)
{
  switch (tag) {
    case BranchTag::T_EQUAL:
      *this = eqBranch;
      break;
    case BranchTag::T_GREATER:
      *this = gtBranch;
      break;
    case BranchTag::T_INCOMPARABLE:
      *this = incBranch;
      break;
    case BranchTag::T_JUMP:
      jump_pos += jump_offset;
      break;
  }
}

void updateBranchInRange(Stack<Instruction>& st, unsigned startIndex, unsigned endIndex, Branch prevBranch, Branch newBranch)
{
  for (unsigned i = startIndex; i < endIndex; i++) {
    for (unsigned j = 0; j < 3; j++) {
      if (st[i].bs[j] == prevBranch) {
        st[i].bs[j] = newBranch;
      }
    }
  }
}

/**
 * Pushes instructions to the end of an instruction stack, while replacing each
 * equal/greater/incomparable branch with @b eqBranch, @b gtBranch, @b incBranch,
 * respectively, and adding an appropriate offset to any jump operation.
 */
void pushInstructions(Stack<Instruction>& st, const Stack<Instruction>& other, Branch eqBranch, Branch gtBranch, Branch incBranch)
{
  auto startIndex = st.size();
  for (const auto& n : other) {
    st.push(n);
    for (unsigned j = 0; j < 3; j++) {
      st.top().bs[j].update(eqBranch, gtBranch, incBranch, startIndex);
    }
  }
}

void deleteDuplicates(Stack<Instruction>& st)
{
  unsigned removedCnt = 0;
  Map<Instruction,unsigned> lastPos;
  std::vector<unsigned> removedAfter(st.size(),0);

  // First pass, remember the last position of
  // any duplicate instruction, and update every
  // jump to the respective last instruction.
  // Also, save how many elements we marked removed
  // after each not-removed element.
  for (int i = st.size()-1; i >= 0; i--) {
    auto& curr = st[i];
    for (unsigned j = 0; j < 3; j++) {
      if (curr.bs[j].tag == BranchTag::T_JUMP) {
        auto& jpos = curr.bs[j].jump_pos;
        jpos = lastPos.get(st[jpos]);
      }
    }

    unsigned* ptr;
    if (lastPos.getValuePtr(curr, ptr, i)) {
      removedAfter[i] = removedCnt;
    } else {
      removedCnt++;
    }
  }
  if (!removedCnt) {
    return;
  }
  // The first instruction should be completely
  // unique, otherwise we would be looping.
  ASS_EQ(lastPos.get(st[0]),0);

  // Second pass, create the resulting stack
  // without duplicates, and doing so apply
  // appropriate offsets to each jump where we
  // removed elements in between.
  Stack<Instruction> res;
  for (unsigned i = 0; i < st.size(); i++) {
    auto curr = st[i];
    if (lastPos.get(curr)!=i) {
      continue;
    }
    for (unsigned j = 0; j < 3; j++) {
      if (curr.bs[j].tag == BranchTag::T_JUMP) {
        auto& jpos = curr.bs[j].jump_pos;
        jpos -= removedAfter[i]-removedAfter[jpos];
        jpos -= i-res.size();
      }
    }
    res.push(curr);
  }
  swap(res,st);
}

#define INDEX_UNINITIALIZED -1

/**
 * Implements an @b LPO::majo call via instructions.
 */
pair<Stack<Instruction>,BranchTag> LPOComparator::majoChain(const LPO& lpo, TermList tl1, Term* t, unsigned i)
{
  Stack<Instruction> res;
  int prevIndex = INDEX_UNINITIALIZED;
  for (unsigned j = i; j < t->arity(); j++) {
    auto compRes = createHelper(tl1,*t->nthArgument(j),lpo);
    // If the comparison is 'greater', we skip this iteration.
    if (compRes->second == BranchTag::T_GREATER) {
      continue;
    }
    // Otherwise, if the comparison is 'equal' or 'incomparable',
    // we can return early with a negative result.
    if (compRes->second != BranchTag::T_JUMP) {
      res.reset();
      return make_pair(res,BranchTag::T_INCOMPARABLE);
    }
    // Update previous 'greater' branches
    // to a jump to the current index.
    if (prevIndex != INDEX_UNINITIALIZED) {
      updateBranchInRange(res, prevIndex, (unsigned)res.size(),
        Branch::gt(), Branch::jump(res.size()));
    }
    prevIndex = res.size();
    // Push the comparison instructions and replace each
    // 'equal' with 'incomparable' in them.
    pushInstructions(res, compRes->first, Branch::inc(), Branch::gt(), Branch::inc());
  }
  return make_pair(res,res.isEmpty() ? BranchTag::T_GREATER : BranchTag::T_JUMP);
}

/**
 * Implements an @b LPO::alpha call via instructions.
 */
pair<Stack<Instruction>,BranchTag> LPOComparator::alphaChain(const LPO& lpo, Term* s, unsigned i, TermList tl2)
{
  Stack<Instruction> res;
  int prevIndex = INDEX_UNINITIALIZED;
  for (unsigned j = i; j < s->arity(); j++) {
    auto compRes = createHelper(*s->nthArgument(j),tl2,lpo);
    // If the comparison is 'incomparable', we skip this iteration.
    if (compRes->second == BranchTag::T_INCOMPARABLE) {
      continue;
    }
    // Otherwise, if the comparison is 'greater' or 'equal',
    // we can return early with a positive result.
    if (compRes->second != BranchTag::T_JUMP) {
      res.reset();
      return make_pair(res,BranchTag::T_GREATER);
    }
    // Update previous 'incomparable' branches
    // to a jump to the current index.
    if (prevIndex != INDEX_UNINITIALIZED) {
      updateBranchInRange(res, prevIndex, (unsigned)res.size(),
        Branch::inc(), Branch::jump(res.size()));
    }
    prevIndex = res.size();
    // Push the comparison instructions and replace each
    // 'equal' with 'greater' in them.
    pushInstructions(res, std::move(compRes->first), Branch::gt(), Branch::gt(), Branch::inc());
  }
  return make_pair(res,res.isEmpty() ? BranchTag::T_INCOMPARABLE : BranchTag::T_JUMP);
}

pair<Stack<Instruction>,BranchTag>* LPOComparator::createHelper(TermList tl1, TermList tl2, const LPO& lpo)
{
  static DHMap<std::pair<TermList,TermList>,pair<Stack<Instruction>,Instruction::BranchTag>*> _cache;

  pair<Stack<Instruction>,BranchTag>** ptr;
  // We have a local cache for subresults to avoid too much computation.
  if (!_cache.getValuePtr(make_pair(tl1,tl2),ptr)) {
    return *ptr;
  }
  // Allocate on heap so that cache reallocation
  // won't affect partial results.
  auto res = new pair(Stack<Instruction>(), BranchTag::T_JUMP);
  *ptr = res;

  // Use compare here to filter out as many
  // precomputable comparisons as possible.
  auto comp = lpo.compare(tl1,tl2);
  if (comp != Ordering::INCOMPARABLE) {
    if (comp == Ordering::LESS) {
      (*ptr)->second = BranchTag::T_INCOMPARABLE;
    } else if (comp == Ordering::GREATER) {
      (*ptr)->second = BranchTag::T_GREATER;
    } else {
      (*ptr)->second = BranchTag::T_EQUAL;
    }
    return *ptr;
  }
  // If we have a variable, we cannot preprocess further.
  if (tl1.isVar() || tl2.isVar()) {
    (*ptr)->first.push(Instruction(tl1,tl2));
    (*ptr)->second = BranchTag::T_JUMP;
    return *ptr;
  }

  auto s = tl1.term();
  auto t = tl2.term();

  switch (lpo.comparePrecedences(s, t)) {
    case Ordering::EQUAL: {
      ASS(s->arity()); // constants cannot be incomparable

      int prevStartIndex = INDEX_UNINITIALIZED;
      unsigned prevEndIndex = 0; // to silence a gcc warning (we overwrite the value below anyway, at least where it matters)

       // copies for unification
      auto tl1s = tl1;
      auto tl2s = tl2;

      // lexicographic comparisons
      for (unsigned i = 0; i < s->arity(); i++) {
        auto s_arg = *tl1s.term()->nthArgument(i);
        auto t_arg = *tl2s.term()->nthArgument(i);
        auto compRes = createHelper(s_arg,t_arg,lpo);

        // If the comparison is 'equal', we skip this iteration.
        if (compRes->second == BranchTag::T_EQUAL) {
          // In the next iteration these two arguments are
          // assumed to be equal, so we can restrict the
          // comparisons by doing a unification here.
          ALWAYS(unify(s_arg,t_arg,tl1s,tl2s));
          continue;
        }

        auto majoRes = majoChain(lpo, tl1s, tl2s.term(), i+1);
        // If the comparison is 'greater', the rest of the
        // instructions consist of the majo chain.
        if (compRes->second == BranchTag::T_GREATER) {
          if (majoRes.second != BranchTag::T_JUMP) {
            // The majo chain is empty.
            if (prevStartIndex != INDEX_UNINITIALIZED) {
              // Update previous 'equal' values to the new return value.
              updateBranchInRange(res->first, prevStartIndex, prevEndIndex,
                Branch::eq(), Branch{ majoRes.second, 0 });
            } else {
              // Update the overall return value to the new return value.
              res->first.reset();
              res->second = majoRes.second;
            }
          } else {
            // The majo chain is non-empty, update the previous 'equal'
            // values to the new jump offset and push the chain.
            if (prevStartIndex != INDEX_UNINITIALIZED) {
              updateBranchInRange(res->first, prevStartIndex, prevEndIndex,
                Branch::eq(), Branch::jump(res->first.size()));
            }
            pushInstructions(res->first, majoRes.first, Branch::eq(), Branch::gt(), Branch::inc());
          }
          break;
        }

        auto alphaRes = alphaChain(lpo, tl1s.term(), i+1, tl2s);
        // If the comparison is 'incomparable', the rest of the
        // instructions consist of the alpha chain.
        if (compRes->second == BranchTag::T_INCOMPARABLE) {
            // The alpha chain is empty.
          if (alphaRes.second != BranchTag::T_JUMP) {
            if (prevStartIndex != INDEX_UNINITIALIZED) {
              // Update previous 'equal' values to the new return value.
              updateBranchInRange(res->first, prevStartIndex, prevEndIndex,
                Branch::eq(), Branch{ alphaRes.second, 0 });
            } else {
              // Update the overall return value to the new return value.
              res->first.reset();
              res->second = alphaRes.second;
            }
          } else {
            // The alpha chain is non-empty, update the previous 'equal'
            // values to the new jump offset and push the chain.
            if (prevStartIndex != INDEX_UNINITIALIZED) {
              updateBranchInRange(res->first, prevStartIndex, prevEndIndex,
                Branch::eq(), Branch::jump(res->first.size()));
            }
            pushInstructions(res->first, alphaRes.first, Branch::eq(), Branch::gt(), Branch::inc());
          }
          break;
        }

        // Otherwise, we have to create a branching point here.

        // Replace the previous 'equal' instructions with a jump to here.
        if (prevStartIndex != INDEX_UNINITIALIZED) {
          updateBranchInRange(res->first, prevStartIndex, prevEndIndex,
            Branch::eq(), Branch::jump(res->first.size()));
        }
        prevStartIndex = res->first.size();
        prevEndIndex = res->first.size() + compRes->first.size();
        // The majo branch will be after the comparison instructions
        Branch majoBranch{
          majoRes.second,
          (uint16_t)(majoRes.second == BranchTag::T_JUMP ? res->first.size() + compRes->first.size() : 0)
        };
        // The alpha branch will be after the majo branch instructions
        Branch alphaBranch{
          alphaRes.second,
          (uint16_t)(alphaRes.second == BranchTag::T_JUMP ? res->first.size() + compRes->first.size() + majoRes.first.size() : 0)
        };

        // push all three sets of instructions if needed
        pushInstructions(res->first, compRes->first, Branch::eq(), majoBranch, alphaBranch);

        if (majoRes.second == BranchTag::T_JUMP) {
          pushInstructions(res->first, majoRes.first, Branch::eq(), Branch::gt(), Branch::inc());
        }

        if (alphaRes.second == BranchTag::T_JUMP) {
          pushInstructions(res->first, alphaRes.first, Branch::eq(), Branch::gt(), Branch::inc());
        }

        if (!unify(s_arg,t_arg,tl1s,tl2s)) {
          // If we cannot unify, the rest of the iterations will be
          // 'incomparable', update the previous 'equal' values to that.
          updateBranchInRange(res->first, prevStartIndex, prevEndIndex, Branch::eq(), Branch::inc());
          break;
        }
      }
      break;
    }
    case Ordering::GREATER: {
      auto subres = majoChain(lpo, tl1, t, 0);
      if (subres.second == BranchTag::T_JUMP) {
        pushInstructions(res->first, subres.first, Branch::eq(), Branch::gt(), Branch::inc());
      } else {
        res->second = subres.second;
      }
      break;
    }
    case Ordering::LESS: {
      auto subres = alphaChain(lpo, s, 0, tl2);
      if (subres.second == BranchTag::T_JUMP) {
        pushInstructions(res->first, subres.first, Branch::eq(), Branch::gt(), Branch::inc());
      } else {
        res->second = subres.second;
      }
      break;
    }
    default:
      ASSERTION_VIOLATION;
  }
  ASS((res->second != BranchTag::T_JUMP) == res->first.isEmpty());
  deleteDuplicates(res->first);
  ASS((res->second != BranchTag::T_JUMP) == res->first.isEmpty());
  ASS(res->second != BranchTag::T_GREATER || lpo.compare(tl1,tl2)==Ordering::GREATER);
  ASS(res->second != BranchTag::T_EQUAL || lpo.compare(tl1,tl2)==Ordering::EQUAL);
  ASS(res->second != BranchTag::T_INCOMPARABLE || lpo.compare(tl1,tl2)==Ordering::LESS || lpo.compare(tl1,tl2)==Ordering::INCOMPARABLE);
  ptr = _cache.findPtr(make_pair(tl1,tl2));
  ASS(ptr);
  *ptr = res;
  return *ptr;
}

LPOComparator::LPOComparator(TermList tl1, TermList tl2, const LPO& lpo)
  : _lpo(lpo), _instructions(), _res()
{
  auto kv = createHelper(tl1, tl2, lpo);
  _instructions = kv->first;
  _res = kv->second;
}

bool LPOComparator::check(const SubstApplicator* applicator) const
{
  // we calculate all three values in each iteration
  // to optimise CPU branch prediction (the values are
  // computed regardless and hence no branching is needed)
  bool cond = _res == BranchTag::T_JUMP;
  bool res = _res == BranchTag::T_GREATER;
  auto curr = _instructions.begin();

  while (cond) {
    auto comp = _lpo.lpo(AppliedTerm(curr->lhs,applicator,true),AppliedTerm(curr->rhs,applicator,true));
    const auto& branch = curr->getBranch(comp);

    cond = branch.tag == BranchTag::T_JUMP;
    res = branch.tag == BranchTag::T_GREATER;
    curr = _instructions.begin() + branch.jump_pos;
  }
  return res;
}

}
