/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "SATSubsumption/SubsumptionLogger.hpp"
#include "Lib/Timer.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"
#include "Parse/TPTP.hpp"

using namespace Indexing;
using namespace Kernel;
using namespace SATSubsumption;
using namespace std;

ForwardSubsumptionLogger::ForwardSubsumptionLogger(vstring const& filename_base)
  : m_file_slog{}
  , m_file_tptp{}
  , m_tptp{&m_file_tptp}
{
  vstring path_slog = filename_base + ".slog";
  vstring path_tptp = filename_base + ".p";
  m_file_slog.open(path_slog.c_str());
  m_file_tptp.open(path_tptp.c_str());
  if (!m_file_slog.is_open()) {
    USER_ERROR("unable to open file for writing: ", path_slog);
  }
  if (!m_file_tptp.is_open()) {
    USER_ERROR("unable to open file for writing: ", path_tptp);
  }
}

ForwardSubsumptionLogger::LitIdx ForwardSubsumptionLogger::logLiteral(Literal* lit)
{
  if (LitIdx* idx = m_logged_lits.findPtr(lit))
    return *idx;
  LitIdx idx = m_next_lit++;
  ALWAYS(m_logged_lits.insert(lit, idx));

  TimeoutProtector _tp;
  vostringstream id_stream;
  id_stream << "l_" << idx;
  m_tptp.printWithRole(id_stream.str(), "hypothesis", lit);

  return idx;
}

bool ForwardSubsumptionLogger::ClauseInfo::is_equal_to(Clause* cl) const
{
  if (lits.size() != cl->length())
    return false;
  return std::equal(lits.begin(), lits.end(), cl->literals());
}

ForwardSubsumptionLogger::ClauseIdx ForwardSubsumptionLogger::logClause(Clause* cl)
{
  if (ClauseInfo* info = m_logged_clauses.findPtr(cl)) {
    if (info->is_equal_to(cl))
      return info->idx;
    else
      m_logged_clauses.remove(cl);
  }

  TimeoutProtector _tp;
  ClauseIdx clause_idx = m_next_clause++;
  ClauseInfo info;
  info.idx = clause_idx;

  m_file_slog << "C " << clause_idx;
  for (unsigned i = 0; i < cl->length(); ++i) {
    Literal* lit = (*cl)[i];
    LitIdx lit_idx = logLiteral(lit);
    ASS(lit_idx != 0);
    info.lits.push_back(lit);
    m_file_slog << ' ' << lit_idx;
  }
  m_file_slog << " 0" << std::endl;

  ALWAYS(m_logged_clauses.emplace(cl, std::move(info)));
  return clause_idx;
}

void ForwardSubsumptionLogger::beginLoop(Clause* main_premise)
{
  TimeoutProtector _tp;
  ClauseIdx main_idx = logClause(main_premise);
  m_file_slog << "L " << main_idx << std::endl;
  m_main_premise = main_premise;
}

void ForwardSubsumptionLogger::logSubsumption(Clause* side_premise, Clause* main_premise, int result)
{
  ASS(main_premise == m_main_premise);
  TimeoutProtector _tp;
  ClauseIdx side_idx = logClause(side_premise);
  m_file_slog << "S " << side_idx << ' ' << result << std::endl;
}

void ForwardSubsumptionLogger::logSubsumptionResolution(Clause* side_premise, Clause* main_premise, Clause* result)
{
  ASS(main_premise == m_main_premise);
  TimeoutProtector _tp;
  ClauseIdx side_idx = logClause(side_premise);
  m_file_slog << "R " << side_idx << ' ' << (!!result) << std::endl;
}

DHMap<uint32_t, Literal*> getNumberedLiterals(UnitList const* units)
{
  DHMap<uint32_t, Literal*> literals;

  vstring name;
  vstring const prefix = "l_";

  for (; UnitList::isNonEmpty(units); units = units->tail()) {
    Clause* const clause = units->head()->asClause();
    // std::cerr << "Clause: " << clause->toString() << std::endl;

    // Find input formula from which the clause was derived
    Unit* unit = clause;
    while (true) {
      auto const& inference = unit->inference();
      auto parents = inference.iterator();
      if (!inference.hasNext(parents))
        break;  // no parents -> we have an axiom
      // there's still parents to process
      Unit* const parent = inference.next(parents);
      ASS(!inference.hasNext(parents));  // we expect exactly one parent
      unit = parent;
    }

    Parse::TPTP::findAxiomName(unit, name);

    if (std::strncmp(name.c_str(), prefix.c_str(), prefix.size()) == 0) {
      if (clause->length() != 1) {
        USER_ERROR("expected unit clause, but has length ", clause->length());
      }

      // We need to get the literal from the input unit,
      // because we need the original literal (before variable names are normalized).
      ASS(!unit->isClause());
      Formula* f = unit->getFormula();
      while (f->connective() == FORALL)
        f = f->qarg();
      ASS_EQ(f->connective(), LITERAL);

      Literal* const lit = f->literal();
      uint32_t const lit_idx = std::strtoul(name.c_str() + prefix.size(), nullptr, 10);
      bool const inserted = literals.insert(lit_idx, lit);
      if (!inserted) {
        USER_ERROR("more than one literal with index: ", lit_idx);
      }
    }
  } // for (units)

  return literals;
}

template <typename T>
void read_value(std::istream& in, T& val, char const* name)
{
  if (!(in >> val)) {
    USER_ERROR("expected <", name, ">");
  }
}

// L <main_premise_idx>
// C <clause_idx> <lit_1> ... <lit_n> 0
// S <side_premise_idx> <result>
// R <side_premise_idx> <result>
void SubsumptionBenchmark::load_from(UnitList const* units, vstring const& slog_filename)
{
  std::cout << "\% Loading subsumption log from " << slog_filename << std::endl;

  DHMap<uint32_t, Literal*> const literals = getNumberedLiterals(units);
  DHMap<uint32_t, Clause*> clauses;

  std::ifstream slog{slog_filename.c_str()};

  auto read_literal = [&literals, &slog]() -> Literal* {
    uint32_t idx;
    if (!(slog >> idx)) {
      USER_ERROR("expected <literal_idx>");
    }
    if (idx == 0) {
      return nullptr;
    }
    Literal* lit = literals.get(idx, nullptr);
    if (!lit) {
      USER_ERROR("invalid <literal_idx>");
    }
    return lit;
  };

  auto read_clause = [&clauses, &slog](char const* name) -> Clause* {
    uint32_t idx;
    if (!(slog >> idx)) {
      USER_ERROR("expected <", name, "_idx>");
    }
    Clause* cl = clauses.get(idx, nullptr);
    if (!cl) {
      USER_ERROR("invalid <", name, "_idx>");
    }
    return cl;
  };

  ForwardSubsumptionLoop loop;
  vvector<Literal*> lits;
  std::string cmd;

  while (slog >> cmd) {
    if (cmd == "C") {
      // clause definition
      uint32_t idx;
      read_value(slog, idx, "clause_idx");
      ASS(lits.empty());
      while (Literal* lit = read_literal()) {
        lits.push_back(lit);
      }
      Clause* cl = new (lits.size()) Clause(lits.size(), FromInput(UnitInputType::AXIOM));
      for (unsigned i = 0; i < lits.size(); ++i) {
        (*cl)[i] = lits[i];
      }
      lits.clear();
      bool const inserted = clauses.insert(idx, cl);
      if (!inserted) {
        USER_ERROR("more than one clause with index: ", idx);
      }
    }
    else if (cmd == "L") {
      // new loop iteration
      if (!loop.empty()) {
        fwd_loops.push_back(std::move(loop));
      }
      loop.reset();
      loop.main_premise = read_clause("main_premise");
    }
    else if (cmd == "S") {
      // subsumption
      SSRInstance s;
      s.do_subsumption = true;
      s.side_premise = read_clause("side_premise");
      read_value(slog, s.subsumption_result, "result");  // TODO: on error, could continue with result 'unknown'
      loop.instances.push_back(s);
    }
    else if (cmd == "R") {
      // subsumption resolution
      SSRInstance sr;
      sr.do_subsumption_resolution = true;
      sr.side_premise = read_clause("side_premise");
      read_value(slog, sr.subsumption_resolution_result, "result");  // TODO: on error, could continue with result 'unknown'
      // try to merge with previous instance, if possible
      bool merged = false;
      if (!loop.instances.empty()) {
        SSRInstance& s = loop.instances.back();
        if (s.side_premise == sr.side_premise && !s.do_subsumption_resolution) {
          s.do_subsumption_resolution = true;
          s.subsumption_resolution_result = sr.subsumption_resolution_result;
          merged = true;
        }
      }
      if (!merged) {
        loop.instances.push_back(sr);
      }
    }
    else {
      USER_ERROR("expected 'C', 'L', 'S', or 'R'");
    }
  }

  if (!loop.empty()) {
    fwd_loops.push_back(std::move(loop));
  }
}
