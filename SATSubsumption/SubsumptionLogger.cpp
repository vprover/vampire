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
  ASS(m_file_slog.is_open());
  ASS(m_file_tptp.is_open());
}

ForwardSubsumptionLogger::LitIdx ForwardSubsumptionLogger::logLiteral(Literal* lit)
{
  if (LitIdx* idx = m_logged_lits.findPtr(lit))
    return *idx;
  LitIdx idx = m_next_lit++;
  ALWAYS(m_logged_lits.insert(lit, idx));

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
  ClauseIdx idx = m_next_clause++;
  ClauseInfo info;

  m_file_slog << "C " << idx;
  for (unsigned i = 0; i < cl->length(); ++i) {
    Literal* lit = (*cl)[i];
    info.lits.push_back(lit);
    m_file_slog << ' ' << logLiteral(lit);
  }
  m_file_slog << '\n';

  ALWAYS(m_logged_clauses.emplace(cl, std::move(info)));
  return idx;
}

void ForwardSubsumptionLogger::beginLoop(Clause* main_premise)
{
  ClauseIdx main_idx = logClause(main_premise);
  m_file_slog << "L " << main_idx << '\n';
  m_main_premise = main_premise;
}

void ForwardSubsumptionLogger::logSubsumption(Clause* side_premise, Clause* main_premise, int result)
{
  ASS(main_premise == m_main_premise);
  ClauseIdx side_idx = logClause(side_premise);
  m_file_slog << "S " << side_idx << ' ' << result << '\n';
}

void ForwardSubsumptionLogger::logSubsumptionResolution(Clause* side_premise, Clause* main_premise, Clause* result)
{
  ASS(main_premise == m_main_premise);
  ClauseIdx side_idx = logClause(side_premise);
  m_file_slog << "R " << side_idx << ' ' << (!!result) << '\n';
}

void ForwardSubsumptionLogger::flush()
{
  m_file_slog.flush();
  m_file_tptp.flush();
}
