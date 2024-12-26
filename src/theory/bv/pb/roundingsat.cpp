/******************************************************************************
 * Top contributors (to current version):
 *   Alan Prado
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrapper for the RoundingSat PB Solver.
 *
 * Implementation of the RoundingSat PB solver for cvc5 (bit-vectors).
 */

#ifdef CVC5_USE_ROUNDINGSAT

#include "theory/bv/pb/roundingsat.h"

//#include "base/check.h"
//#include "options/main_options.h"
//#include "options/proof_options.h"
//#include "prop/theory_proxy.h"
//#include "util/resource_manager.h"
//#include "util/statistics_registry.h"
#include "util/rational.h"

#include <cstdio>

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {


RoundingSatSolver::RoundingSatSolver(std::string solverPath,
                                     Env& env,
                                     StatisticsRegistry& registry,
                                     const std::string& name,
                                     bool logProofs)
    : EnvObj(env),
      d_binPath(solverPath),
      d_logProofs(logProofs),
      d_statistics(registry, name)
{
  if (logProofs) Unimplemented();
  init();  // TODO: Remove this? Make a private constructor?
}

void RoundingSatSolver::init()
{
  Trace("bv-pb-roundingsat") << "RoundingSatSolver::init\n";
  d_pboPath = std::tmpnam(nullptr);
  d_pboPath += ".opb";
  (void) std::ofstream(d_pboPath, std::ostream::app);
  d_pboFile.open(d_pboPath);
}

void RoundingSatSolver::addVariable(Node variable)
{
  Trace("bv-pb-roundingsat") << "RoundingSatSolver::addVariable " << variable << "\n";
  Assert(variable.isVar());
  if (d_variableSet.count(variable)) return;
  d_variableSet.emplace(variable);
  // TODO: ++d_statistics.d_numVariables;
}

void RoundingSatSolver::addConstraint(Node constraint)
{
  Trace("bv-pb-roundingsat") << "RoundingSatSolver::addConstraint " << constraint << "\n";
  if (d_constraintSet.count(constraint)) return;

  std::vector<std::string> variables, coefficients;
  std::string result;

  Node linear_form = constraint[0];

  if (linear_form.getKind() == Kind::MULT)
  {
    Assert(linear_form.getNumChildren() == 2);
    Assert(linear_form[0].isConst());
    Assert(linear_form[1].isVar());
    coefficients.push_back(linear_form[0].getConst<Rational>().toString());
    if (!d_variableSet.count(linear_form[1])) addVariable(linear_form[1]);
    variables.push_back(linear_form[1].toString());
  }

  else if (linear_form.getKind() == Kind::ADD)
  {
    for (const Node& term : linear_form)
    {
      Assert(term.getNumChildren() == 2);
      Assert(term[0].isConst());
      Assert(term[1].isVar());
      coefficients.push_back(term[0].getConst<Rational>().toString());
      if (!d_variableSet.count(term[1])) addVariable(term[1]);
      variables.push_back(term[1].toString());
    }
  }

  else Unreachable();

  for (unsigned i = 0; i < variables.size(); i++)
  {
    if (coefficients[i][0] != '-') result += "+";
    result += coefficients[i] + " ";
    result += variables[i] + " ";
  }

  if (constraint.getKind() == Kind::EQUAL) result += "= ";
  else result += ">= ";
  result += constraint[1].getConst<Rational>().toString();
  result += ";\n";

  // TODO: ++d_statistics.d_numConstraints;
  d_opbConstraints.push_back(result);
  Trace("bv-pb-roundingsat") << "    produces " << result;
}

PbSolveState RoundingSatSolver::solve()
{
  Trace("bv-pb-roundingsat") << "RoundingSatSolver::solve\n";
  d_pboFile << "* #variable= " << d_variableSet.size() << " #constraint= "
            << d_opbConstraints.size() << "\n";
  for (std::string constraint : d_opbConstraints)
  {
    d_pboFile << constraint;
  }
  d_pboFile.close();

  if (TraceIsOn("bv-pb-roundingsat"))
  {
    d_pboFile.open(d_pboPath);
    Trace("bv-pb-roundingsat")
      << "    Contents of the file " << d_pboPath << " are:\n";
    d_pboFile.seekg(0);
    std::string line;
    while ( getline (d_pboFile,line) )
    {
      Trace("bv-pb-roundingsat") << "        " << line << '\n';
    }
    d_pboFile.close();
  }

  std::string output_file = std::tmpnam(nullptr);
  output_file += ".txt";
  std::string command = d_binPath;
  command += " --bits-learned=0 --bits-overflow=0 --bits-reduced=0 --lp=0";
  command += " " + d_pboPath + " > " + output_file;
  Trace("bv-pb-roundingsat") << "    The command is: " << command << "\n";

  std::system(command.c_str());

  std::fstream output;
  output.open(output_file);
  Trace("bv-pb-roundingsat") << "    RoundingSat result:\n";
  std::string line;
  std::string result;
  while (getline (output,line))
  {
    Trace("bv-pb-roundingsat") << "        " << line << '\n';
    if (line[0] == 's')
    {
      result = line.substr(2, line.length() - 2);
    }
  }
  output.close();

  if (result == "SATISFIABLE") return PB_SAT;
  if (result == "UNSATISFIABLE") return PB_UNSAT;
  return PB_UNKNOWN;
}

RoundingSatSolver::Statistics::Statistics(StatisticsRegistry& registry, const std::string& prefix)
{}

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif  // CVC5_USE_ROUNDINGSAT
