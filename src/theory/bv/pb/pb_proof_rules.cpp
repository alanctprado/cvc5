/******************************************************************************
 * Top contributors (to current version):
 *   Alan Prado
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * PB proof rules
 */

#include "theory/bv/pb/pb_proof_rules.h"
#include "util/string.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb{

PbProofRules::PbProofRules(Env& env) : EnvObj(env)
{
  initializeRules();
}

void PbProofRules::initializeRules()
{
  rules = {
    {"del", [this](const std::string& line) { return deleteConstraints2(line); }},
    {"d", [this](const std::string& line) { return deleteConstraints(line); }},
    {"a", [this](const std::string& line) { return assumption(line); }},
    {"u", [this](const std::string& line) { return reverseUnitPropagation(line); }},
    {"rup", [this](const std::string& line) { return reverseUnitPropagation(line); }},
    {"e", [this](const std::string& line) { return constraintEquals(line); }},
    {"i", [this](const std::string& line) { return constraintImplies(line); }},
    {"j", [this](const std::string& line) { return constraintImpliesGetImplied(line); }},
    {"v", [this](const std::string& line) { return solution(line); }},
    {"ov", [this](const std::string& line) { return originalSolution(line); }},
    {"o", [this](const std::string& line) { return objectiveBound(line); }},
    {"c", [this](const std::string& line) { return isContradiction(line); }},
    {"p", [this](const std::string& line) { return reversePolishNotation(line); }},
    {"pol", [this](const std::string& line) { return reversePolishNotation(line); }},
    {"f", [this](const std::string& line) { return loadFormula(line); }},
    {"l", [this](const std::string& line) { return loadAxiom(line); }},
    {"core", [this](const std::string& line) { return markCore(line); }},
    {"#", [this](const std::string& line) { return setLevel(line); }},
    {"w", [this](const std::string& line) { return wipeLevel(line); }}
  };
}

Node PbProofRules::parseLine(const std::string& line)
{
  size_t space_position = line.find(' ');
  if (space_position == 0 || space_position == std::string::npos)
  {
    Unreachable() << "\nPbProofRules::parseLine: failed parsing line:\n" << line << "\n";
  }
  std::string ruleId = line.substr(0, space_position);
  auto it = rules.find(ruleId);
  if (it == rules.end())
  {
    Unreachable() << "\nPbProofRules::parseLine: failed parsing line:\n" << line << "\n";
  }
  return it->second(line);
}

Node PbProofRules::assumption(const std::string& line)
{
  Unimplemented();
}

Node PbProofRules::constraintEquals(const std::string& line)
{
  Unimplemented();
}

Node PbProofRules::constraintImplies(const std::string& line)
{
  Unimplemented();
}

Node PbProofRules::constraintImpliesGetImplied(const std::string& line)
{
  Unimplemented();
}

Node PbProofRules::deleteConstraints(const std::string& line)
{
  Unimplemented();
}

Node PbProofRules::deleteConstraints2(const std::string& line)
{
  Unimplemented();
}

Node PbProofRules::isContradiction(const std::string& line)
{
  Trace("bv-pb-proof") << "isContradiction\n";
  Trace("bv-pb-proof") << line << "\n";
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkConst(String(line));
}

Node PbProofRules::loadAxiom(const std::string& line)
{
  Trace("bv-pb-proof") << "loadAxiom";
  Trace("bv-pb-proof") << line << "\n";
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkConst(String(line));
}

Node PbProofRules::loadFormula(const std::string& line)
{
  Unimplemented();
}

Node PbProofRules::markCore(const std::string& line)
{
  Unimplemented();
}

Node PbProofRules::objectiveBound(const std::string& line)
{
  Unimplemented();
}

Node PbProofRules::originalSolution(const std::string& line)
{
  Unimplemented();
}

Node PbProofRules::reversePolishNotation(const std::string& line)
{
  Trace("bv-pb-proof") << "reversePolishNotation\n";
  Trace("bv-pb-proof") << line << "\n";
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkConst(String(line));
}

Node PbProofRules::reverseUnitPropagation(const std::string& line)
{
  Trace("bv-pb-proof") << "reverseUnitPropagation\n";
  Trace("bv-pb-proof") << line << "\n";
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkConst(String(line));
}

Node PbProofRules::setLevel(const std::string& line)
{
  Unimplemented();
}

Node PbProofRules::solution(const std::string& line)
{
  Unimplemented();
}

Node PbProofRules::wipeLevel(const std::string& line)
{
  Unimplemented();
}


}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
