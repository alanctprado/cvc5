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
#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__PB__PB_PROOF_RULES_H
#define CVC5__THEORY__BV__PB__PB_PROOF_RULES_H

#include "smt/env_obj.h"

namespace cvc5::internal {

namespace theory {
namespace bv {
namespace pb {

class PbProofRules : protected EnvObj
{
 public:
  PbProofRules(Env& env);
  ~PbProofRules(){};

  Node parseLine(const std::string& line);

 private:
  /** Rules */
  Node assumption(const std::string& line);
  Node constraintEquals(const std::string& line);
  Node constraintImplies(const std::string& line);
  Node constraintImpliesGetImplied(const std::string& line);
  Node deleteConstraints(const std::string& line);
  Node deleteConstraints2(const std::string& line);
  Node isContradiction(const std::string& line);
  Node loadAxiom(const std::string& line);
  Node loadFormula(const std::string& line);
  Node markCore(const std::string& line);
  Node objectiveBound(const std::string& line);
  Node originalSolution(const std::string& line);
  Node reversePolishNotation(const std::string& line);
  Node reverseUnitPropagation(const std::string& line);
  Node setLevel(const std::string& line);
  Node solution(const std::string& line);
  Node wipeLevel(const std::string& line);

  /** Internal */
  void initializeRules();
  std::unordered_map<std::string, std::function<Node(const std::string&)>> rules;
};

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__PB__PB_PROOF_RULES_H */
