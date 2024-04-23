/******************************************************************************
 * Top contributors (to current version):
 *   Alan Prado, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * PB-blaster used to PB-blast to 0-1 linear inequalities
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__PB__NODE_BLASTER_H
#define CVC5__THEORY__BV__PB__NODE_BLASTER_H

#include <sstream>
#include <vector>

#include "theory/bv/pb/pb_blaster.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

/**
 * Implementation of a simple PB-blaster.
 *
 * Implements the bare minimum to PB-blast bit-vector atoms/terms.
 */
class PseudoBooleanBlaster : public TPseudoBooleanBlaster<unsigned,
                             std::string>, protected EnvObj
{
 public:
  PseudoBooleanBlaster(Env& env, TheoryState* state);
  ~PseudoBooleanBlaster() = default;

  /** PB-blast term 'node' and return variables and constraints in 'sp'. */
  void blastTerm(TNode node, Subproblem& sp) override;
  /** PB-blast atom 'node'. */
  void blastAtom(TNode node) override;
  /** Store Subproblem representing a PB-blasted atom. */
  void storeAtom(TNode atom, Subproblem atom_bb) override;
  /** Simplify a vector of constraints. */
  void simplifyConstraints(std::vector<std::string> constraints, Subproblem& sp) override;
  /** Store Subproblem representing a PB-blasted term. */
  void storeTerm(TNode node, const Subproblem& sp) override;
  /** Check if atom was already PB-blasted. */
  bool hasAtom(TNode atom) const override;
  /** Get PB-blasted Subproblem stored for atom. */
  Subproblem getStoredAtom(TNode node);
  /** Create 'variables' for bit-vector 'node'. */
  void makeVariables(TNode node, Subproblem& sp, unsigned spare=0) override;
  /** Create a new variable not yet used in the solver. */
  unsigned newVariable() override;
  Node newVariable2() override;

 private:
  /** Caches PB-blasted atoms. */
  std::unordered_map<Node, Subproblem> d_pbAtoms;
  /** Counts variables used so far. */
  unsigned d_varCounter;
  unsigned d_varCounter2;
};

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif
