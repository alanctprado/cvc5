/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for managing witness form conversion in proofs.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__WITNESS_FORM_H
#define CVC5__SMT__WITNESS_FORM_H

#include <unordered_set>

#include "proof/conv_proof_generator.h"
#include "proof/method_id.h"
#include "proof/proof.h"
#include "proof/proof_generator.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

namespace theory {
class Rewriter;
}

namespace smt {

/** A response to requiresWitnessFormTransform/requiresWitnessFormIntro */
enum WitnessReq
{
  // we require converting to witness form and rewriting again
  WITNESS_AND_REWRITE,
  // we require converting to witness form
  WITNESS,
  // we require rewriting again
  REWRITE,
  // we don't require anything
  NONE
};
/** Print method */
std::ostream& operator<<(std::ostream& out, WitnessReq wr);

/**
 * The witness form proof generator, which acts as a wrapper around a
 * TConvProofGenerator for adding rewrite steps for witness introduction.
 *
 * The proof steps managed by this class are stored in a context-independent
 * manager, which matches how witness forms are managed in SkolemManager.
 */
class WitnessFormGenerator : protected EnvObj, public ProofGenerator
{
 public:
  WitnessFormGenerator(Env& env);
  ~WitnessFormGenerator() {}
  /**
   * Get proof for, which expects an equality of the form t = toWitness(t).
   * This returns a proof based on the term conversion proof generator utility.
   * This proof may contain open assumptions of the form:
   *   k = toWitness(k)
   * Each of these assumptions are included in the set getWitnessFormEqs()
   * below after returning this call.
   */
  std::shared_ptr<ProofNode> getProofFor(Node eq) override;
  /** Identify */
  std::string identify() const override;
  /**
   * Does the rewrite require witness form conversion?
   * When calling this method, it should be the case that:
   *   Rewriter::rewrite(toWitness(t)) == Rewriter::rewrite(toWitness(s))
   * The rule MACRO_SR_PRED_TRANSFORM concludes t == s if the above holds.
   * This method returns false if:
   *   rewriteViaMethod(t, idr) == rewriteViaMethod(s, idr)
   * which means that the proof of the above fact does not need to do
   * witness form conversion to prove conclusions of MACRO_SR_PRED_TRANSFORM.
   */
  WitnessReq requiresWitnessFormTransform(Node t, Node s, MethodId idr) const;
  /**
   * Same as above, with s = true. This is intended for use with
   * MACRO_SR_PRED_INTRO.
   */
  WitnessReq requiresWitnessFormIntro(Node t, MethodId idr) const;
  /**
   * Get witness form equalities. This returns a set of equalities of the form:
   *   k = toWitness(k)
   * where k is a skolem, containing all rewrite steps used in calls to
   * getProofFor during the entire lifetime of this generator.
   */
  const std::unordered_set<Node>& getWitnessFormEqs() const;

 private:
  /**
   * Convert to witness form. This internally constructs rewrite steps that
   * suffice to show t = toWitness(t) using the term conversion proof generator
   * of this class (d_tcpg).
   */
  Node convertToWitnessForm(Node t);
  /** The true node */
  Node d_true;
  /** The rewriter we are using */
  theory::Rewriter* d_rewriter;
  /** The term conversion proof generator */
  TConvProofGenerator d_tcpg;
  /** The nodes we have already added rewrite steps for in d_tcpg */
  std::unordered_set<Node> d_visited;
  /** The set of equalities added as proof steps */
  std::unordered_set<Node> d_eqs;
  /** Lazy proof storing witness intro steps */
  LazyCDProof d_wintroPf;
  /** CDProof for justifying purification existentials */
  CDProof d_pskPf;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
