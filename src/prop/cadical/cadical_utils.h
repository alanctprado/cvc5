/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility functions for CaDiCaL SAT solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__CADICAL__CADICAL_UTILS_H
#define CVC5__PROP__CADICAL__CADICAL_UTILS_H

#include "cadical.hpp"

#include "base/check.h"
#include "prop/sat_solver_types.h"
#include "util/resource_manager.h"

namespace cvc5::internal {
namespace prop {

/**
 * Terminator class that notifies CaDiCaL to terminate when the resource limit
 * is reached (used for resource limits specified via --rlimit or --tlimit).
 */
class ResourceLimitTerminator : public CaDiCaL::Terminator
{
 public:
  ResourceLimitTerminator(ResourceManager& resmgr) : d_resmgr(resmgr){};

  inline bool terminate() override
  {
    d_resmgr.spendResource(Resource::BvSatStep);
    return d_resmgr.out();
  }

 private:
  ResourceManager& d_resmgr;
};

typedef int64_t CadicalVar;
typedef int64_t CadicalLit;

inline SatValue toSatValue(int result)
{
  if (result == 10) return SAT_VALUE_TRUE;
  if (result == 20) return SAT_VALUE_FALSE;
  Assert(result == 0);
  return SAT_VALUE_UNKNOWN;
}

inline SatValue toSatValueLit(int value)
{
  // NOTE: CaDiCaL returns lit/-lit for true/false.
  if (value > 0) return SAT_VALUE_TRUE;
  Assert(value < 0);
  return SAT_VALUE_FALSE;
}

inline CadicalLit toCadicalLit(const SatLiteral lit)
{
  return lit.isNegated() ? -lit.getSatVariable() : lit.getSatVariable();
}

inline SatLiteral toSatLiteral(CadicalLit lit)
{
  return SatLiteral(std::abs(lit), lit < 0);
}

inline CadicalVar toCadicalVar(SatVariable var) { return var; }

}  // namespace cvc5::internal
}  // namespace prop

#endif  // CVC5__PROP__CADICAL__CADICAL_UTILS_H
