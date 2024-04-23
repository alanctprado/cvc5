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
 * Various utility functions for PB-blasting.
 */

#include <initializer_list>
#include <iterator>
#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__PB__PB_BLAST_UTILS_H
#define CVC5__THEORY__BV__PB__PB_BLAST_UTILS_H

#include <ostream>
#include <vector>
#include "expr/node.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

template <class T, class U> class TPseudoBooleanBlaster;

template <class T, class U>
using TSubproblem = std::pair<std::vector<T>, std::vector<U>>;

template <class T> std::string toString (const std::vector<T>& bv);
template <class T> std::string mkPbVar(T var, long long coeff);
template <class T> std::string bvToUnsigned(const std::vector<T>& bv,
                                            int sign = 1);
template <class T> std::string bvToClause(const std::vector<T>& bv);

/**
 * Term Node format:
 * SEXPR ( SEXPR (variables),
 *         SEXPR (term Constraints),
 *         children...
 *       )
 */
template <class T> inline
T mkTermNode(std::vector<T> variables, std::vector<T> constraints, NodeManager* nm)
{
  T variables_t = nm->mkNode(Kind::SEXPR, variables);
  T constraints_t = nm->mkNode(Kind::SEXPR, constraints);
  std::vector<T> result = {variables_t, constraints_t};
  T result_t = nm->mkNode(Kind::SEXPR, result);
  return result_t;
} 

/**
 * Atom Node format:
 * SEXPR ( Constraint,
 *         children...
 *       )
 */
template <class T> inline
T mkAtomNode(T constraint, std::vector<T> children, NodeManager* nm)
{
  std::vector<T> result = {constraint};
  std::move(children.begin(), children.end(), std::back_inserter(result));
  T result_t = nm->mkNode(Kind::SEXPR, result);
  return result_t;
} 

/**
 * Constraint Node format:
 * SEXPR ( SEXPR (type, SEXPR (vars, coeffs), val),
 *         children...
 *       )
 */
template <class T> inline
T mkConstraintNode(std::vector<T> variables, std::vector<T> coefficients,
                       T type, T value, NodeManager* nm)
{
  T variables_t = nm->mkNode(Kind::SEXPR, variables);
  T coefficients_t = nm->mkNode(Kind::SEXPR, coefficients);
  T result = nm->mkNode(Kind::SEXPR, {type, variables_t, coefficients_t, value});
  return result;
} 

template <class T> inline
std::string toString (const std::vector<T>& bv)
{
  std::ostringstream os;
  os << "[ ";
  for (unsigned i = 0; i < bv.size(); i++) { os << bv[i] << " "; }
  os << "]";
  return os.str();
} 

template <class T> inline
std::string mkPbVar(T var, long long coeff)
{
  std::string sign = coeff >= 0 ? "+" : "-";
  return sign + std::to_string(llabs(coeff)) + " x" + std::to_string(var);
}

template <class T> inline
std::string mkPbVar(T var)
{
  return "+1 x" + std::to_string(var);
}

template <class T> inline
std::string bvToUnsigned(const std::vector<T>& bv, int sign)
{
  std::ostringstream os;
  long long coeff = (1 << (bv.size() - 1)) * sign;
  for (unsigned i = 0; i < bv.size(); i++)
  {
    os << mkPbVar(bv[i], coeff) << " ";
    coeff /= 2;
  }
  return os.str();
} 

template <class T = Node> inline
std::vector<T> bvToUnsigned2(unsigned size, NodeManager* nm, int sign = 1)
{
  std::ostringstream os;
  int coeff = (1 << size) * sign;
  std::vector<T> coefficients(size);
  std::generate(coefficients.begin(), coefficients.end(), [&coeff, nm] {
      return nm->mkConstInt(Rational(coeff /= 2)); });
  return coefficients;
}

template <class T> inline
std::string bvToClause(const std::vector<T>& bv)
{
  std::ostringstream os;
  for (unsigned i = 0; i < bv.size(); i++) { os << mkPbVar(bv[i]) << " "; }
  os <<  ">= 1 ;\n";
  return os.str();
} 

template <class T> std::vector<std::string> mkPbXor(T a, T b, T res);

template <class T> inline
std::vector<std::string> mkPbXor(T a, T b, T res)
{
  std::vector<std::string> constraints;
  constraints.push_back(mkPbVar(res, -1) + " " + mkPbVar(a, 1) + " "
                        + mkPbVar(b, 1) + " >= 0 ;\n");
  constraints.push_back(mkPbVar(res, -1) + " " + mkPbVar(a, -1) + " "
                        + mkPbVar(b, -1) + " >= -2 ;\n");
  constraints.push_back(mkPbVar(res, 1) + " " + mkPbVar(a, 1) + " "
                        + mkPbVar(b, -1) + " >= 0 ;\n");
  constraints.push_back(mkPbVar(res, 1) + " " + mkPbVar(a, -1) + " "
                        + mkPbVar(b, 1) + " >= 0 ;\n");
  return constraints;
}

template <class T> inline
int ceil_log2(T a)
{
  unsigned long long x = (unsigned long long) a;
  static const unsigned long long t[6] = {
    0xFFFFFFFF00000000ull, 0x00000000FFFF0000ull, 0x000000000000FF00ull,
    0x00000000000000F0ull, 0x000000000000000Cull, 0x0000000000000002ull
  };
  int y = (((x & (x - 1)) == 0) ? 0 : 1);
  int j = 32;
  int i;
  for (i = 0; i < 6; i++)
  {
    int k = (((x & t[i]) == 0) ? 0 : j);
    y += k;
    x >>= k;
    j >>= 1;
  }
  return y;
}

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif  // CVC5__THEORY__BV__PB__PB_BLAST_UTILS_H
