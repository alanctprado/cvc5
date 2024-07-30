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
 * External propagator for the CaDiCaL SAT Solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__CADICAL__CADICAL_PROPAGATOR_H
#define CVC5__PROP__CADICAL__CADICAL_PROPAGATOR_H

#include <cadical.hpp>

#include "prop/cadical/cadical_utils.h"
#include "prop/theory_proxy.h"

namespace cvc5::internal {
namespace prop {

class CadicalPropagator : public CaDiCaL::ExternalPropagator
{
 public:
  CadicalPropagator(prop::TheoryProxy* proxy,
                    context::Context* context,
                    CaDiCaL::Solver& solver);

  /**
   * Notification from the SAT solver on assignment of a new literal.
   *
   * Saves assignment for notified literal, enqueues corresponding theory
   * literal in theory proxy.
   *
   * @param lit      The CaDiCaL literal that was assigned.
   * @param is_fixed True if the assignment is fixed (on level 0).
   */
  void notify_assignment(int lit, bool is_fixed) override;

  /**
   * Notification from the SAT solver when it makes a decision.
   * Pushes new SAT context level.
   */
  void notify_new_decision_level() override;

  /**
   * Notification from the SAT solver on backtrack to the given level.
   *
   * This will automatically backtrack decisions and assignments to the
   * specified level. Fixed assignments that get backtracked will be
   * re-assigned at `level` and the corresponding theory literals are
   * re-enqueued in the theory proxy.
   *
   * @param level The level the SAT solver backtracked to.
   */
  void notify_backtrack(size_t level) override;

  /**
   * Callback of the SAT solver on finding a full sat assignment.
   *
   * Checks whether current model is consistent with the theories, performs a
   * full effort check and theory propgations.
   *
   * @param model The full assignment.
   * @return true If the current model is not in conflict with the theories.
   */
  bool cb_check_found_model(const std::vector<int>& model) override;

  /**
   * Callback of the SAT solver before making a new decision.
   *
   * Processes decision requests from the theory proxy.
   *
   * @note This may call cb_check_found_model() in case the decision engine
   *       determines that we have a partial model, i.e., stopSearch is true.
   *
   * @return The next decision.
   */
  int cb_decide() override;

  /**
   * Callback of the SAT solver after BCP.
   *
   * Performs standard theory check and theory propagations.
   *
   * If we don't have any theory propagations queued in d_propagations, we
   * perform an EFFORT_STANDARD check in combination with theory_propagate() to
   * populate d_propagations.
   *
   * @return The next theory propagation.
   */
  int cb_propagate() override;

  /**
   * Callback of the SAT solver asking for the explanation of a theory literal.
   * @note This is called on `propagated_lit` until the reason clause is
   *       fully processed.
   * @param propagated_lit The theory literal.
   * @return The next literal of the reason clause, 0 to terminate the clause.
   */
  int cb_add_reason_clause_lit(int propagated_lit) override;

  /**
   * Callback of the SAT solver to determine if we have a new clause to add.
   * @return True to indicate that we have clauses to add.
   */
  bool cb_has_external_clause() override;

  /**
   * Callback of the SAT solver to add a new clause.
   * @note This is called consecutively until the full clause is processed.
   * @note Clauses are terminated with 0 in d_new_clauses.
   * @return The next literal of the clause, 0 to terminate the clause.
   */
  int cb_add_external_clause_lit() override;

  /**
   * Get the current trail of decisions.
   * @return The trail of decisions.
   */
  const std::vector<SatLiteral>& get_decisions() const;

  /**
   * Get the current assignment of lit.
   *
   * Note: This does not query d_solver->val() since this can only be queried
   * if the SAT solver is in a SAT state, which is not the case during solving.
   *
   * @param lit SatLiteral to be queried.
   * @return Current value of given literal on the trail.
   */
  SatValue value(SatLiteral lit) const;

  /**
   * Adds a new clause to the propagator.
   *
   * The clause will not immediately added to the SAT solver, but instead
   * will be added through the `cb_add_external_clause_lit` callback.
   *
   * Note: Filters out clauses satisfied by fixed literals.
   *
   * @param clause The clause to add.
   */
  void add_clause(const SatClause& clause);

  /**
   * Add new CaDiCaL variable.
   * @param var            The variable to add.
   * @param level          The current user assertion level.
   * @param is_theory_atom True if variable is a theory atom.
   * @param in_search      True if SAT solver is currently in search().
   */
  void add_new_var(const SatVariable& var, bool is_theory_atom);

  /**
   * Checks whether the theory engine is done, no new clauses need to be added
   * and the current model is consistent.
   */
  bool done() const;

  /** Push user assertion level. */
  void user_push(SatVariable& alit);

  /** Pop user assertion level. */
  void user_pop();

  /** TODO: document */
  bool is_fixed(SatVariable var) const;

  /**
   * Configure and record preferred phase of variable.
   * @param lit The literal.
   */
  void phase(SatLiteral lit);

  /**
   * Return the activation literal for the current user level.
   *
   * Note: Returns undefSatLiteral at user level 0.
   */
  const SatLiteral& current_activation_lit();

  /** Return the current user (assertion) level. */
  size_t current_user_level();

  /** Return the current list of activation literals. */
  const std::vector<SatLiteral>& activation_literals();

  /**
   * Renotify fixed literals in the current user level.
   *
   * This is done prior to a new solve() call and ensures that fixed literals
   * are enqueued in the theory proxy. This is needed since the SAT solver does
   * not re-notify us about fixed literals.
   */
  void renotify_fixed();

  /** Set d_in_search flag to indicate whether solver is currently in search. */
  void in_search(bool flag);

 private:
  /** Retrieve theory propagations and add them to the propagations list. */
  void theory_propagate();

  /**
   * Get next propagation.
   *
   * @return Return next propagation queued in d_propagations.
   */
  int next_propagation();

  /** The associated theory proxy. */
  prop::TheoryProxy* d_proxy = nullptr;

  /** The SAT context. */
  context::Context& d_context;
  CaDiCaL::Solver& d_solver;

  /** Struct to store information on variables. */
  struct VarInfo
  {
    uint32_t level_intro = 0;     // user level at which variable was created
    uint32_t level_fixed = 0;     // user level at which variable was fixed
    bool is_theory_atom = false;  // is variable a theory atom
    bool is_fixed = false;        // has variable fixed assignment
    bool is_active = true;        // is variable active
    int32_t assignment = 0;       // current variable assignment
    int8_t phase = 0;             // preferred phase
  };
  /** Maps SatVariable to corresponding info struct. */
  std::vector<VarInfo> d_var_info;

  /**
   * Currently active variables, can get inactive on user pops.
   * Dependent on user context.
   */
  std::vector<SatVariable> d_active_vars;
  /**
   * Control stack to mananage d_active_vars on user pop.
   *
   * Note: We do not use a User-context-dependent CDList here, since we neeed
   *       to know which variables are popped and thus become inactive.
   */
  std::vector<size_t> d_active_vars_control;

  /**
   * Current activation literals.
   *
   * For each user level, we push a fresh activation literal to the vector (in
   * user_pop()). Activation literals get removed and disabled in user_pop().
   * The size of the vector corresponds to the current user level.
   *
   * The activation literals corrsponding to the current user level gets
   * automtically added to each clause added in this user level. With
   * activation literals we can simulate push/pop of clauses in the SAT solver.
   */
  std::vector<SatLiteral> d_activation_literals;

  /** List of fixed literals to be re-notified in lower user level. */
  std::vector<SatLiteral> d_renotify_fixed;

  /**
   * Variable assignment notifications.
   *
   * Used to unassign variables on backtrack.
   */
  std::vector<SatLiteral> d_assignments;

  /**
   * Control stack to manage d_assignments when backtracking on SAT level.
   *
   * Note: We do not use a SAT-context-depenent CDList for d_assignments, since
   *       we need to know which non-fixed variables are unassigned on
   *       backtrack.
   */
  std::vector<size_t> d_assignment_control;

  /**
   * Stores all observed decision variables.
   *
   * Note: May contain undefSatLiteral for unobserved decision variables.
   */
  std::vector<SatLiteral> d_decisions;

  /** Used by cb_propagate() to return propagated literals. */
  std::deque<SatLiteral> d_propagations;

  /**
   * Used by add_clause() to buffer added clauses, which will be added via
   * cb_add_reason_clause_lit().
   */
  std::deque<CadicalLit> d_new_clauses;

  /**
   * Flag indicating whether cb_add_reason_clause_lit() is currently
   * processing a reason.
   */
  bool d_processing_reason = false;

  /** Reason storage to process current reason in cb_add_reason_clause_lit(). */
  std::deque<SatLiteral> d_reason;

  bool d_found_solution = false;

  /** Flag indicating if SAT solver is in search(). */
  bool d_in_search = false;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif  // CVC5__PROP__CADICAL__CADICAL_PROPAGATOR_H
