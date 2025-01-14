/*********************                                                        */
/*! \file node_algorithm.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common algorithms on nodes
 **
 ** This file implements common algorithms applied to nodes, such as checking if
 ** a node contains a free or a bound variable. This file should generally only
 ** be included in source files.
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__NODE_ALGORITHM_H
#define CVC4__EXPR__NODE_ALGORITHM_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace expr {

/**
 * Check if the node n has a subterm t.
 * @param n The node to search in
 * @param t The subterm to search for
 * @param strict If true, a term is not considered to be a subterm of itself
 * @return true iff t is a subterm in n
 */
bool hasSubterm(TNode n, TNode t, bool strict = false);

/**
 * Check if the node n has >1 occurrences of a subterm t.
 */
bool hasSubtermMulti(TNode n, TNode t);

/**
 * Returns true iff the node n contains a bound variable, that is a node of
 * kind BOUND_VARIABLE. This bound variable may or may not be free.
 * @param n The node under investigation
 * @return true iff this node contains a bound variable
 */
bool hasBoundVar(TNode n);

/**
 * Returns true iff the node n contains a free variable, that is, a node
 * of kind BOUND_VARIABLE that is not bound in n.
 * @param n The node under investigation
 * @return true iff this node contains a free variable.
 */
bool hasFreeVar(TNode n);

/**
 * Get the free variables in n, that is, the subterms of n of kind
 * BOUND_VARIABLE that are not bound in n, adds these to fvs.
 * @param n The node under investigation
 * @param fvs The set which free variables are added to
 * @param computeFv If this flag is false, then we only return true/false and
 * do not add to fvs.
 * @return true iff this node contains a free variable.
 */
bool getFreeVariables(TNode n,
                      std::unordered_set<Node, NodeHashFunction>& fvs,
                      bool computeFv = true);

/**
 * Get all variables in n.
 * @param n The node under investigation
 * @param vs The set which free variables are added to
 * @return true iff this node contains a free variable.
 */
bool getVariables(TNode n, std::unordered_set<TNode, TNodeHashFunction>& vs);

/**
 * For term n, this function collects the symbols that occur as a subterms
 * of n. A symbol is a variable that does not have kind BOUND_VARIABLE.
 * @param n The node under investigation
 * @param syms The set which the symbols of n are added to
 */
void getSymbols(TNode n, std::unordered_set<Node, NodeHashFunction>& syms);
/** Same as above, with a visited cache */
void getSymbols(TNode n,
                std::unordered_set<Node, NodeHashFunction>& syms,
                std::unordered_set<TNode, TNodeHashFunction>& visited);
/**
 * Substitution of Nodes in a capture avoiding way.
 */
Node substituteCaptureAvoiding(TNode n, Node src, Node dest);

/**
 * Simultaneous substitution of Nodes in a capture avoiding way.  Elements in
 * source will be replaced by their corresponding element in dest.  Both
 * vectors should have the same size.
 */
Node substituteCaptureAvoiding(TNode n,
                               std::vector<Node>& src,
                               std::vector<Node>& dest);

}  // namespace expr
}  // namespace CVC4

#endif
