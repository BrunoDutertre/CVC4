/*********************                                                        */
/*! \file node_algorithm.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common algorithms on nodes
 **
 ** This file implements common algorithms applied to nodes, such as checking if
 ** a node contains a free or a bound variable.
 **/

#include "expr/node_algorithm.h"

#include "expr/attribute.h"

namespace CVC4 {
namespace expr {

bool hasSubterm(TNode n, TNode t, bool strict)
{
  if (!strict && n == t)
  {
    return true;
  }

  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> toProcess;

  toProcess.push_back(n);

  for (unsigned i = 0; i < toProcess.size(); ++i)
  {
    TNode current = toProcess[i];
    if (current.hasOperator() && current.getOperator() == t)
    {
      return true;
    }
    for (unsigned j = 0, j_end = current.getNumChildren(); j < j_end; ++j)
    {
      TNode child = current[j];
      if (child == t)
      {
        return true;
      }
      if (visited.find(child) != visited.end())
      {
        continue;
      }
      else
      {
        visited.insert(child);
        toProcess.push_back(child);
      }
    }
  }

  return false;
}

bool hasSubtermMulti(TNode n, TNode t)
{
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::unordered_map<TNode, bool, TNodeHashFunction> contains;
  std::unordered_map<TNode, bool, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      if (cur == t)
      {
        visited[cur] = true;
        contains[cur] = true;
      }
      else
      {
        visited[cur] = false;
        visit.push_back(cur);
        for (const Node& cc : cur)
        {
          visit.push_back(cc);
        }
      }
    }
    else if (!it->second)
    {
      bool doesContain = false;
      for (const Node& cn : cur)
      {
        it = contains.find(cn);
        Assert(it != visited.end());
        if (it->second)
        {
          if (doesContain)
          {
            // two children have t, return true
            return true;
          }
          doesContain = true;
        }
      }
      contains[cur] = doesContain;
      visited[cur] = true;
    }
  } while (!visit.empty());
  return false;
}

struct HasBoundVarTag
{
};
struct HasBoundVarComputedTag
{
};
/** Attribute true for expressions with bound variables in them */
typedef expr::Attribute<HasBoundVarTag, bool> HasBoundVarAttr;
typedef expr::Attribute<HasBoundVarComputedTag, bool> HasBoundVarComputedAttr;

bool hasBoundVar(TNode n)
{
  if (!n.getAttribute(HasBoundVarComputedAttr()))
  {
    bool hasBv = false;
    if (n.getKind() == kind::BOUND_VARIABLE)
    {
      hasBv = true;
    }
    else
    {
      for (auto i = n.begin(); i != n.end() && !hasBv; ++i)
      {
        hasBv = hasBoundVar(*i);
      }
    }
    if (!hasBv && n.hasOperator())
    {
      hasBv = hasBoundVar(n.getOperator());
    }
    n.setAttribute(HasBoundVarAttr(), hasBv);
    n.setAttribute(HasBoundVarComputedAttr(), true);
    Debug("bva") << n << " has bva : " << n.getAttribute(HasBoundVarAttr())
                 << std::endl;
    return hasBv;
  }
  return n.getAttribute(HasBoundVarAttr());
}

bool hasFreeVar(TNode n)
{
  std::unordered_set<Node, NodeHashFunction> fvs;
  return getFreeVariables(n, fvs, false);
}

bool getFreeVariables(TNode n,
                      std::unordered_set<Node, NodeHashFunction>& fvs,
                      bool computeFv)
{
  std::unordered_set<TNode, TNodeHashFunction> bound_var;
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    // can skip if it doesn't have a bound variable
    if (!hasBoundVar(cur))
    {
      continue;
    }
    Kind k = cur.getKind();
    bool isQuant = cur.isClosure();
    std::unordered_map<TNode, bool, TNodeHashFunction>::iterator itv =
        visited.find(cur);
    if (itv == visited.end())
    {
      if (k == kind::BOUND_VARIABLE)
      {
        if (bound_var.find(cur) == bound_var.end())
        {
          if (computeFv)
          {
            fvs.insert(cur);
          }
          else
          {
            return true;
          }
        }
      }
      else if (isQuant)
      {
        for (const TNode& cn : cur[0])
        {
          // should not shadow
          Assert(bound_var.find(cn) == bound_var.end());
          bound_var.insert(cn);
        }
        visit.push_back(cur);
      }
      // must visit quantifiers again to clean up below
      visited[cur] = !isQuant;
      if (cur.hasOperator())
      {
        visit.push_back(cur.getOperator());
      }
      for (const TNode& cn : cur)
      {
        visit.push_back(cn);
      }
    }
    else if (!itv->second)
    {
      Assert(isQuant);
      for (const TNode& cn : cur[0])
      {
        bound_var.erase(cn);
      }
      visited[cur] = true;
    }
  } while (!visit.empty());

  return !fvs.empty();
}

bool getVariables(TNode n, std::unordered_set<TNode, TNodeHashFunction>& vs)
{
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    std::unordered_set<TNode, TNodeHashFunction>::iterator itv =
        visited.find(cur);
    if (itv == visited.end())
    {
      if (cur.isVar())
      {
        vs.insert(cur);
      }
      else
      {
        for (const TNode& cn : cur)
        {
          visit.push_back(cn);
        }
      }
      visited.insert(cur);
    }
  } while (!visit.empty());

  return !vs.empty();
}

void getSymbols(TNode n, std::unordered_set<Node, NodeHashFunction>& syms)
{
  std::unordered_set<TNode, TNodeHashFunction> visited;
  getSymbols(n, syms, visited);
}

void getSymbols(TNode n,
                std::unordered_set<Node, NodeHashFunction>& syms,
                std::unordered_set<TNode, TNodeHashFunction>& visited)
{
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur.isVar() && cur.getKind() != kind::BOUND_VARIABLE)
      {
        syms.insert(cur);
      }
      if (cur.hasOperator())
      {
        visit.push_back(cur.getOperator());
      }
      for (TNode cn : cur)
      {
        visit.push_back(cn);
      }
    }
  } while (!visit.empty());
}

Node substituteCaptureAvoiding(TNode n, Node src, Node dest)
{
  if (n == src)
  {
    return dest;
  }
  if (src == dest)
  {
    return n;
  }
  std::vector<Node> srcs;
  std::vector<Node> dests;
  srcs.push_back(src);
  dests.push_back(dest);
  return substituteCaptureAvoiding(n, srcs, dests);
}

Node substituteCaptureAvoiding(TNode n,
                               std::vector<Node>& src,
                               std::vector<Node>& dest)
{
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode curr;
  visit.push_back(n);
  Assert(src.size() == dest.size(),
         "Substitution domain and range must be equal size");
  do
  {
    curr = visit.back();
    visit.pop_back();
    it = visited.find(curr);

    if (it == visited.end())
    {
      auto itt = std::find(src.rbegin(), src.rend(), curr);
      if (itt != src.rend())
      {
        Assert(
            (std::distance(src.begin(), itt.base()) - 1) >= 0
            && static_cast<unsigned>(std::distance(src.begin(), itt.base()) - 1)
                   < dest.size());
        Node n = dest[std::distance(src.begin(), itt.base()) - 1];
        visited[curr] = n;
        continue;
      }
      if (curr.getNumChildren() == 0)
      {
        visited[curr] = curr;
        continue;
      }

      visited[curr] = Node::null();
      // if binder, rename variables to avoid capture
      if (curr.isClosure())
      {
        NodeManager* nm = NodeManager::currentNM();
        // have new vars -> renames subs in the end of current sub
        for (const Node& v : curr[0])
        {
          src.push_back(v);
          dest.push_back(nm->mkBoundVar(v.getType()));
        }
      }
      // save for post-visit
      visit.push_back(curr);
      // visit children
      if (curr.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        // push the operator
        visit.push_back(curr.getOperator());
      }
      for (unsigned i = 0, size = curr.getNumChildren(); i < size; ++i)
      {
        visit.push_back(curr[i]);
      }
    }
    else if (it->second.isNull())
    {
      // build node
      NodeBuilder<> nb(curr.getKind());
      if (curr.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        // push the operator
        Assert(visited.find(curr.getOperator()) != visited.end());
        nb << visited[curr.getOperator()];
      }
      // collect substituted children
      for (unsigned i = 0, size = curr.getNumChildren(); i < size; ++i)
      {
        Assert(visited.find(curr[i]) != visited.end());
        nb << visited[curr[i]];
      }
      Node n = nb;
      visited[curr] = n;

      // remove renaming
      if (curr.isClosure())
      {
        // remove beginning of sub which correspond to renaming of variables in
        // this binder
        unsigned nchildren = curr[0].getNumChildren();
        src.resize(src.size() - nchildren);
        dest.resize(dest.size() - nchildren);
      }
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  return visited[n];
}

}  // namespace expr
}  // namespace CVC4
