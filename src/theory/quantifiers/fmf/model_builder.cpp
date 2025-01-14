/*********************                                                        */
/*! \file model_builder.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of model builder class
 **/

#include "theory/quantifiers/fmf/model_builder.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/fmf/model_engine.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/theory_uf_model.h"
#include "theory/uf/theory_uf_strong_solver.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

QModelBuilder::QModelBuilder(context::Context* c, QuantifiersEngine* qe)
    : TheoryEngineModelBuilder(qe->getTheoryEngine()),
      d_qe(qe),
      d_addedLemmas(0),
      d_triedLemmas(0) {}

bool QModelBuilder::optUseModel() {
  return options::mbqiMode()!=MBQI_NONE || options::fmfBound();
}

bool QModelBuilder::preProcessBuildModel(TheoryModel* m) {
  return preProcessBuildModelStd( m );
}

bool QModelBuilder::preProcessBuildModelStd(TheoryModel* m) {
  d_addedLemmas = 0;
  d_triedLemmas = 0;
  if( options::fmfEmptySorts() || options::fmfFunWellDefinedRelevant() ){
    FirstOrderModel * fm = (FirstOrderModel*)m;
    //traverse equality engine
    std::map< TypeNode, bool > eqc_usort;
    eq::EqClassesIterator eqcs_i =
        eq::EqClassesIterator(fm->getEqualityEngine());
    while( !eqcs_i.isFinished() ){
      TypeNode tr = (*eqcs_i).getType();
      eqc_usort[tr] = true;
      ++eqcs_i;
    }
    //look at quantified formulas
    for( unsigned i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
      Node q = fm->getAssertedQuantifier( i, true );
      if( fm->isQuantifierActive( q ) ){
        //check if any of these quantified formulas can be set inactive
        if( options::fmfEmptySorts() ){
          for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
            TypeNode tn = q[0][i].getType();
            //we are allowed to assume the type is empty
            if( tn.isSort() && eqc_usort.find( tn )==eqc_usort.end() ){
              Trace("model-engine-debug") << "Empty domain quantified formula : " << q << std::endl;
              fm->setQuantifierActive( q, false );
            }
          }
        }else if( options::fmfFunWellDefinedRelevant() ){
          if( q[0].getNumChildren()==1 ){
            TypeNode tn = q[0][0].getType();
            if( tn.getAttribute(AbsTypeFunDefAttribute()) ){
              //Trace("model-engine-debug2") << "...possible irrelevant function def : " << q << ", #rr = " << d_quantEngine->getModel()->d_rep_set.getNumRelevantGroundReps( tn ) << std::endl;
              //we are allowed to assume the introduced type is empty
              if( eqc_usort.find( tn )==eqc_usort.end() ){
                Trace("model-engine-debug") << "Irrelevant function definition : " << q << std::endl;
                fm->setQuantifierActive( q, false );
              }
            }
          }
        }
      }
    }
  }
  return true;
}

void QModelBuilder::debugModel( TheoryModel* m ){
  //debug the model: cycle through all instantiations for all quantifiers, report ones that are not true
  if( Trace.isOn("quant-check-model") ){
    FirstOrderModel* fm = (FirstOrderModel*)m;
    Trace("quant-check-model") << "Testing quantifier instantiations..." << std::endl;
    int tests = 0;
    int bad = 0;
    for( unsigned i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
      Node f = fm->getAssertedQuantifier( i );
      std::vector< Node > vars;
      for( unsigned j=0; j<f[0].getNumChildren(); j++ ){
        vars.push_back( f[0][j] );
      }
      QRepBoundExt qrbe(d_qe);
      RepSetIterator riter(d_qe->getModel()->getRepSet(), &qrbe);
      if( riter.setQuantifier( f ) ){
        while( !riter.isFinished() ){
          tests++;
          std::vector< Node > terms;
          for (unsigned k = 0; k < riter.getNumTerms(); k++)
          {
            terms.push_back( riter.getCurrentTerm( k ) );
          }
          Node n = d_qe->getInstantiate()->getInstantiation(f, vars, terms);
          Node val = fm->getValue( n );
          if (val != d_qe->getTermUtil()->d_true)
          {
            Trace("quant-check-model") << "*******  Instantiation " << n << " for " << std::endl;
            Trace("quant-check-model") << "         " << f << std::endl;
            Trace("quant-check-model") << "         Evaluates to " << val << std::endl;
            bad++;
          }
          riter.increment();
        }
        Trace("quant-check-model") << "Tested " << tests << " instantiations";
        if( bad>0 ){
          Trace("quant-check-model") << ", " << bad << " failed" << std::endl;
        }
        Trace("quant-check-model") << "." << std::endl;
      }else{
        if( riter.isIncomplete() ){
          Trace("quant-check-model") << "Warning: Could not test quantifier " << f << std::endl;
        }
      }
    }
  }
}
