/*
 * FlowDAAPass.cpp
 *
 *  Created on: Jun 4, 2013
 *      Author: yusui
 */

#include "DDA/DAAPass.h"
#include "Util/AnalysisUtil.h"

#include <llvm/Support/raw_ostream.h>	// for output
using namespace llvm;
using namespace analysisUtil;

char FlowDAAPass::ID = 0;

static RegisterPass<FlowDAAPass> LDAA("pldaa",
		"Flow sensitive FICI Demand-Driven Alias Analysis Pass");

bool FlowDAAPass::runOnModule(SVFModule module){

	for (Module::iterator fi = module.begin(), fe = module.end();
	        fi != fe; ++fi) {
		Function* fn = &(*fi);
		 if (isExtCall(fn)) continue;
	    IteratedDominanceFrontier *curIDF  =  &getAnalysis<IteratedDominanceFrontier>(*fn);
	    //DominanceFrontier *curIDF  = &getAnalysis<llvm::DominanceFrontier>(*fn);
	    for (Function::iterator bi = fn->begin(), be = fn->end();
	            bi != be; ++bi) {
	    	BasicBlock* bb = &(*bi);
	    	DBOUT(DDDA,outs() << "BB node " << bb->getName() << " IDF BB node set:{\n");
	        IteratedDominanceFrontier::iterator idf = curIDF->getIDFSet(bb);
	        if (idf != curIDF->end()) {
	            const std::set<BasicBlock *> &idfset = idf->second;
	            for (std::set<BasicBlock *>::iterator bi = idfset.begin(), be = idfset.end(); bi != be; bi ++) {
	                BasicBlock *tbb = *bi;
					DBOUT(DDDA, outs() << "\t[ " << tbb->getName() << "]\t");

	            }
	        }
	        DBOUT(DDDA,outs() << "}\n");
	    }
	}

	return false;
}
