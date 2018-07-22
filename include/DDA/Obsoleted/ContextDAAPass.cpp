/*
 * Context sensitive version of Demand-Driven Alias Analysis Pass
 *
 *  Created on: May 28, 2013
 *      Author: yusui
 */

#include "DDA/DAAPass.h"
#include "Util/AnalysisUtil.h"

#include <llvm/Support/raw_ostream.h>	// for output
using namespace llvm;

char ContextDAAPass::ID = 0;

static RegisterPass<ContextDAAPass> FDAA("pcdaa",
		"Context sensitive Demand-Driven Alias Analysis Pass");

bool ContextDAAPass::dyckCFLParentheseMatch(const DPTItem& origItem,
		NodeVector &stack, DPTItem::State propState,
		PAGEdge *gepOrCallRetEdge) {

	assert(gepOrCallRetEdge && "expect gep or callret edge!!");
	if (!(isa<CallPE>(gepOrCallRetEdge) ||isa<RetPE>(gepOrCallRetEdge)) )
		return true;


	CallSiteID csId = (isa<CallPE>(gepOrCallRetEdge)) ?
			cast<CallPE>(gepOrCallRetEdge)->getCallSiteID() : cast<RetPE>(gepOrCallRetEdge)->getCallSiteID();

	// at S1 we push inverse exit(ret) or pop inverse entry(call)
	if (inverseFieldStateTransition(origItem, propState, csId)) {
		if (isa<RetPE>(gepOrCallRetEdge)) {
			stack.push_back(csId);
			DBOUT(DDDA,
					outs() << "\tPush inverse ret, stack size=" << stack.size()
							<< "\n");
		} else if (isa<CallPE>(gepOrCallRetEdge)) {
			if (!stack.empty() && csId == stack.back()) {
				stack.pop_back();
				DBOUT(DDDA,
						outs() << "\tPop inverse call, stack size="
								<< stack.size() << "\n");
			} else
				return false;
		} else
			assert(false && "should only be call or ret edge");
	}
	// at S3 we push forward entry(call) or pop forward exit(ret)
	else if (directFieldStateTransition(origItem, propState, csId)) {
		if (isa<CallPE>(gepOrCallRetEdge)) {
			stack.push_back(csId);
			DBOUT(DDDA,
					outs() << "\tPush forward call, stack size=" << stack.size()
							<< "\n");
		} else if (isa<RetPE>(gepOrCallRetEdge)) {
			if (!stack.empty() && csId == stack.back()) {
				stack.pop_back();
				DBOUT(DDDA,
						outs() << "\tPop forward ret, stack size="
								<< stack.size() << "\n");
			} else
				return false;
		} else
			assert(false && "should only be call or ret edge");
	}

	return true;
}

void ContextDAAPass::stateProp(const DPTItem& origItem, NodeID propNode,
		DPTItem::State propState, PAGEdge *gepOrCallRetEdge) {

//	DAAPass::stateProp( origItem,  propNode,  propState, gepOrCallRetEdge);

	DPTItem item(propNode, origItem.root, propState, origItem.field,
			origItem.context);

	bool dyckCFLMatch = true;
	// if this is a gep or call ret edge, then we perform dyck CFL match first
	if (gepOrCallRetEdge)
		dyckCFLMatch = dyckCFLParentheseMatch(origItem, item.context, propState,
				gepOrCallRetEdge);

	// if we haven't see this item state in this propNode before
	if (nodesVisited[propNode].find(item) == nodesVisited[propNode].end()) {
		nodesVisited[propNode].insert(item);

		/// if the dyck CFL parenthese match fails, then there is no need for further propagation.
		if (dyckCFLMatch == false)
			return;

		worklist.push_front(item);

		DBOUT(DDDA,
				outs() << "\t\t#Propagate to node " << propNode << "(root "
						<< origItem.root << ")" << "state " << propState
						<< "\n");

		/// we record alias when all field edges have been matched
		if (propState != DPTItem::S2)
			addToAliasSet(item.root, propNode);
	} else {
		DBOUT(DDDA,
				outs() << "\t\t#Already visited " << propNode << "(root "
						<< origItem.root << ")" << "state " << propState
						<< "\n");
	}

}

