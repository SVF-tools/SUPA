/*
 *  // Field sensitive version of FICI Demand-Driven Alias Analysis Pass
 *
 *  Created on: May 23, 2013
 *      Author: yusui
 */

#include "DDA/DAAPass.h"
#include "Util/AnalysisUtil.h"

#include <llvm/Support/raw_ostream.h>	// for output
using namespace llvm;

char FieldDAAPass::ID = 0;

static RegisterPass<FieldDAAPass> FDAA("pfdaa",
		"Field sensitive FICI Demand-Driven Alias Analysis Pass");

void FieldDAAPass::resetStatePerQuery() {

	DAAPass::resetStatePerQuery();

	//TODO:: do we need to reset some others here or just cache it??
	for (NodeToDPTItemMap::iterator iter = savedS1States.begin();
			iter != savedS1States.end(); ++iter) {
		iter->second.clear();
	}
	for (NodeToDPTItemMap::iterator iter = savedS3States.begin();
			iter != savedS3States.end(); ++iter) {
		iter->second.clear();
	}

	savedS1States.clear();
	savedS3States.clear();
}

bool FieldDAAPass::inverseFieldStateTransition(const DPTItem& origItem,
		DPTItem::State propState, Size_t offsetOrCSId) {
	return origItem.state == DPTItem::S1 && propState == DPTItem::S1
			&& offsetOrCSId != 0;
}

bool FieldDAAPass::directFieldStateTransition(const DPTItem& origItem,
		DPTItem::State propState, Size_t offsetOrCSId) {
	return origItem.state == DPTItem::S3 && propState == DPTItem::S3
			&& offsetOrCSId != 0;
}

void FieldDAAPass::propAliasUpToInverseFlow(DPTItem& item) {

	PAGNode* root = pag->getPAGNode(item.root);
	PAGNode* cur = pag->getPAGNode(item.cur);

	/// for field sensitivity  root and cur node may not be aliased with each other,
	/// then there is no need to propagate upwards
	/// like p gep q, p is not aliased with q although p can reach q during propagation
	if (!isAlias(item.root, item.cur))
		return;

	for (PAGNode::iterator lit = root->getOutgoingEdges(PAGEdge::Load).begin();
			lit != root->getOutgoingEdges(PAGEdge::Load).end(); ++lit) {
		for (PAGNode::iterator sit =
				cur->getIncomingEdges(PAGEdge::Store).begin();
				sit != cur->getIncomingEdges(PAGEdge::Store).end(); ++sit) {
			// add matched pair loadDst (*lit)->getDstID() to storeSrc (*sit)->getSrcID()
			addToNodeMatchMap((*lit)->getDstID(), (*sit)->getSrcID());
		}
	}

	// given savedS1States (loadDst) before propagating downwards
	// match all the stores (storeSrc) connected by item.cur for upward propagation
	for (DPTItemSet::iterator iter = savedS1States[item.root].begin();
			iter != savedS1States[item.root].end(); ++iter) {
		for (PAGNode::iterator sit =
				cur->getIncomingEdges(PAGEdge::Store).begin();
				sit != cur->getIncomingEdges(PAGEdge::Store).end(); ++sit) {
			DBOUT(DDDA,
					outs() << "\tPropagate upward(to S1)  from node "
							<< (*iter).cur << "(root " << (*iter).root
							<< ") to node " << (*sit)->getSrcID() << "\n");
			DPTItem newItem((*iter).cur, (*iter).root, (*iter).state,
					item.field, item.context);
			stateProp(newItem, (*sit)->getSrcID(), DPTItem::S1);
			//TODO: here we should delete the savedS1States as it has been propagated upward
		}
	}

}

void FieldDAAPass::propAliasUpToDirectFlow(DPTItem& item) {

	PAGNode* root = pag->getPAGNode(item.root);
	PAGNode* cur = pag->getPAGNode(item.cur);

	if (!isAlias(item.root, item.cur))
		return;

	for (PAGNode::iterator sit = root->getIncomingEdges(PAGEdge::Store).begin();
			sit != root->getIncomingEdges(PAGEdge::Store).end(); ++sit) {
		for (PAGNode::iterator lit =
				cur->getOutgoingEdges(PAGEdge::Load).begin();
				lit != cur->getOutgoingEdges(PAGEdge::Load).end(); ++lit) {
			// add matched pair loadDst (*lit)->getDstID() to storeSrc (*iter).cur
			addToNodeMatchMap((*lit)->getDstID(), (*sit)->getSrcID());
		}
	}

	// given savedS3States (storeSrc) before propagating downwards
	// match all the loads (loadDst) connected by item.cur for upward propagation
	for (DPTItemSet::iterator iter = savedS3States[item.root].begin();
			iter != savedS3States[item.root].end(); ++iter) {
		for (PAGNode::iterator lit =
				cur->getOutgoingEdges(PAGEdge::Load).begin();
				lit != cur->getOutgoingEdges(PAGEdge::Load).end(); ++lit) {
			DBOUT(DDDA,
					outs() << "\tPropagate upward(to S3)  from node "
							<< (*iter).cur << "(root " << (*iter).root
							<< ") to node " << (*lit)->getDstID() << "\n");
			DPTItem newItem((*iter).cur, (*iter).root, (*iter).state,
					item.field, item.context);
			stateProp(newItem, (*lit)->getDstID(), DPTItem::S3);
			//TODO: here we should delete the savedS1States as it has been propagated upward
		}
	}

}

void FieldDAAPass::propAliasDownwards(DPTItem& item) {
	PAGNode* pNode = pag->getPAGNode(item.cur);
	if (item.state == DPTItem::S1) {
		for (PAGNode::iterator iter =
				pNode->getIncomingEdges(PAGEdge::Load).begin();
				iter != pNode->getIncomingEdges(PAGEdge::Load).end(); ++iter) {
			DBOUT(DDDA, outs() << "\tinverse through Load, propagate down\n");
			// save the state before propagate down
			// map LoadSrc --> item
			savedS1States[(*iter)->getSrcID()].insert(item);
			// create a new item when propagating down, start new round of alias analysis
			DPTItem newItem((*iter)->getSrcID(), (*iter)->getSrcID(),
					DPTItem::S1, item.field, item.context);
			stateProp(newItem, (*iter)->getSrcID(), DPTItem::S1);
		}
	}

	else if (item.state == DPTItem::S3) {
		for (PAGNode::iterator iter =
				pNode->getOutgoingEdges(PAGEdge::Store).begin();
				iter != pNode->getOutgoingEdges(PAGEdge::Store).end(); ++iter) {
			DBOUT(DDDA, outs() << "\tforward through Store, propagate down\n");
			// save the state before propagate down
			// map StoreDst --> item
			savedS3States[(*iter)->getDstID()].insert(item);
			// create a new item when propagating down, start new round of alias analysis
			DPTItem newItem((*iter)->getDstID(), (*iter)->getDstID(),
					DPTItem::S1, item.field, item.context);
			stateProp(newItem, (*iter)->getDstID(), DPTItem::S1);
		}
	}
}

bool FieldDAAPass::dyckCFLParentheseMatch(const DPTItem& origItem,
		NodeVector &stack, DPTItem::State propState,
		PAGEdge *gepOrCallRetEdge) {

	assert(gepOrCallRetEdge && "expect gep or callret edge!!");

	// only handle field sensitivity here
	if (!isa<GepPE>(gepOrCallRetEdge))
		return true;

	Size_t offset = 0;
	if (NormalGepPE* edge = dyn_cast<NormalGepPE>(gepOrCallRetEdge))
		offset = edge->getOffset();
	else
		assert(false && "expecting a gep edge with offset");
	/// at S1 we only push the field into stack
	if (inverseFieldStateTransition(origItem, propState, offset)) {
		stack.push_back(offset);
		DBOUT(DDDA,
				outs() << "\tPush field, stack size=" << stack.size() << "\n");
	}
	/// at S3 check whether we can match the field or not
	else if (directFieldStateTransition(origItem, propState, offset)) {
		/// if field match then we pop the matched field and then propagate to the next node
		if ((!stack.empty() && offset == stack.back())) {
			stack.pop_back();
			DBOUT(DDDA,
					outs() << "\tPop field, stack size=" << stack.size()
							<< "\n");
		}
		/// if it does not match then we stop propagating forward and return
		else {
			DBOUT(DDDA,
					outs() << "\tField not match, stack size=" << stack.size()
							<< "\n");
			return false;
		}
	}

	return true;
}

void FieldDAAPass::stateProp(const DPTItem& origItem, NodeID propNode,
		DPTItem::State propState, PAGEdge *gepOrCallRetEdge) {

	// DAAPass::stateProp( origItem,  propNode,  propState, gepOrCallRetEdge);

	DPTItem item(propNode, origItem.root, propState, origItem.field,
			origItem.context);

	bool dyckCFLMatch = true;
	// if this is a gep or call ret edge, then we perform dyck CFL match first
	if (gepOrCallRetEdge)
		dyckCFLMatch = dyckCFLParentheseMatch(origItem, item.field, propState,
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
		if (propState != DPTItem::S2 && item.field.empty())
			addToAliasSet(item.root, propNode);
	} else {
		DBOUT(DDDA,
				outs() << "\t\t#Already visited " << propNode << "(root "
						<< origItem.root << ")" << "state " << propState
						<< "\n");
	}
}
