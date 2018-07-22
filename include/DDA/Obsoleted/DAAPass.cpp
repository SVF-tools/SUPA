/*
 // Flow Insensitive and Context Insensitive  Demand-Driven Alias Analysis Pass
 // reference: Demand-Driven Alias Anlaysis For C (POPL '08)

 // Author: Yulei Sui,
 */

#include "DDA/DAAPass.h"
#include "Util/AnalysisUtil.h"

#include <llvm/Support/raw_ostream.h>	// for output
#include <llvm/Support/CommandLine.h> // for tool output file
using namespace llvm;
using namespace std;
using namespace analysisUtil;

#define QUERYBUDGET 30000

char DAAPass::ID = 0;

static RegisterPass<DAAPass> DAA("pdaa",
		"FICI Demand-Driven Alias Analysis Pass");

/// register this into alias analysis group
static RegisterAnalysisGroup<AliasAnalysis> AA_GROUP(DAA);

static cl::opt<bool> ALIASPrint("print-alias", cl::init(false),
		cl::desc("Print alias set"));

static cl::opt<bool> ENABLECACHE("enable-cache", cl::init(true),
		cl::desc("enable caching for demand-driven analysis"));

////@{==============================================
/*
 * Demand-Driven Alias Anlaysis For C (POPL '08)
 */

void DAAPass::resetStatePerQuery() {
	for (NodeToDPTItemMap::iterator iter = nodesVisited.begin();
			iter != nodesVisited.end(); ++iter) {
		iter->second.clear();
	}
	for (AliasSetMap::iterator iter = nodeToAliasMap.begin();
			iter != nodeToAliasMap.end(); ++iter) {
		iter->second.clear();
	}
	nodesVisited.clear();
	nodeToAliasMap.clear();
}

/*!
 *
 */
void DAAPass::analyze(SVFModule module){

	initialize(module);

	Size_t query_num = 0;
	Size_t total_query = getTotalNumberOfQuery();
	DBOUT(DGENERAL,
			outs() << pasMsg("total query number: ") << total_query << "\n");
	DBOUT(DDDA, outs() << "total query number: " << total_query << "\n");

	for (NodeBS::iterator nIter = getAllValidPtrs().begin();
			nIter != getAllValidPtrs().end(); ++nIter) {
		NodeID nodeId = *nIter;
		DBOUT(DGENERAL,
				outs() << pasMsg("Answering query for node") << nodeId << "\t ("
						<< ++query_num << "/" << total_query << ")" << " \n");
		DBOUT(DDDA,
				outs() << "Answering query for node" << nodeId << "\t ("
						<< ++query_num << "/" << total_query << ")" << " \n");

		// do not compute points-to for isolated node
		if (pag->isValidPointer(nodeId) == false)
			continue;
		computeAlias(nodeId);
		// filter the pointer target that is not a valid pointer
		if (ALIASPrint)
			dumpAliasSet(nodeId, getAliasSet(nodeId));

		resetStatePerQuery();
	}

	finalize();
}

/*!
 *
 */
bool DAAPass::runOnModule(SVFModule module) {

	/// DDA analysis
	analyze(module);

	return false;
}

void DAAPass::computeAlias(NodeID node) {

	DPTItem item(node, node, DPTItem::S1);
	worklist.push_front(item);

	while (!worklist.empty()) {
		DPTItem item = worklist.front();

		DBOUT(DDDA,
				outs() << "   AT node " << item.cur << "(root " << item.root
						<< ") " << "state " << item.state << "\n");
		worklist.pop_front();

		// find the opportunities that whether we can propagate the alias information upwards
		propAliasUpwards(item);

		// handling the normal transition
		if (item.state == DPTItem::S1) {
			handleS1(item);
		}

		else if (item.state == DPTItem::S2) {
			handleS2(item);
		}

		else if (item.state == DPTItem::S3) {
			handleS3(item);
		} else
			assert(false && "no such state transition!!");

		///TODO: optimizations if we already get alias match, then we do not need to propagate downward
		propAliasDownwards(item);

	}

	// enable cache for this node
	//enableCache(node);

}

void DAAPass::propAliasDownwards(DPTItem& item) {
	PAGNode* pNode = pag->getPAGNode(item.cur);
	if (item.state == DPTItem::S1) {
		for (PAGNode::iterator iter =
				pNode->getIncomingEdges(PAGEdge::Load).begin();
				iter != pNode->getIncomingEdges(PAGEdge::Load).end(); ++iter) {
			DBOUT(DDDA, outs() << "\tinverse through Load, propagate down\n");
			// save the state before propagate down
			stateProp((*iter)->getSrcID(), (*iter)->getSrcID(), DPTItem::S1);
		}
	}

	else if (item.state == DPTItem::S3) {
		for (PAGNode::iterator iter =
				pNode->getOutgoingEdges(PAGEdge::Store).begin();
				iter != pNode->getOutgoingEdges(PAGEdge::Store).end(); ++iter) {
			DBOUT(DDDA, outs() << "\tforward through Store, propagate down\n");
			// save the state before propagate down
			stateProp((*iter)->getDstID(), (*iter)->getDstID(), DPTItem::S1);
		}
	}
}

void DAAPass::propAliasUpwards(DPTItem& item) {

	// if we are standing at S3, we need to consider two cases:
	// 1) propagate the alias to inverse flow
	// 			match propagate upward, match load store
	// 			 root --> q (load), p --> cur (store),  value flow from p --> q
	propAliasUpToInverseFlow(item);

	// 2) propagate the alias to direct flow
	// 			match propagate upward, match load store
	//  		p --> root (store), cur --> q (load),  value flow from p --> q
	propAliasUpToDirectFlow(item);

}

void DAAPass::propAliasUpToInverseFlow(DPTItem& item) {

	PAGNode* root = pag->getPAGNode(item.root);
	PAGNode* cur = pag->getPAGNode(item.cur);

	for (PAGNode::iterator lit = root->getOutgoingEdges(PAGEdge::Load).begin();
			lit != root->getOutgoingEdges(PAGEdge::Load).end(); ++lit) {
		for (PAGNode::iterator sit =
				cur->getIncomingEdges(PAGEdge::Store).begin();
				sit != cur->getIncomingEdges(PAGEdge::Store).end(); ++sit) {
			addToNodeMatchMap((*lit)->getDstID(), (*sit)->getSrcID());
			stateProp((*lit)->getDstID(), (*sit)->getSrcID(), DPTItem::S1);
			//propagate reachable with (*lit)->getDstID()
			for (DPTItemSet::iterator iter =
					nodesVisited[(*lit)->getDstID()].begin();
					iter != nodesVisited[(*lit)->getDstID()].end(); ++iter) {
				if ((*iter).state == DPTItem::S1) {
					stateProp((*iter).root, (*sit)->getSrcID(), DPTItem::S1);
				}
//				//TODO: should not be S3 here?
//				else if (iter->second == DPTItem::S3) {
//					stateProp(iter->first, (*sit)->getSrcID(), DPTItem::S3);
//				}
//				else
//					assert(false && "wrong state!!");
			}
		}
	}
}

void DAAPass::propAliasUpToDirectFlow(DPTItem& item) {

	PAGNode* root = pag->getPAGNode(item.root);
	PAGNode* cur = pag->getPAGNode(item.cur);

	for (PAGNode::iterator sit = root->getIncomingEdges(PAGEdge::Store).begin();
			sit != root->getIncomingEdges(PAGEdge::Store).end(); ++sit) {
		for (PAGNode::iterator lit =
				cur->getOutgoingEdges(PAGEdge::Load).begin();
				lit != cur->getOutgoingEdges(PAGEdge::Load).end(); ++lit) {
			addToNodeMatchMap((*lit)->getDstID(), (*sit)->getSrcID());
			stateProp((*sit)->getSrcID(), (*lit)->getDstID(), DPTItem::S3);
			//propagate reachable with (*sit)->getSrcID()
			for (DPTItemSet::iterator iter =
					nodesVisited[(*sit)->getSrcID()].begin();
					iter != nodesVisited[(*sit)->getSrcID()].end(); ++iter) {
				if ((*iter).state == DPTItem::S3) {
					stateProp((*iter).root, (*lit)->getDstID(), DPTItem::S3);
				}
				//				//TODO: should not be S1 here
				//				else if (iter->second == DPTItem::S1) {
				//					stateProp( iter->first,(*lit)->getDstID(), DPTItem::S1);
				//				}
				//				else
				//					assert(false && "wrong state!!");
			}
		}
	}
}

void DAAPass::MatchLoadStore(DPTItem& origItem, NodeID cur,
		DPTItem::State propState) {

	if (propState == DPTItem::S1) {
		AliasSet& aliasSet = getMatchSTdstFromLDsrc(cur);
		for (AliasSet::iterator ait = aliasSet.begin(); ait != aliasSet.end();
				++ait) {
			DBOUT(DDDA,
					outs() << "\tAlias Match LoadDst node " << cur << " to "
							<< "StoreSrc node " << *ait << "\n");

			stateProp(origItem, *ait, propState);
		}
	}

	else if (propState == DPTItem::S3) {
		AliasSet& aliasSet = getMatchLDsrcFromSTdst(cur);
		for (AliasSet::iterator ait = aliasSet.begin(); ait != aliasSet.end();
				++ait) {
			DBOUT(DDDA,
					outs() << "\tAlias  Match StoreSrc node " << cur << " to "
							<< "LoadDst node " << *ait << "\n");
			stateProp(origItem, *ait, propState);
		}
	} else
		assert(false && "no such state transition!!");
}

void DAAPass::handleS1(DPTItem& item) {

	PAGNode* pNode = pag->getPAGNode(item.cur);

	for (PAGNode::iterator iter =
			pNode->getIncomingEdges(PAGEdge::Addr).begin();
			iter != pNode->getIncomingEdges(PAGEdge::Addr).end(); ++iter) {
		DBOUT(DDDA, outs() << "\tinverse through Addr edge\n");
		stateProp(item, (*iter)->getSrcID(), DPTItem::S2);
	}

	for (PAGNode::iterator iter =
			pNode->getIncomingEdges(PAGEdge::Copy).begin();
			iter != pNode->getIncomingEdges(PAGEdge::Copy).end(); ++iter) {
		DBOUT(DDDA, outs() << "\tinverse through Copy edge\n");
		stateProp(item, (*iter)->getSrcID(), DPTItem::S1);
	}

	for (PAGNode::iterator iter = pNode->getIncomingEdges(PAGEdge::NormalGep).begin();
			iter != pNode->getIncomingEdges(PAGEdge::NormalGep).end(); ++iter) {
		DBOUT(DDDA, outs() << "\tinverse through Gep edge\n");
		stateProp(item, (*iter)->getSrcID(), DPTItem::S1, (*iter));
	}

	for (PAGNode::iterator iter = pNode->getIncomingEdges(PAGEdge::VariantGep).begin();
			iter != pNode->getIncomingEdges(PAGEdge::VariantGep).end(); ++iter) {
		DBOUT(DDDA, outs() << "\tinverse through Gep edge\n");
		stateProp(item, (*iter)->getSrcID(), DPTItem::S1, (*iter));
	}

	for (PAGNode::iterator iter =
			pNode->getIncomingEdges(PAGEdge::Call).begin();
			iter != pNode->getIncomingEdges(PAGEdge::Call).end(); ++iter) {
		DBOUT(DDDA, outs() << "\tinverse through Call edge\n");
		stateProp(item, (*iter)->getSrcID(), DPTItem::S1, (*iter));
	}

	for (PAGNode::iterator iter = pNode->getIncomingEdges(PAGEdge::Ret).begin();
			iter != pNode->getIncomingEdges(PAGEdge::Ret).end(); ++iter) {
		DBOUT(DDDA, outs() << "\tinverse through Return edge\n");
		stateProp(item, (*iter)->getSrcID(), DPTItem::S1, (*iter));
	}

	for (PAGNode::iterator iter =
			pNode->getIncomingEdges(PAGEdge::Load).begin();
			iter != pNode->getIncomingEdges(PAGEdge::Load).end(); ++iter) {
		MatchLoadStore(item, pNode->getId(), DPTItem::S1);
	}

}

void DAAPass::handleS2(DPTItem& item) {

	PAGNode* pNode = pag->getPAGNode(item.cur);

	DBOUT(DDDA, outs() << "\tSit at Addr node " << pNode->getId() << "\n");
	assert(pNode->getInEdges().empty() && "in edge should be emtpy");
	assert(pNode->getOutEdges().size() == 1 && "should only have one outedge!!");

	for (PAGNode::iterator iter =
			pNode->getOutgoingEdges(PAGEdge::Addr).begin();
			iter != pNode->getOutgoingEdges(PAGEdge::Addr).end(); ++iter) {
		stateProp(item, (*iter)->getDstID(), DPTItem::S3);
	}
}

void DAAPass::handleS3(DPTItem& item) {

	PAGNode* pNode = pag->getPAGNode(item.cur);

	assert(
			pNode->getOutgoingEdges(PAGEdge::Addr).empty()
					&& "no outgoing addr edge");

	for (PAGNode::iterator iter =
			pNode->getOutgoingEdges(PAGEdge::Copy).begin();
			iter != pNode->getOutgoingEdges(PAGEdge::Copy).end(); ++iter) {
		DBOUT(DDDA, outs() << "\tforward through Copy edge\n");
		stateProp(item, (*iter)->getDstID(), DPTItem::S3);
	}

	for (PAGNode::iterator iter = pNode->getOutgoingEdges(PAGEdge::NormalGep).begin();
			iter != pNode->getOutgoingEdges(PAGEdge::NormalGep).end(); ++iter) {
		DBOUT(DDDA, outs() << "\tforward through Gep edge\n");
		stateProp(item, (*iter)->getDstID(), DPTItem::S3, (*iter));
	}

	for (PAGNode::iterator iter = pNode->getOutgoingEdges(PAGEdge::VariantGep).begin();
			iter != pNode->getOutgoingEdges(PAGEdge::VariantGep).end(); ++iter) {
		DBOUT(DDDA, outs() << "\tforward through Gep edge\n");
		stateProp(item, (*iter)->getDstID(), DPTItem::S3, (*iter));
	}

	for (PAGNode::iterator iter =
			pNode->getOutgoingEdges(PAGEdge::Call).begin();
			iter != pNode->getOutgoingEdges(PAGEdge::Call).end(); ++iter) {
		DBOUT(DDDA, outs() << "\tforward through Call edge\n");
		stateProp(item, (*iter)->getDstID(), DPTItem::S3, (*iter));
	}

	for (PAGNode::iterator iter = pNode->getOutgoingEdges(PAGEdge::Ret).begin();
			iter != pNode->getOutgoingEdges(PAGEdge::Ret).end(); ++iter) {
		DBOUT(DDDA, outs() << "\tforward through Return edge\n");
		stateProp(item, (*iter)->getDstID(), DPTItem::S3, (*iter));
	}

	for (PAGNode::iterator iter =
			pNode->getOutgoingEdges(PAGEdge::Store).begin();
			iter != pNode->getOutgoingEdges(PAGEdge::Store).end(); ++iter) {
		MatchLoadStore(item, pNode->getId(), DPTItem::S3);
	}
}

void DAAPass::stateProp(const DPTItem& origItem, NodeID propNode,
		DPTItem::State propState, PAGEdge* gepOrCallRetEdge) {
	stateProp(origItem.root, propNode, propState);
}

void DAAPass::stateProp(NodeID root, NodeID node, DPTItem::State state) {

	DPTItem item(node, root, state);

	// if we haven't see this item state in this propNode before
	if (nodesVisited[node].find(item) == nodesVisited[node].end()) {
		nodesVisited[node].insert(item);
		worklist.push_front(item);

		// we only care about value alias
		// do not add object as aliases when we at S2
		if (state != DPTItem::S2)
			addToAliasSet(root, node);

		DBOUT(DDDA,
				outs() << "\t\t#Propagate to node " << node << "(root " << root
						<< ")" << "state " << state << "\n");

	} else {
		DBOUT(DDDA,
				outs() << "\t\t#Already visited " << node << "(root " << root
						<< ")" << "state " << state << "\n");
	}
}

void DAAPass::enableCache(NodeID nodeId) {
	if (ENABLECACHE) {
		// cache the result
		DBOUT(DCache, outs() << "cache ");
		DBOUT(DCache, dumpAliasSet(nodeId, nodeToAliasMap[nodeId]));
		ptsCache.insert(std::make_pair(nodeId, nodeToAliasMap[nodeId]));
	}
}

bool DAAPass::reuseCache(NodeID nodeId, NodeID root, DPTItem::State propState) {
	AliasSetMap::iterator cit = ptsCache.find(nodeId);
	if (cit != ptsCache.end()) {
		for (AliasSet::iterator ait = cit->second.begin();
				ait != cit->second.end(); ++ait) {
			PAGNode* pNode = pag->getPAGNode(*ait);
			if (propState == DPTItem::S1) {
				for (PAGNode::iterator iter = pNode->getIncomingEdges(
						PAGEdge::Store).begin();
						iter != pNode->getIncomingEdges(PAGEdge::Store).end();
						++iter) {
					stateProp(root, ((*iter)->getSrcID()), propState);
				}
			} else if (propState == DPTItem::S3) {
				for (PAGNode::iterator iter = pNode->getOutgoingEdges(
						PAGEdge::Load).begin();
						iter != pNode->getOutgoingEdges(PAGEdge::Load).end();
						++iter) {
					stateProp(root, ((*iter)->getDstID()), propState);
				}
			} else
				assert(false && "no such state transition!!");
		}
		return true;
	} else
		return false;
}

void DAAPass::addToNodeMatchMap(NodeID loadDst, NodeID storeSrc) {

	if ((pag->isValidPointer(loadDst) == false
			&& pag->isValidPointer(storeSrc) == false) || loadDst == storeSrc)
		return;

	bool add1 = MatchLDSrcToSTdstMap[loadDst].test_and_set(storeSrc);
	bool add2 = MatchSTdstToLDsrcMap[storeSrc].test_and_set(loadDst);

	if (add1 && add2)
		DBOUT(DDDA,
				outs() << "\tCapture Match StoreSrc node " << storeSrc
						<< " to LoadDst node " << loadDst << "\n");

	addToAliasSet(loadDst, storeSrc);
}

AliasSet& DAAPass::getMatchSTdstFromLDsrc(NodeID cur) {
	return MatchLDSrcToSTdstMap[cur];
}

AliasSet& DAAPass::getMatchLDsrcFromSTdst(NodeID cur) {
	return MatchSTdstToLDsrcMap[cur];
}

void DAAPass::addToAliasSet(NodeID root, NodeID node) {
	//	assert(nodeToAliasMap[root].test(node)
	//			== false && "should never seen this before!!");
	// avoid self aliasing and invalid pointer
	if ((pag->isValidPointer(root) == false
			&& pag->isValidPointer(node) == false) || root == node)
		return;

	bool add1 = nodeToAliasMap[root].test_and_set(node);
	bool add2 = nodeToAliasMap[node].test_and_set(root);

	if (add1 && add2)
		DBOUT(DDDA,
				outs() << "\t\t@Add AliasSet (" << node << "--> " << root << ")"
						<< "\n");
}

bool DAAPass::isAlias(NodeID node1, NodeID node2) {
	// include self-alias
	if (node1 == node2)
		return true;
	else if (nodeToAliasMap[node1].test(node2)) {
		assert(
				nodeToAliasMap[node2].test(node1)
						&& "two aliases should be Symetric");
		return true;
	}

	return false;
}

Size_t DAAPass::getTotalNumberOfQuery() {

	Size_t query_num = 0;
	for (NodeBS::iterator nIter = getAllValidPtrs().begin(); nIter != getAllValidPtrs().end(); ++nIter) {
		query_num++;
	}
	assert(getAllValidPtrs().count() == query_num
					&& "candidate pointer not match!!");
	return query_num;
}

bool DAAPass::checkEarlyTemination() {
	if (earlyTerminate)
		return true;
	if (stepNum++ > QUERYBUDGET) {
		wrnMsg(" Early termination  due to excess the budget \n ");
		earlyTerminate = true;
		return true;
	}
	return false;
}

////@==============================================}

