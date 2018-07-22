/*
 * RegularPTPass.cpp
 *
 *  Created on: May 14, 2013
 *      Author: rocky
 */

#include "DDA/RegularPTPass.h"
#include "Util/AnalysisUtil.h"

#include <llvm/Support/raw_ostream.h>	// for output
#include <llvm/Support/CommandLine.h> // for tool output file
using namespace llvm;
using namespace analysisUtil;

#define QUERYBUDGET 3000

char RegularPTPass::ID = 1;
char RefinePTPass::ID = 2;

static RegisterPass<RegularPTPass> REGPTS("preg",
		"Demand-driven regular points-to analysis");

static RegisterPass<RefinePTPass> RFINEPTS("prefine",
		"Demand-driven refinement points-to analysis");

/// register this into alias analysis group
static RegisterAnalysisGroup<AliasAnalysis> AA_GROUP(REGPTS);


static cl::opt<bool> PTSPrint("print-pt", cl::init(false),
		cl::desc("Print points-to set"));

static cl::opt<bool> ALIASPrint("pts-alias", cl::init(false),
		cl::desc("Print alias set"));

void RegularPTPass::resetStatePerQuery() {

	aliasCheckPairs.clear();
	earlyTerminate = false;
	stepNum = 0;
}

void RegularPTPass::dumpAliasSetWithPointsToMap() {

	for (NodeBS::iterator nIter = getAllValidPtrs().begin();
			nIter != getAllValidPtrs().end(); ++nIter) {
		AliasSet aliases;
		PointsToMap::iterator npit = ptsCache.find(*nIter);
		assert(npit != ptsCache.end() && "points-to result is not in cache");
		for (NodeBS::iterator xIter = getAllValidPtrs().begin(); xIter != getAllValidPtrs().end(); ++xIter) {
			PointsToMap::iterator xpit = ptsCache.find(*xIter);
			assert(
					xpit != ptsCache.end()
							&& "points-to result is not in cache");
			// if two points-to set intersection not null, btw exclude self-alias
			if (npit->second.intersects(xpit->second) && *nIter != *xIter)
				aliases.test_and_set(*xIter);
		}
		dumpAliasSet(*nIter, aliases);
	}
}

Size_t RegularPTPass::getTotalNumberOfQuery() {

	Size_t query_num = 0;
	for (NodeBS::iterator nIter = getAllValidPtrs().begin(); nIter != getAllValidPtrs().end(); ++nIter) {
		query_num++;
	}
	assert(getAllValidPtrs().count() == query_num
					&& "candidate pointer not match!!");
	return query_num;
}

bool RegularPTPass::checkEarlyTemination() {
	if (earlyTerminate)
		return true;
	if (stepNum++ > QUERYBUDGET) {
		wrnMsg(" Early termination  due to excess the budget \n ");
		earlyTerminate = true;
		return true;
	}
	return false;
}

void RegularPTPass::analyze(llvm::Module& module){
	initialize(module);

	Size_t query_num = 0;
	Size_t total_query = getTotalNumberOfQuery();
	DBOUT(DGENERAL,
			outs() << pasMsg("total query number: ") << total_query << "\n");

	// start DAA analysis
	for (NodeBS::iterator nIter = getAllValidPtrs().begin();
			nIter != getAllValidPtrs().end(); ++nIter) {
		NodeID nodeId = *nIter;
		DBOUT(DGENERAL,
				outs() << pasMsg("Answering query for node") << nodeId << "\t ("
						<< ++query_num << "/" << total_query << ")" << " \n");

		PointsTo pts = regularPT(nodeId);
		if (PTSPrint)
			dumpPointsToSet(nodeId, pts);

		resetStatePerQuery();
	}

	if (ALIASPrint) {
		dumpAliasSetWithPointsToMap();
	}

	finalize();
}

/*!
 * we start from here
 */
bool RegularPTPass::runOnModule(Module& module) {

	analyze(module);

	return false;
}

////@{==============================================
/*
 * Demand-Driven Points-to Analysis for Java (OOPSLA '05)
 */
PointsTo RegularPTPass::regularPT(NodeID nodeId) {

	// find whether we have already visited this node
	PointsToMap::iterator iter = ptsCache.find(nodeId);
	if (iter != ptsCache.end()) {
		DBOUT(DDDA,
				outs() << "Using caching results for node " << nodeId << "\n");
		return iter->second;
	}

	PointsTo pts;
	NodeList workList;
	NodeSet visited;
	propagate(nodeId, workList, visited);

	while (!workList.empty()) {
		NodeID nodeId = workList.front();
		workList.pop_front();
		DBOUT(DDDA, outs() << "AT node" << nodeId << "\n");

		PAGNode* pNode = pag->getPAGNode(nodeId);
		// assume we have pNode as 'w', and value flows from src node.
		for (PAGNode::iterator iter = pNode->getInEdges().begin();
				iter != pNode->getInEdges().end(); ++iter) {
			PAGEdge* pedge = (*iter);
			NodeID srcId = pedge->getSrcID();
			// 'o-->w" (address)
			if (isa<AddrPE>(pedge)) {
				DBOUT(DDDA,
						outs() << "\t++Add  node" << nodeId << " with PointsTo "
								<< srcId << "\n");
				pts.test_and_set(srcId);
			}
			// "y-->w'  (copy)
			else if (isa<CopyPE>(pedge)) {
				DBOUT(DDDA, outs() << "To Copy src" << srcId << "\n");
				propagate(srcId, workList, visited);
			}
			// "y-->w'  (return)
			else if (isa<RetPE>(pedge)) {
				DBOUT(DDDA, outs() << "To Ret src" << srcId << "\n");
				propagate(srcId, workList, visited);
			}
			// "y-->w'  (callsite)
			else if (isa<CallPE>(pedge)) {
				DBOUT(DDDA, outs() << "To Call src" << srcId << "\n");
				propagate(srcId, workList, visited);
			}
			// "y-->w'  (ptr gep)
			else if (isa<GepPE>(pedge)) {
				DBOUT(DDDA, outs() << "To Gep src" << srcId << "\n");
				propagate(srcId, workList, visited);
			}
			// 'p-->w' (load)
			else if (isa<LoadPE>(pedge)) {

				matchLoadStore(pedge, workList, visited);
			}
		}
	}

	// cache the result
	DBOUT(DDDA, outs() << "cache ");
	DBOUT(DDDA, dumpPointsToSet(nodeId, pts));
	ptsCache.insert(std::make_pair(nodeId, pts));

	return pts;
}

/*!
 * match the load and store, transit the status from dst of load edge to src of store edge
 */
void RegularPTPass::matchLoadStore(PAGEdge* load, NodeList &workList,
		NodeSet& visited) {

	NodeID loadDst = load->getDstID();
	NodeID loadSrc = load->getSrcID();
	// try to search all possible stores for matching with the load
	// for example, given a 'y-->q' (store) and 'p->w' (load)
	// if pts(q) alias with pts(p), then there is a match path flows from 'w'  to 'y'
	for (PAGEdge::PAGEdgeSetTy::iterator eIter =
			pag->getEdgeSet(PAGEdge::Store).begin();
			eIter != pag->getEdgeSet(PAGEdge::Store).end(); ++eIter) {
		PAGEdge* store = (*eIter);
		NodeID storeDst = store->getDstID();
		NodeID storeSrc = store->getSrcID();
		// in order to speed up the analysis, we may need to enable caching matched pairs
		// find out whether match path 'w' to 'y' has been processed
		if (checkMatchCache(load->getEdgeID(), store->getEdgeID())) {
			propagate(storeSrc, workList, visited);
			DBOUT(DDDA,
					outs() << "Enable caching from loadDst " << loadDst
							<< " to storeSrc " << storeSrc << "\n");
			continue;
		}
		// in order to avoid dead loop, make sure that we only match load/store once per call stack
		// check 'p' and 'q' whether it has already been processed
		if (checkRecurAliasing(load->getEdgeID(), store->getEdgeID())) {
			DBOUT(DDDA,
					outs() << "Already checked loadSrc " << loadSrc
							<< " storeDst " << storeDst << "\n");
			continue;
		} else {
			addCheckRecurAliasing(load->getEdgeID(), store->getEdgeID());
		}

		DBOUT(DDDA, outs() << "Sit at Load src" << loadSrc << "\n");
		// get the pts of 'p'
		PointsTo loadpts = regularPT(loadSrc);
		// storeDst refers to 'q'
		DBOUT(DDDA,
				outs() << "Test store dst node" << storeDst
						<< " for load edge (" << loadSrc << "->" << loadDst
						<< ")" << "\n");
		// get the pts of 'q'
		PointsTo storepts = regularPT(storeDst);
		// intersect pts(p) and pts(q) if not empty, propagate the value-flow to 'y'
		if (loadpts.intersects(storepts)) {
			DBOUT(DDDA,
					outs() << "\tMatched!! move from loadDst " << loadDst
							<< " to loadSrc node" << loadSrc << " to storeSrc"
							<< storeSrc << "\n");
			addToMatchCache(load->getEdgeID(), store->getEdgeID());
			propagate(storeSrc, workList, visited);
		}

		// remember to remove the recur aliasing check to make sure one stack trace doesn't mess with another stack.
		removeCheckRecurAliasing(load->getEdgeID(), store->getEdgeID());
	}

}

/*!
 * Propagate the state to another node
 */
void RegularPTPass::propagate(NodeID nodeId, NodeList &workList,
		NodeSet& markedSet) {
	// if excess the query budget then we return directly and won't add the worklist
	if (markedSet.find(nodeId) == markedSet.end()) {
		markedSet.insert(nodeId);
		workList.push_front(nodeId);
	} else {
		DBOUT(DDDA, outs() << "Already visited node" << nodeId << "\n");
	}
}
////@==============================================}

////@{==============================================
/*
 * Refinement-Based Context Sensitive Points-to Analysis for Java (PLDI' 06)
 */

bool RefinePTPass::runOnModule(Module& module) {

	/// start analysis
	analyze(module);
	return false;
}

/// analysis
void RefinePTPass::analyze(llvm::Module& module){

	initialize(module);

	Size_t query_num = 0;
	Size_t total_query = getTotalNumberOfQuery();
	DBOUT(DGENERAL,
			outs() << pasMsg("total query number: ") << total_query << "\n");

	// start DAA analysis
	for (NodeBS::iterator nIter = getAllValidPtrs().begin();
			nIter != getAllValidPtrs().end(); ++nIter) {
		NodeID nodeId = *nIter;
		DBOUT(DGENERAL,
				outs() << pasMsg("Answering query for node") << nodeId << "\t ("
						<< ++query_num << "/" << total_query << ")" << " \n");

		PointsTo pts;
		NodeBS visited;
		findPointsTo(nodeId, visited, pts);
		visited.clear();

		if (PTSPrint)
			dumpPointsToSet(nodeId, pts);

		resetStatePerQuery();
	}

	if (ALIASPrint) {
		dumpAliasSetWithPointsToMap();
	}

	finalize();
}

void RefinePTPass::findPointsTo(NodeID nodeId, NodeBS &visited, PointsTo& pts) {

	// only cache the node that ask the query, and do not cache the node during traversing.
	bool cacheable = (visited.empty());
	// reuse the points-to information from last query
	PointsToMap::iterator iter = ptsCache.find(nodeId);
	if (iter != ptsCache.end()) {
		DBOUT(DDDA, outs() << "Using caching results for ");
		DBOUT(DDDA, dumpPointsToSet(nodeId, iter->second));
		pts |= iter->second;
		return;
	}

	// find whether we have already visited this node at one query, to make sure we only visit node once per call stack
	if (visited.test(nodeId)) {
		DBOUT(DDDA, outs() << "Already visited node" << nodeId << "\n");
		return;
	}

#if 0
	if(checkEarlyTemination())
	return;
#endif

	visited.set(nodeId);

	DBOUT(DDDA,
			outs() << "AT node" << nodeId << " cacheable " << cacheable
					<< "\n");

	PAGNode* pNode = pag->getPAGNode(nodeId);
	// assume we have pNode as 'w', and value flows from src node.
	for (PAGNode::iterator iter = pNode->getInEdges().begin();
			iter != pNode->getInEdges().end(); ++iter) {
		PAGEdge* pedge = (*iter);
		NodeID srcId = pedge->getSrcID();
		// 'o-->w" (address)
		if (isa<AddrPE>(pedge)) {
			DBOUT(DDDA,
					outs() << "\t++Add  node" << nodeId << " with PointsTo "
							<< srcId << "\n");
			pts.test_and_set(srcId);
		}
		// "y-->w'  (copy)
		else if (isa<CopyPE>(pedge)) {
			DBOUT(DDDA, outs() << "To copy node" << srcId << "\n");
			findPointsTo(srcId, visited, pts);
		}
		// "y-->w'  (gep)
		else if (isa<GepPE>(pedge)) {
			DBOUT(DDDA, outs() << "To gep node" << srcId << "\n");
			findPointsTo(srcId, visited, pts);
		}
		// "y-->w'  (call)
		else if (isa<CallPE>(pedge)) {
			DBOUT(DDDA, outs() << "To call node" << srcId << "\n");
			findPointsTo(srcId, visited, pts);
		}
		// "y-->w'  (return)
		else if (isa<RetPE>(pedge)) {
			DBOUT(DDDA, outs() << "To return node" << srcId << "\n");
			findPointsTo(srcId, visited, pts);
		}
		// 'p-->w' (load)
		else if (isa<LoadPE>(pedge)) {
			DBOUT(DDDA, outs() << "To Load src" << srcId << "\n");

			// try to search all possible stores   'y-->q' (store)
			matchLoadWithStore(pts, pedge, visited);
		}
	}

	// cache the result
	if (cacheable && earlyTerminate == false) {
		DBOUT(DDDA, outs() << "cache ");
		DBOUT(DDDA, dumpPointsToSet(nodeId, pts));
		ptsCache[nodeId] = pts;
	}
}

/*!
 * match the load and store, transit the status from dst of load edge to src of store edge
 */
void RefinePTPass::matchLoadWithStore(PointsTo &pts, PAGEdge* load,
		NodeBS &visited) {

	NodeID loadDst = load->getDstID();
	NodeID loadSrc = load->getSrcID();

	// we first try to find the store edge we have, only the store edge which connected undirected to the load edge will be considered
	if (!candidateStoresMap.count(load->getEdgeID()))
		refineStoreEdgeSearch(load);

	// try to search all possible stores for matching with the load
	// for example, given a 'y-->q' (store) and 'p->w' (load)
	// if pts(q) alias with pts(p), then there is a match path flows from 'w'  to 'y'
	for (PAGEdge::PAGEdgeSetTy::iterator eIter =
			candidateStoresMap[load->getEdgeID()].begin();
			eIter != candidateStoresMap[load->getEdgeID()].end(); ++eIter) {
		PAGEdge* store = (*eIter);
		assert(store->getEdgeKind() == PAGEdge::Store && "not a store edge!");
		NodeID storeDst = store->getDstID();
		NodeID storeSrc = store->getSrcID();
		// in order to speed up the analysis, we may need to enable caching matched pairs
		// find out whether match path 'w' to 'y' has been processed
		if (checkMatchCache(load->getEdgeID(), store->getEdgeID())) {
			DBOUT(DDDA,
					outs() << "Enable caching from loadDst " << loadDst
							<< " to storeSrc " << storeSrc << "\n");
			findPointsTo(storeSrc, visited, pts);
			continue;
		}
		// in order to avoid dead loop, make sure that we only match load/store once per call stack
		// check 'p' and 'q' whether it has already been processed
		if (checkRecurAliasing(load->getEdgeID(), store->getEdgeID())) {
			DBOUT(DDDA,
					outs() << "Already checked Store edge" << "(" << storeSrc
							<< "-->" << storeDst << ")" << "Load edge" << "("
							<< loadSrc << "-->" << loadDst << ")" << "\n");
			continue;
		} else {
			DBOUT(DDDA,
					outs() << "Add recur aliasing check loadSrc " << loadSrc
							<< " storeDst " << storeDst << "\n");
			addCheckRecurAliasing(load->getEdgeID(), store->getEdgeID());
		}

		DBOUT(DDDA,
				outs() << "Sit at Load edge" << "(" << loadSrc << "-->"
						<< loadDst << ")" << "\n");
		// get the pts of 'p'
		NodeBS loadvisited;
		PointsTo loadpts;
		findPointsTo(loadSrc, loadvisited, loadpts);
		loadvisited.clear();

		// storeDst refers to 'q'
		DBOUT(DDDA,
				outs() << "Test store edge" << "(" << storeSrc << "-->"
						<< storeDst << ") with " << "Load edge" << "("
						<< loadSrc << "-->" << loadDst << ")" << "\n");
		// get the pts of 'q'
		NodeBS storevisited;
		PointsTo storepts;
		findPointsTo(storeDst, storevisited, storepts);
		storevisited.clear();

		// intersect pts(p) and pts(q) if not empty, propagate the value-flow to 'y'
		if (loadpts.intersects(storepts)) {
			DBOUT(DDDA,
					outs() << "Match!! Store edge" << "(" << storeSrc << "-->"
							<< storeDst << ")" << "Load edge" << "(" << loadSrc
							<< "-->" << loadDst << ")" << "\n");
			addToMatchCache(load->getEdgeID(), store->getEdgeID());
			findPointsTo(storeSrc, visited, pts);
		}

		loadpts.clear();
		storepts.clear();
		// remember to remove the recur aliasing check to make sure one stack trace doesn't mess with another stack.
		DBOUT(DDDA,
				outs() << "Delete recur aliasing check loadSrc " << loadSrc
						<< " storeDst " << storeDst << "\n");
		removeCheckRecurAliasing(load->getEdgeID(), store->getEdgeID());
	}

}

void RefinePTPass::refineStoreEdgeSearch(PAGEdge* load) {

	NodeList workList;
	NodeBS visitedSet;
	workList.push_front(load->getSrcID());
	while (!workList.empty()) {
		NodeID nodeId = workList.front();
		workList.pop_front();
		visitedSet.set(nodeId);

		PAGNode* pNode = pag->getPAGNode(nodeId);
		for (PAGNode::iterator iter = pNode->InEdgeBegin();
				iter != pNode->InEdgeEnd(); iter++) {
			PAGEdge* pedge = (*iter);
			if (pedge->getEdgeKind() == PAGEdge::Store) {
				candidateStoresMap[load->getEdgeID()].insert(pedge);
			}
			NodeID succ = pedge->getSrcID();
			if (!visitedSet.test(succ))
				workList.push_front(succ);
		}
		for (PAGNode::iterator iter = pNode->OutEdgeBegin();
				iter != pNode->OutEdgeEnd(); iter++) {
			PAGEdge* pedge = (*iter);
			if (pedge->getEdgeKind() == PAGEdge::Store) {
				candidateStoresMap[load->getEdgeID()].insert(pedge);
			}
			NodeID succ = pedge->getDstID();
			if (!visitedSet.test(succ))
				workList.push_front(succ);
		}
	}
}

////@==============================================}
