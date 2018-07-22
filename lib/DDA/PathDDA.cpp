/*
 * PathDDA.cpp
 *
 *  Created on: Jul 7, 2014
 *      Author: Yulei Sui, Sen Ye
 */

#include "DDA/PathDDA.h"
#include "DDA/FlowDDA.h"
#include "DDA/ContextDDA.h"
#include "DDA/DDAClient.h"
#include <llvm/Support/CommandLine.h>
#include <llvm/IR/Dominators.h>

using namespace llvm;

static cl::opt<unsigned long long> pathBudget("pathbg",  cl::init(ULONG_MAX - 1),
        cl::desc("Maximum step budget of path-sensitive traversing"));

/*!
 * Constructor
 */
PathDDA::PathDDA(SVFModule m, DDAClient* client)
    : CondPTAImpl<VFPathCond>(PointerAnalysis::PathS_DDA),
      DDAVFSolver<VFPathVar,VFPathPtSet,PathDPItem>(),
      _client(client) {
    pathCondAllocator = new DDAPathAllocator();
    contextDDA = new ContextDDA(m, client);
}

/*!
 * Destructor
 */
PathDDA::~PathDDA() {
    if(pathCondAllocator)
        delete pathCondAllocator;
    pathCondAllocator = NULL;

    if(contextDDA)
        delete contextDDA;
    contextDDA = NULL;
}

/*!
 * Initialize the analysis
 */
void PathDDA::initialize(SVFModule module) {
    CondPTAImpl<VFPathCond>::initialize(module);
    buildSVFG(module);
    setCallGraph(getPTACallGraph());
    setCallGraphSCC(getCallGraphSCC());
    pathCondAllocator->allocate(module);
    stat = setDDAStat(new DDAStat(this));
    contextDDA->initialize(module);
}

/*!
 * Compute points-to set for a path-sensitive pointer
 */
const VFPathPtSet& PathDDA::computeDDAPts(const VFPathVar& var) {

    resetQuery();
    LocDPItem::setMaxBudget(pathBudget);

    NodeID id = var.get_id();
    PAGNode* node = getPAG()->getPAGNode(id);
    PathDPItem dpm = getDPIm(var, getDefSVFGNode(node));

    /// start DDA analysis
    DOTIMESTAT(double start = DDAStat::getClk());
    const VFPathPtSet& cpts = findPT(dpm);
    DOTIMESTAT(ddaStat->_AnaTimePerQuery = DDAStat::getClk() - start);
    DOTIMESTAT(ddaStat->_TotalTimeOfQueries += ddaStat->_AnaTimePerQuery);

    if(isOutOfBudgetQuery() == false)
        unionPts(var,cpts);
    else
        handleOutOfBudgetDpm(dpm);

    if (this->printStat())
        DOSTAT(stat->performStatPerQuery(id));
    DBOUT(DGENERAL, stat->printStatPerQuery(id,getBVPointsTo(getPts(var))));
    return this->getPts(var);
}

/*!
 * Compute points-to set for an unconditional pointer
 */
void PathDDA::computeDDAPts(NodeID id) {

    VFPathCond vfpath;
    VFPathVar var(vfpath, id);
    computeDDAPts(var);
}

/*!
 * Handle out-of-budget dpm
 */
void PathDDA::handleOutOfBudgetDpm(const PathDPItem& dpm) {

    DBOUT(DGENERAL,outs() << "~~~Out of budget query, downgrade to context sensitive analysis \n");
    contextDDA->computeDDAPts(dpm.getCurNodeID());
    ContextCond cxt;
    CxtVar cxtVar(cxt, dpm.getCurNodeID());
    CxtLocDPItem cxtDpm = contextDDA->getDPIm(cxtVar, dpm.getLoc());
    const CxtPtSet& cxtPts = contextDDA->getPts(cxtVar);
    VFPathPtSet pathPts;
    for(CxtPtSet::iterator it = cxtPts.begin(), eit = cxtPts.end(); it!=eit; ++it) {
        VFPathCond vfpath;
        CallStrCxt& cxt = vfpath.getContexts();
        cxt = (*it).get_cond().getContexts();
        VFPathVar var(vfpath, (*it).get_id());
        pathPts.set(var);
    }
    updateCachedPointsTo(dpm,pathPts);
    unionPts(dpm.getCondVar(),pathPts);
    addOutOfBudgetDpm(dpm);
}

/*!
 * context conditions of local(not in recursion)  and global variables are compatible
 */
bool PathDDA::isCondCompatible(const VFPathCond& cond1, const VFPathCond& cond2, bool singleton) const {
    VFPathCond::PathCond* pathCond = pathCondAllocator->condAnd(cond1.getPaths(),cond2.getPaths());
    bool pathCompatible = (pathCond!=pathCondAllocator->getFalseCond());

    if(singleton)
        return pathCompatible;

    int i = cond1.cxtSize() - 1;
    int j = cond2.cxtSize() - 1;
    for(; i >= 0 && j>=0; i--, j--) {
        if(cond1.getContexts()[i] != cond2.getContexts()[j])
            return false;
    }
    return pathCompatible;
}

/*!
 * Generate field objects for structs
 */
VFPathPtSet PathDDA::processGepPts(const GepSVFGNode* gep, const VFPathPtSet& srcPts) {
    VFPathPtSet tmpDstPts;
    for (VFPathPtSet::iterator piter = srcPts.begin(); piter != srcPts.end(); ++piter) {

        VFPathVar ptd = *piter;
        if (isBlkObjOrConstantObj(ptd.get_id()))
            tmpDstPts.set(ptd);
        else {
            if (isa<VariantGepPE>(gep->getPAGEdge())) {
                setObjFieldInsensitive(ptd.get_id());
                VFPathVar var(ptd.get_cond(),getFIObjNode(ptd.get_id()));
                tmpDstPts.set(var);
            }
            else if (const NormalGepPE* normalGep = dyn_cast<NormalGepPE>(gep->getPAGEdge())) {
                VFPathVar var(ptd.get_cond(),getGepObjNode(ptd.get_id(),normalGep->getLocationSet()));
                tmpDstPts.set(var);
            }
            else
                assert(false && "new gep edge?");
        }
    }
    DBOUT(DDDA, outs() << "\t return created gep objs ");
    DBOUT(DDDA, outs() << srcPts.toString());
    DBOUT(DDDA, outs() << " --> ");
    DBOUT(DDDA, outs() << tmpDstPts.toString());
    DBOUT(DDDA, outs() << "\n");

    return tmpDstPts;
}

bool PathDDA::testIndCallReachability(PathDPItem& dpm, const llvm::Function* callee, llvm::CallSite cs) {
    if(getPAG()->isIndirectCallSites(cs)) {
        NodeID id = getPAG()->getFunPtr(cs);
        PAGNode* node = getPAG()->getPAGNode(id);
        VFPathVar funptrVar(dpm.getCondVar().get_cond(), id);
        PathDPItem funptrDpm = getDPIm(funptrVar,getDefSVFGNode(node));
        PointsTo pts = getBVPointsTo(findPT(funptrDpm));
        if(pts.test(getPAG()->getObjectNode(callee)))
            return true;
        else
            return false;
    }
    return true;
}

/*!
 * get callsite id from call, return 0 if it is a spurious call edge
 * translate the callsite id from pre-computed callgraph on SVFG to the one on current callgraph
 */
CallSiteID PathDDA::getCSIDAtCall(PathDPItem& dpm, const SVFGEdge* edge) {

    CallSiteID svfg_csId = 0;
    if (const CallDirSVFGEdge* callEdge = dyn_cast<CallDirSVFGEdge>(edge))
        svfg_csId = callEdge->getCallSiteId();
    else
        svfg_csId = cast<CallIndSVFGEdge>(edge)->getCallSiteId();

    CallSite cs = getSVFG()->getCallSite(svfg_csId);
    const Function* callee = edge->getDstNode()->getBB()->getParent();

    if(getPTACallGraph()->hasCallSiteID(cs,callee)) {
        return getPTACallGraph()->getCallSiteID(cs,callee);
    }

    return 0;
}

/*!
 * get callsite id from return, return 0 if it is a spurious return edge
 * translate the callsite id from pre-computed callgraph on SVFG to the one on current callgraph
 */
CallSiteID PathDDA::getCSIDAtRet(PathDPItem& dpm, const SVFGEdge* edge) {

    CallSiteID svfg_csId = 0;
    if (const RetDirSVFGEdge* retEdge = dyn_cast<RetDirSVFGEdge>(edge))
        svfg_csId = retEdge->getCallSiteId();
    else
        svfg_csId = cast<RetIndSVFGEdge>(edge)->getCallSiteId();

    CallSite cs = getSVFG()->getCallSite(svfg_csId);
    const Function* callee = edge->getSrcNode()->getBB()->getParent();

    if(getPTACallGraph()->hasCallSiteID(cs,callee)) {
        return getPTACallGraph()->getCallSiteID(cs,callee);
    }

    return 0;
}

/// Handle backward propagation along direct value-flow edges
bool PathDDA::handleBKCondition(PathDPItem& dpm, const SVFGEdge* edge) {
    _client->handleStatement(edge->getSrcNode(), dpm.getCurNodeID());

    if (edge->isCallVFGEdge()) {
        /// we don't handle context in recursions, they treated as assignments
        if(CallSiteID csId = getCSIDAtCall(dpm,edge)) {

            if(isEdgeInRecursion(csId)) {
                DBOUT(DDDA,outs() << "\t\t call edge " << getPTACallGraph()->getCallerOfCallSite(csId)->getName() <<
                      "=>" << getPTACallGraph()->getCalleeOfCallSite(csId)->getName() << "in recursion \n");
                popRecursiveCallSites(dpm);
            }
            else {
                if (dpm.matchContext(csId) == false) {
                    DBOUT(DDDA,	outs() << "\t\t context not match, edge "
                          << edge->getDstID() << " --| " << edge->getSrcID() << " \t");
                    DBOUT(DDDA, dumpContexts(dpm.getCond()));
                    return false;
                }

                DBOUT(DDDA, outs() << "\t\t match contexts ");
                DBOUT(DDDA, dumpContexts(dpm.getCond()));
            }
        }
    }

    else if (edge->isRetVFGEdge()) {
        /// we don't handle context in recursions, they treated as assignments
        if(CallSiteID csId = getCSIDAtRet(dpm,edge)) {

            if(isEdgeInRecursion(csId)) {
                DBOUT(DDDA,outs() << "\t\t return edge " << getPTACallGraph()->getCalleeOfCallSite(csId)->getName() <<
                      "=>" << getPTACallGraph()->getCallerOfCallSite(csId)->getName() << "in recursion \n");
                popRecursiveCallSites(dpm);
            }
            else {
                assert(dpm.getCond().containCallStr(csId) ==false && "contain visited call string ??");
                if(dpm.pushContext(csId)) {
                    DBOUT(DDDA, outs() << "\t\t push context ");
                    DBOUT(DDDA, dumpContexts(dpm.getCond()));
                }
                else {
                    DBOUT(DDDA, outs() << "\t\t context is full ");
                    DBOUT(DDDA, dumpContexts(dpm.getCond()));
                }
            }
        }
    }

    /// Whether this is an infeasible path according to condition operations
    return dpm.addVFPath(pathCondAllocator, getVFCond(edge),edge->getDstID(),edge->getSrcID());
}


/*!
 * Get complement BB of normal SSA phi (top-level pointer)
 */
const llvm::BasicBlock* PathDDA::getComplementBBOfNPHI(const IntraPHISVFGNode* phi, u32_t pos) {

    const BasicBlock* incomingBB2 = NULL;
    if (phi->getOpVerNum() == 2) {
        if(pos == 0)
            incomingBB2 = phi->getOpIncomingBB(1);
        else
            incomingBB2 = phi->getOpIncomingBB(0);
    }

    return incomingBB2;
}


/*!
 * Get complement BB of memory SSA phi (address-taken variable)
 */
const llvm::BasicBlock* PathDDA::getComplementBBOfMPHI(const IntraMSSAPHISVFGNode* node, const SVFGEdge* candidateEdge) {
    u32_t inEdgeNum = 0;
    const BasicBlock* complementBB = NULL;
    for(SVFGNode::const_iterator it = node->InEdgeBegin() ; it!=node->InEdgeEnd(); ++it,++inEdgeNum) {
        const SVFGEdge* edge = *it;
        if(edge->getSrcNode() != candidateEdge->getSrcNode()) {
            assert((edge->isIntraVFGEdge()) && "not an intra indirect edge??");
            complementBB = edge->getSrcNode()->getBB();
        }
    }
    if(inEdgeNum == 2)
        return complementBB;

    return NULL;
}

/*!
 * Return path condition of the value-flow path
 */
PathDDA::Condition* PathDDA::getVFCond(const SVFGEdge* edge) {
    SVFGEdgeToCondMapTy::iterator it = edgeToCondMap.find(edge);
    if(it!=edgeToCondMap.end()) {
        DBOUT(DDDA, outs() << "\t\t cached condition VFEdge (" << edge->getDstID() << "--> " << edge->getSrcID() << ") : " << it->second << "\n");
        return it->second;
    }

    Condition* vfCond = pathCondAllocator->trueCond();
    Condition* complementCond = pathCondAllocator->trueCond();
    const SVFGNode* srcVFGNode = edge->getSrcNode();
    const SVFGNode* dstVFGNode = edge->getDstNode();
    const BasicBlock* srcBB = srcVFGNode->getBB();
    const BasicBlock* dstBB = dstVFGNode->getBB();

    /// two SVFGNodes within same procedure:
    /// (1) intra (2) not global variable initialization (e.g. dstBB should be not NULL)
    if (edge->isIntraVFGEdge() && dstBB) {
        /// if srcBB is an global variable initialization, then we treat its value-flow source at function entry
        if (srcBB == NULL)
            srcBB = &dstBB->getParent()->getEntryBlock();
        if (const IntraPHISVFGNode* phi = dyn_cast<IntraPHISVFGNode>(dstVFGNode)) {
            for (u32_t i = 0; i < phi->getOpVerNum(); i++) {
                if (getSVFG()->getDefSVFGNode(phi->getOpVer(i))== srcVFGNode) {
                    const BasicBlock* incomingBB = phi->getOpIncomingBB(i);
                    /// Note that top-level ptr PHI in LLVM has properties that:
                    /// we may not find the definition site at the incomingBB of an operand
                    /// for example phi(%1, if.cond), %1 may be defined at the function entry but not at BB if.cond
                    /// so we need to consider incomingBB (e.g., if.cond) as a constraint to compute path condition
                    /// calculate the path condition along path srcBB-->incomingBB-->dstBB
                    /// 1) compute incomingBB-->dstBB
                    vfCond = pathCondAllocator->ComputeIntraVFGGuard(incomingBB,dstBB);
                    if (const BasicBlock* complementBB = getComplementBBOfNPHI(phi, i)) {
                        complementCond = pathCondAllocator->getPHIComplementCond(incomingBB,complementBB,dstBB);
                        complementCond = pathCondAllocator->condAnd(vfCond,complementCond);
                    }
                    /// 2) adjust dstBB to compute srcBB-->incomingBB
                    dstBB = incomingBB;
                    break;
                }
            }
        }

        else if (const IntraMSSAPHISVFGNode* mphi = dyn_cast<IntraMSSAPHISVFGNode>(dstVFGNode)) {
            if (const BasicBlock* complementBB = getComplementBBOfMPHI(mphi, edge))
                complementCond = pathCondAllocator->getPHIComplementCond(srcVFGNode->getBB(),complementBB,dstBB);
        }
    }

    DBOUT(DDDA, outs() << "\t\t VFEdge [" << edge->getDstID() << "--> " << edge->getSrcID() << "]");

    if(srcBB && dstBB) {
        /// clean up the control flow conditions for next round guard computation
        pathCondAllocator->clearCFCond();

        if(edge->isCallVFGEdge())
            vfCond = pathCondAllocator->ComputeInterCallVFGGuard(srcBB,dstBB, getCallSite(edge).getInstruction()->getParent());
        else if(edge->isRetVFGEdge())
            vfCond = pathCondAllocator->ComputeInterRetVFGGuard(srcBB,dstBB, getRetSite(edge).getInstruction()->getParent());
        else
            vfCond = pathCondAllocator->ComputeIntraVFGGuard(srcBB,dstBB);

        vfCond = pathCondAllocator->condAnd(vfCond,complementCond);
        DBOUT(DDDA, outs() << " (bb:" << (dstVFGNode->getBB() ? dstVFGNode->getBB()->getName() : dstBB->getName()) <<
              " - bb:" << (srcVFGNode->getBB() ? srcVFGNode->getBB()->getName(): srcBB->getName()) << ") " );
    }

    DBOUT(DDDA, outs() << " condition: " << vfCond << "\n");

    edgeToCondMap[edge] = vfCond;
    return vfCond;
}
