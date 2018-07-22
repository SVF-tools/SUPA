/*
 * @file: DDAClient.cpp
 * @author: yesen
 * @date: 16 Feb 2015
 *
 * LICENSE
 *
 */


#include "DDA/DDAClient.h"
#include "DDA/FlowDDA.h"
#include <iostream>
#include <iomanip>	// for std::setw
#include <llvm/Support/CommandLine.h> // for tool output file

using namespace llvm;
using namespace analysisUtil;

static cl::opt<bool> SingleLoad("single-load", cl::init(true),
                                cl::desc("Count load pointer with same source operand as one query"));

static cl::opt<bool> DumpFree("dump-free", cl::init(false),
                              cl::desc("Dump use after free locations"));

static cl::opt<bool> DumpUninitVar("dump-uninit-var", cl::init(false),
                                   cl::desc("Dump uninitialised variables"));

static cl::opt<bool> DumpUninitPtr("dump-uninit-ptr", cl::init(false),
                                   cl::desc("Dump uninitialised pointers"));

static cl::opt<bool> DumpSUPts("dump-su-pts", cl::init(false),
                               cl::desc("Dump strong updates store"));

static cl::opt<bool> DumpSUStore("dump-su-store", cl::init(false),
                                 cl::desc("Dump strong updates store"));

static cl::opt<bool> MallocOnly("malloc-only", cl::init(true),
                                cl::desc("Only add tainted objects for malloc"));

static cl::opt<bool> TaintUninitHeap("uninit-heap", cl::init(true),
                                     cl::desc("detect uninitialized heap variables"));

static cl::opt<bool> TaintUninitStack("uninit-stack", cl::init(true),
                                      cl::desc("detect uninitialized stack variables"));

void DDAClient::answerQueries(PointerAnalysis* pta) {

    collectCandidateQueries(pta->getPAG());

    u32_t count = 0;
    for (NodeBS::iterator nIter = candidateQueries.begin();
            nIter != candidateQueries.end(); ++nIter,++count) {
        PAGNode* node = pta->getPAG()->getPAGNode(*nIter);
        if(pta->getPAG()->isValidTopLevelPtr(node)) {
            DBOUT(DGENERAL,outs() << "\n@@Computing PointsTo for :" << node->getId() <<
                  " [" << count + 1<< "/" << candidateQueries.count() << "]" << " \n");
            DBOUT(DDDA,outs() << "\n@@Computing PointsTo for :" << node->getId() <<
                  " [" << count + 1<< "/" << candidateQueries.count() << "]" << " \n");
            setCurrentQueryPtr(node->getId());
            pta->computeDDAPts(node->getId());
        }
    }
}

void FunptrDDAClient::performStat(PointerAnalysis* pta) {

    AndersenWaveDiff* ander = AndersenWaveDiff::createAndersenWaveDiff(pta->getModule());
    u32_t totalCallsites = 0;
    u32_t morePreciseCallsites = 0;
    u32_t zeroTargetCallsites = 0;
    u32_t oneTargetCallsites = 0;
    u32_t twoTargetCallsites = 0;
    u32_t moreThanTwoCallsites = 0;

    for (VTablePtrToCallSiteMap::iterator nIter = vtableToCallSiteMap.begin();
            nIter != vtableToCallSiteMap.end(); ++nIter) {
        NodeID vtptr = nIter->first;
        const PointsTo& ddaPts = pta->getPts(vtptr);
        const PointsTo& anderPts = ander->getPts(vtptr);

        PTACallGraph* callgraph = ander->getPTACallGraph();
        if(!callgraph->hasIndCSCallees(nIter->second)) {
            //outs() << "virtual callsite has no callee" << *(nIter->second.getInstruction()) << "\n";
            continue;
        }

        const PTACallGraph::FunctionSet& callees = callgraph->getIndCSCallees(nIter->second);
        totalCallsites++;
        if(callees.size() == 0)
            zeroTargetCallsites++;
        else if(callees.size() == 1)
            oneTargetCallsites++;
        else if(callees.size() == 2)
            twoTargetCallsites++;
        else
            moreThanTwoCallsites++;

        if(ddaPts.count() >= anderPts.count() || ddaPts.empty())
            continue;

        std::set<const Function*> ander_vfns;
        std::set<const Function*> dda_vfns;
        ander->getVFnsFromPts(nIter->second,anderPts, ander_vfns);
        pta->getVFnsFromPts(nIter->second,ddaPts, dda_vfns);

        ++morePreciseCallsites;
        outs() << "============more precise callsite =================\n";
        outs() << *(nIter->second).getInstruction() << "\n";
        outs() << getSourceLoc((nIter->second).getInstruction()) << "\n";
        outs() << "\n";
        outs() << "------ander pts or vtable num---(" << anderPts.count()  << ")--\n";
        outs() << "------DDA vfn num---(" << ander_vfns.size() << ")--\n";
        //ander->dumpPts(vtptr, anderPts);
        outs() << "------DDA pts or vtable num---(" << ddaPts.count() << ")--\n";
        outs() << "------DDA vfn num---(" << dda_vfns.size() << ")--\n";
        //pta->dumpPts(vtptr, ddaPts);
        outs() << "-------------------------\n";
        outs() << "\n";
        outs() << "=================================================\n";
    }

    outs() << "=================================================\n";
    outs() << "Total virtual callsites: " << vtableToCallSiteMap.size() << "\n";
    outs() << "Total analyzed virtual callsites: " << totalCallsites << "\n";
    outs() << "Indirect call map size: " << ander->getPTACallGraph()->getIndCallMap().size() << "\n";
    outs() << "Precise callsites: " << morePreciseCallsites << "\n";
    outs() << "Zero target callsites: " << zeroTargetCallsites << "\n";
    outs() << "One target callsites: " << oneTargetCallsites << "\n";
    outs() << "Two target callsites: " << twoTargetCallsites << "\n";
    outs() << "More than two target callsites: " << moreThanTwoCallsites << "\n";
    outs() << "=================================================\n";
}

u32_t CastDDAClient::checkTypeSize(PointsTo& nodes, llvm::Type* type, llvm::DataLayout* dl) {
    /// Get type size of pointer
    if (llvm::PointerType* ptType = llvm::dyn_cast<llvm::PointerType>(type)) {
        llvm::Type* elemType = ptType->getElementType();
        if (elemType->isFunctionTy()) {
            return statFunctionPointeeNumber(nodes);
        }
        else if (elemType->isSized()) {
            uint64_t pointeeSize = dl->getTypeSizeInBits(elemType);
            return statPtsTypeIncompatible(nodes, pointeeSize, dl);
        }
        else {
            /// If this is a opaque type, we assume it as a safe cast
            return 0;
        }
    }

    assert(false && "expecting a sized pointer type");
    return 0;
}


u32_t CastDDAClient::statFunctionPointeeNumber(PointsTo& pts) {
    u32_t ptsSize = 0;

    for (PointsTo::iterator ptdIt = pts.begin(), ptdEit = pts.end(); ptdIt != ptdEit; ++ptdIt) {
        PAGNode* pointeeNode = pag->getPAGNode(*ptdIt);

        if (llvm::isa<DummyValPN>(pointeeNode) || llvm::isa<DummyObjPN>(pointeeNode) || pag->isBlkObjOrConstantObj(*ptdIt))
            continue;

        if (llvm::PointerType* type = llvm::dyn_cast<llvm::PointerType>(pointeeNode->getValue()->getType())) {
            if (type->getElementType()->isFunctionTy())
                ptsSize++;
        }
        else {
            assert(false && "expecting a pointer type");
        }
    }

    return ptsSize;
}


u32_t CastDDAClient::statPtsTypeIncompatible(PointsTo& pts, uint64_t pointeeSize, llvm::DataLayout* dl) {
    u32_t ptsSize = 0;

    for (PointsTo::iterator ptdIt = pts.begin(), ptdEit = pts.end(); ptdIt != ptdEit; ++ptdIt) {
        PAGNode* pointeeNode = pag->getPAGNode(*ptdIt);
        if (llvm::isa<DummyValPN>(pointeeNode) || llvm::isa<DummyObjPN>(pointeeNode) || pag->isBlkObjOrConstantObj(*ptdIt))
            continue;

        assert(llvm::isa<ObjPN>(pointeeNode) && "expecting an object node");
        if (llvm::PointerType* type = llvm::dyn_cast<llvm::PointerType>(pointeeNode->getValue()->getType())) {
            llvm::Type* elemType = type->getElementType();
            if (elemType->isSized()) {
                uint64_t size = dl->getTypeSizeInBits(elemType);
                if (pointeeSize <= size)
                    ptsSize++;
            }
        }
        else {
            assert(false && "expecting a pointer type");
        }
    }

    return ptsSize;
}


void CastDDAClient::performStat(PointerAnalysis* pta) {
    if (pta->printStat() == false)
        return;

    u32_t numberOfBitCast = 0;
    u32_t numberOfValidPointer = 0;
    u32_t validPointeeSrcNumber = 0;
    u32_t validPointeeDstNumber = 0;
    u32_t totalPtsSize = 0;
    u32_t unsafeSrcCast = 0;
    u32_t unsafeDstCast = 0;

    SVFModule module = pag->getModule();
    llvm::DataLayout* dl = new llvm::DataLayout(module.getMainLLVMModule());
    for (CastInstPtrMap::const_iterator it = instToPtrMap.begin(), eit = instToPtrMap.end(); it != eit; ++it) {
        PointsTo& pointees = pta->getPts(it->second);
        if (pointees.empty())
            continue;

        totalPtsSize += pointees.count();
        numberOfValidPointer++;

        const llvm::BitCastInst* bitcast = it->first;
        validPointeeSrcNumber += checkTypeSize(pointees, bitcast->getSrcTy(), dl);
        validPointeeDstNumber += checkTypeSize(pointees, bitcast->getDestTy(), dl);

        if (validPointeeSrcNumber < totalPtsSize)
            unsafeSrcCast++;

        if (validPointeeDstNumber < totalPtsSize)
            unsafeDstCast++;
    }

    llvm::StringRef fullName(pta->getModule().getModuleIdentifier());
    llvm::StringRef name = fullName.split('/').second;
    std::string moduleName = name.split('.').first.str();

    std::cout << "\n****Bitcast Instruction****\n";
    std::cout << "################ (program : " << moduleName << ")###############\n";
    std::cout.flags(std::ios::left);
    unsigned field_width = 20;
    std::cout << std::setw(field_width) << "BitcastNumber" << numberOfBitCast << "\n";
    std::cout << std::setw(field_width) << "UnsafeSrcCast" << unsafeSrcCast << "\n";
    std::cout << std::setw(field_width) << "UnsafeDstCast" << unsafeDstCast << "\n";
    std::cout << std::setw(field_width) << "ValidPointer" << numberOfValidPointer << "\n";
    std::cout << std::setw(field_width) << "ValidPointeeInSrc" << validPointeeSrcNumber << "\n";
    std::cout << std::setw(field_width) << "ValidPointeeInDst" << validPointeeDstNumber << "\n";
    std::cout << std::setw(field_width) << "TotalPtsSize" << totalPtsSize << "\n";
    std::cout << std::setw(field_width) << "AvgValidSrcSize" << (float)validPointeeSrcNumber / numberOfValidPointer << "\n";
    std::cout << std::setw(field_width) << "AvgValidDstSize" << (float)validPointeeDstNumber / numberOfValidPointer << "\n";
    std::cout << std::setw(field_width) << "AvgPtsSize" << (float)totalPtsSize / numberOfValidPointer << "\n";
    std::cout << "#######################################################" << std::endl;
}


void FreeDDAClient::dumpUseAfterFree() {
    LoadAfterFreePairSet::const_iterator it = detectedUseAfterFree.begin();
    LoadAfterFreePairSet::const_iterator eit = detectedUseAfterFree.end();
    for (; it != eit; ++it) {
        const PtrStorePAGPair& pair = *it;
        llvm::dbgs() << "\nNodeID: " << pair.first << "\tLocation: "
                     << analysisUtil::getSourceLoc(pag->getPAGNode(pair.first)->getValue()) << "\n";
        pag->getPAGNode(pair.first)->getValue()->dump();
        llvm::dbgs() << "\tStore: " << pair.second->getSrcID() << " -> " << pair.second->getDstID()
                     << "\tLocation: " << analysisUtil::getSourceLoc(pair.second->getInst()) << "\n";
    }
}


void FreeDDAClient::performStat(PointerAnalysis* pta) {
    if (pta->printStat() == false)
        return;

    if (DumpFree)
        dumpUseAfterFree();

    llvm::StringRef fullName(pta->getModule().getModuleIdentifier());
    llvm::StringRef name = fullName.split('/').second;
    std::string moduleName = name.split('.').first.str();

    std::cout << "\n****Use After Free****\n";
    std::cout << "################ (program : " << moduleName << ")###############\n";
    std::cout.flags(std::ios::left);
    unsigned field_width = 20;
    std::cout << std::setw(field_width) << "LoadPointers" << getCandidateQueries().count() << "\n";
    std::cout << std::setw(field_width) << "ReachableNullStore" << getReachableFreeStoreNum() << "\n";
    std::cout << std::setw(field_width) << "WarnPointerNum" << getLoadAfterFreePtrNum() << "\n";
    std::cout << "#######################################################" << std::endl;
}


/// Collect all destination ptr of load constraints as query candidates.
NodeBS& UninitDDAClient::collectCandidateQueries(PAG* p) {
    setPAG(p);

    NodeBS loadSrcNodes;            ///< Load source operand values
    const PAGEdge::PAGEdgeSetTy& loadEdges = pag->getEdgeSet(PAGEdge::Load);
    PAGEdge::PAGEdgeSetTy::const_iterator it = loadEdges.begin();
    PAGEdge::PAGEdgeSetTy::const_iterator eit = loadEdges.end();
    for (; it != eit; ++it) {
        PAGEdge* edge = *it;
        if (SingleLoad && loadSrcNodes.test_and_set(edge->getSrcID()) == false)
            continue;

        addCandidate(edge->getDstID());
    }
    return candidateQueries;
}


void UninitDDAClient::getUninitVarNumber(PointerAnalysis* pta, NodeBS& vars, NodeBS& varsFil, NodeBS& objs, NodeBS& objsFil) const {
    const NodeBS& candidates = getCandidateQueries();
    for (NodeBS::iterator it = candidates.begin(), eit = candidates.end(); it != eit; ++it) {
        NodeID ptr = *it;
        const PointsTo& pts = pta->getPts(ptr);
        for (PointsTo::iterator ptsIt = pts.begin(), ptsEit = pts.end(); ptsIt != ptsEit; ++ptsIt) {
            NodeID id = *ptsIt;
            if (pag->isTaintedObj(id)) {
                objs.set(id);
                vars.set(ptr);

                const llvm::Value* value = pagBuilder.getAllocaInstForDummyObj(id);
                NodeID objID = pag->getObjectNode(value);
                if (pta->getStat()->localVarInRecursion.test(objID) || pta->isArrayMemObj(objID) || pta->isFieldInsensitive(objID))
                    continue;

                objsFil.set(objID);
                varsFil.set(ptr);
            }
        }
    }
}


void UninitDDAClient::performStat(PointerAnalysis* pta) {
    if (pta->printStat() == false)
        return;

    NodeBS ptrs, ptrsFil, objs, objsFil;
    getUninitVarNumber(pta, ptrs, ptrsFil, objs, objsFil);

    llvm::StringRef fullName(pta->getModule().getModuleIdentifier());
    llvm::StringRef name = fullName.split('/').second;
    std::string moduleName = name.split('.').first.str();

    std::cout << "\n****Uninitialised Variables****\n";
    std::cout << "################ (program : " << moduleName << ")###############\n";
    std::cout.flags(std::ios::left);
    unsigned field_width = 20;
    std::cout << std::setw(field_width) << "LoadPointers" << getCandidateQueries().count() << "\n";
    std::cout << std::setw(field_width) << "UninitPtrNum" << ptrs.count() << "\n";
    std::cout << std::setw(field_width) << "FilUninitPtrNum" << ptrsFil.count() << "\n";
    std::cout << std::setw(field_width) << "UninitObjNum" << objs.count() << "\n";
    std::cout << std::setw(field_width) << "FilUninitObjNum" << objsFil.count() << "\n";
    std::cout << "#######################################################" << std::endl;

    if (DumpUninitPtr)
        dumpUninitPtrs(ptrsFil, pta);

    if (DumpUninitVar)
        dumpUninitObjs(objsFil, pta);

    if(DumpSUPts)
        printQueryPTS(pta);

    if (DumpSUStore)
        dumpSUStore(pta);
}

void UninitDDAClient::dumpSUPointsTo(const StoreSVFGNode* store, PointerAnalysis* pta) {
    PointsTo& ddaPts = pta->getPts(store->getPAGDstNodeID());
    AndersenWaveDiff* ander = AndersenWaveDiff::createAndersenWaveDiff(pta->getModule());
    const PointsTo& anderPts = ander->getPts(store->getPAGDstNodeID());
    if(ddaPts.count()!=1 || anderPts.count() < 2) {
        return;
    }

    if(const Instruction* inst = store->getPAGEdge()->getInst()) {
        outs() << "============Normal Store dst pts=================\n";
        outs() << *inst << getSourceLoc(inst) << "\n";
        outs() << "\n";
        outs() << "------ander pts-----\n";
        ander->dumpPts(store->getPAGDstNodeID(), anderPts);
        outs() << "------DDA pts --------\n";
        pta->dumpPts(store->getPAGDstNodeID(), ddaPts);
        outs() << "-------------------------\n";
        outs() << "\n";
        outs() << "=================================================\n";
    }
    else {
        outs() << "============Global Store dst pts=================\n";
        pta->dumpPts(store->getPAGDstNodeID(), ddaPts);
        outs() << "=================================================\n";
    }
}
void UninitDDAClient::dumpSUStore(PointerAnalysis* pta) {

    llvm::outs() << "-----Strong Updates Stores-----\n";
    DDAStat* ddaStat = static_cast<DDAStat*>(pta->getStat());

    for (NodeBS::iterator it = ddaStat->getStrongUpdateStores().begin(), eit = ddaStat->getStrongUpdateStores().end(); it != eit; ++it) {
        SVFG* svfg = ddaStat->getSVFG();
        const StoreSVFGNode* store = cast<StoreSVFGNode>(svfg->getSVFGNode(*it));
        if (pagBuilder.isDummyStore(store->getPAGEdge())) {
            outs() << "-------------Dummy Store---------------\n";
            continue;
        }

        dumpSUPointsTo(store,pta);
    }
    outs() << "-------------------------------\n";
}

void UninitDDAClient::dumpUninitObjs(const NodeBS& vars, PointerAnalysis* pta) {
    for (NodeBS::iterator it = vars.begin(), eit = vars.end(); it != eit; ++it) {
        NodeID obj = *it;
        dbgs() << "\nNodeID: " << obj;
        PAGNode* objNode = pag->getPAGNode(obj);
        if (objNode->hasValue()) {
            dbgs() << "  UNINIT_OBJ_  Location: ";
            dbgs() << analysisUtil::getSourceLoc(objNode->getValue()) << "\n";
            objNode->getValue()->print(dbgs());
        }
        else {
            dbgs() << "Dummy Obj Node";
        }
        dbgs() << "\n";
    }
}


void UninitDDAClient::dumpUninitPtrs(const NodeBS& vars, PointerAnalysis* pta) {
    for (NodeBS::iterator it = vars.begin(), eit = vars.end(); it != eit; ++it) {
        NodeID loadPtr = *it;
        dbgs() << "\nNodeID: " << loadPtr;
        PAGNode* loadNode = pag->getPAGNode(loadPtr);
        if (loadNode->hasValue()) {
            dbgs() << " UNINIT_PTR_   Location: ";
            dbgs() << analysisUtil::getSourceLoc(loadNode->getValue()) << "\n";
            loadNode->getValue()->print(dbgs());
        }
        else {
            dbgs() << "Dummy Node";
        }
        dbgs() << "\n";

        Size_t uninit_var_num = 0;
        const PointsTo& pts = pta->getPts(loadPtr);
        for (PointsTo::iterator ptsIt = pts.begin(), ptsEit = pts.end(); ptsIt != ptsEit; ++ptsIt) {
            if (pag->isTaintedObj(*ptsIt)) {
                const Value* value = pagBuilder.getAllocaInstForDummyObj(*ptsIt);
                dbgs() << "        UNINIT_OBJ_" << uninit_var_num++;
                value->print(dbgs());
                dbgs() << "    Location: " << analysisUtil::getSourceLoc(value) << "\n";
            }
        }
        dbgs() << "\n";
    }
}


void UninitDDAClient::DDAUninitPAGBuilder::handleExtCall(CallSite cs, const Function *callee) {

    PAGBuilder::handleExtCall(cs, callee);

    if(TaintUninitHeap==false)
        return;

    const Instruction* inst = cs.getInstruction();
    if (MallocOnly) {
        if (isHeapAllocExtCallViaRet(inst) && getCallee(inst)->getName() == "malloc") {
            addUninitStorePAGEdge(inst);
        }
    }
    else {
        if (isHeapAllocExtCallViaRet(inst)) {
            addUninitStorePAGEdge(inst);
        }
        else if(isExtCall(callee)) {
            ExtAPI::extf_t tF= extCallTy(callee);
            switch(tF) {
            case ExtAPI::EFT_REALLOC: {
                if(!isa<PointerType>(inst->getType()))
                    break;
                // e.g. void *realloc(void *ptr, size_t size)
                // if ptr is null then we will treat it as a malloc
                // if ptr is not null, then we assume a new data memory will be attached to
                // the tail of old allocated memory block.
                if(isa<ConstantPointerNull>(cs.getArgument(0))) {
                    addUninitStorePAGEdge(inst);
                }
                break;
            }
            default:
                break;
            }
        }
    }
}


void UninitDDAClient::DDAUninitPAGBuilder::visitAllocaInst(AllocaInst &AI) {
    /// 1. Handle alloca instruction
    PAGBuilder::visitAllocaInst(AI);

    if(TaintUninitStack == false)
        return;

    addUninitStorePAGEdge(&AI);
}


void UninitDDAClient::DDAUninitPAGBuilder::addUninitStorePAGEdge(const Value* value) {
    NodeID dummyVal = getPAG()->addDummyValNode();
    NodeID dummyObj = getPAG()->addDummyObjNode();
    getPAG()->addAddrEdge(dummyObj, dummyVal);

    NodeID dst = getValueNode(value);
    getPAG()->addStoreEdge(dummyVal, dst);

    objNodeToValueMap.insert(std::make_pair(dummyObj, value));

    PAGEdge* edge = getPAG()->getIntraPAGEdge(dummyVal, dst, PAGEdge::Store);
    dummyStore.insert(dyn_cast<StorePE>(edge));
}

static bool ptsContainTaintedObj(const PointsTo& pts, PAG* pag) {
    for(NodeBS::iterator it = pts.begin(), eit = pts.end(); it!=eit; ++it) {
        if(pag->isTaintedObj(*it))
            return true;
    }
    return false;
}
/*!
 * Print queries' pts
 */
void UninitDDAClient::printQueryPTS(PointerAnalysis* _pta) {

    AndersenWaveDiff* ander = AndersenWaveDiff::createAndersenWaveDiff(_pta->getModule());

    const NodeBS& candidates = getCandidateQueries();
    for (NodeBS::iterator it = candidates.begin(), eit = candidates.end(); it != eit; ++it) {
        const PointsTo& ddaPts = _pta->getPts(*it);
        const PointsTo& anderPts = ander->getPts(*it);
        if(ddaPts.empty() )
            continue;
        if( ptsContainTaintedObj(anderPts,_pta->getPAG()) && !ptsContainTaintedObj(ddaPts,_pta->getPAG())) {
            PAGNode* node = _pta->getPAG()->getPAGNode(*it);
            outs() << "\n=============================\n";
            outs() << "PAGNode:" << *it << " ";
            if(node->hasValue())
                outs() << analysisUtil::getSourceLoc(node->getValue());
            outs() << "\n";
            outs() << "------ander pts-----\n";
            ander->dumpPts(*it, anderPts);
            outs() << "------DDA pts --------\n";
            _pta->dumpPts(*it, ddaPts);
            outs() << "-------------------------\n";
            outs() << "\n";
            for(NodeBS::iterator it = anderPts.begin(), eit = anderPts.end(); it!=eit; ++it) {
                if(pag->isTaintedObj(*it)) {
                    const Value* value = pagBuilder.getAllocaInstForDummyObj(*it);
                    outs() << "    TaintedObject: " << *it <<"   ";
                    outs() << *value << "\n";
                    outs() << "    Location: " << analysisUtil::getSourceLoc(value) << "\n";
                }
            }
            outs() << "-------------------------\n";

            outs() << "=============================\n\n";
        }
    }
}


void UninitDDAClient::collectWPANum(SVFModule mod) {
    FlowSensitive* fspta = new FlowSensitive();
    fspta->runOnModule(mod);

    NodeBS ptrsFS, ptrsFilFS, objsFS, objsFilFS;
    collectCandidateQueries(fspta->getPAG());
    getUninitVarNumber(fspta, ptrsFS, ptrsFilFS, objsFS, objsFilFS);

    llvm::StringRef fullName(fspta->getModule().getModuleIdentifier());
    llvm::StringRef name = fullName.split('/').second;
    std::string moduleName = name.split('.').first.str();

    std::cout << "\n****Uninitialised Variables****\n";
    std::cout << "################ (program : " << moduleName << ")###############\n";
    std::cout.flags(std::ios::left);
    unsigned field_width = 20;
    std::cout << std::setw(field_width) << "LoadPointers" << getCandidateQueries().count() << "\n";
    std::cout << std::setw(field_width) << "UninitPtrNum" << ptrsFS.count() << "\n";
    std::cout << std::setw(field_width) << "FilUninitPtrNum" << ptrsFilFS.count() << "\n";
    std::cout << std::setw(field_width) << "UninitObjNum" << objsFS.count() << "\n";
    std::cout << std::setw(field_width) << "FilUninitObjNum" << objsFilFS.count() << "\n";
    std::cout << "#######################################################" << std::endl;
}
